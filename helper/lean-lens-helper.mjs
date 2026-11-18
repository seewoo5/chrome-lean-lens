#!/usr/bin/env node
// Lean Lens helper: runs real Lean on your machine for the code you are reading on GitHub.
//
// For a repository, a commit and some Lean files, it fetches the commit into its own cache,
// prepares the project (Lean version, Mathlib cache, the files' imports), elaborates each file
// with SubVerso's `subverso-extract-mod` and keeps the result: what Lean knows about every
// token, and the proof state at every tactic. The extension asks for that over localhost.
//
//   node lean-lens-helper.mjs [--port 5326] [--allow owner/repo] [--link owner/repo=/checkout]
//   node lean-lens-helper.mjs run --repo owner/repo --sha <commit> [--pr N] File.lean …
//   node lean-lens-helper.mjs clean [--all]
//   node lean-lens-helper.mjs --codespaces        Lean runs in GitHub Codespaces, not here
//
// Elaborating a Lean file runs the code in it. The helper therefore only works on repositories
// you have allowed, only when asked with its token, and never on its own initiative. On macOS
// that code runs in a sandbox: no network, no access to your files (see `seatbeltProfile`).
//
// Only the results stay on disk. A repository's copy and its build (about 10 GB when it uses
// Mathlib) are removed once they have gone unused for a while, and when the helper stops.

import http from 'node:http';
import { spawn } from 'node:child_process';
import { createHash, randomBytes, timingSafeEqual } from 'node:crypto';
import {
  chmodSync, existsSync, lstatSync, mkdirSync, readFileSync, readdirSync, readlinkSync, realpathSync, renameSync, rmSync, rmdirSync,
  statfsSync, writeFileSync,
} from 'node:fs';
import { rm } from 'node:fs/promises';
import { availableParallelism, homedir } from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';

import { DATA_FORMAT_VERSION, convertModule } from './convert.mjs';

export const HELPER_VERSION = 1;
export const DEFAULT_PORT = 5326;
const DEFAULT_SUBVERSO = 'https://github.com/leanprover/subverso.git';
const DEFAULT_CLONE_BASE = 'https://github.com/';
// SubVerso's JSON is not a stable format, so the revision is pinned. Conversion checks itself
// (see convert.mjs), so a revision with another format gives errors rather than wrong hovers.
const DEFAULT_SUBVERSO_REV = '892d6dc520270b5fb8c1291dd1b131e8c16255ed';
const EXTRACT_TIMEOUT_MS = 20 * 60 * 1000;
const MAX_BODY_BYTES = 1024 * 1024;
// How long a repository's copy and build stay after its last run.
const DEFAULT_TIDY_MINUTES = 30;
// Mathlib's build takes about 10 GB unpacked. Less free space than this and it is not fetched.
const MATHLIB_ROOM_BYTES = 12e9;

// ---------------------------------------------------------------------------------------------
// Checks on what a request names. Everything here ends up in a path or a command's arguments.

// A name may start with a dot (`owner/.github`), but may not be just one: `owner/.` would make
// the copy's folder the owner's folder, which holds the copies of all the owner's repositories.
export const isRepo = (value) => typeof value === 'string' && value.length < 200 &&
  /^[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9_.][A-Za-z0-9_.-]*$/.test(value) && !value.includes('..') && !value.endsWith('/.');
export const isSha = (value) => typeof value === 'string' && /^[0-9a-f]{40}$/.test(value);
export const isLeanPath = (value) => typeof value === 'string' && value.length < 512 && value.endsWith('.lean') &&
  !value.includes('\\') && !value.includes('\0') && value.split('/').every((part) => part && part !== '.' && part !== '..');

export const sha256 = (text) => createHash('sha256').update(text).digest('hex');

const NO_SANDBOX = "This system has no working sandbox for a project's code, so Lean is not run: it would run with your permissions. "
  + 'On Linux, install bubblewrap (bwrap) and check it may run here. Starting the helper with --no-sandbox runs Lean all the same.';

/** Modules a Lean file imports, read from its header only (so `import` in a comment or string is not one). */
export function importsOf(source) {
  const imports = [];
  let depth = 0; // nesting of /- … -/
  for (const raw of source.split('\n')) {
    let line = raw;
    let code = '';
    for (let i = 0; i < line.length; i++) {
      if (line.startsWith('/-', i)) { depth += 1; i += 1; continue; }
      if (depth > 0 && line.startsWith('-/', i)) { depth -= 1; i += 1; continue; }
      if (depth === 0) {
        if (line.startsWith('--', i)) break;
        code += line[i];
      }
    }
    line = code.trim();
    if (!line || line === 'module' || line === 'prelude') continue;
    const match = line.match(/^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)$/);
    if (!match) break; // the header ends at the first command
    imports.push(match[1]);
  }
  return imports;
}

/** The directory of the Lake project a file belongs to (relative to the checkout), or null. */
export function lakeRootFor(checkout, file) {
  const parts = file.split('/').slice(0, -1);
  for (let depth = parts.length; depth >= 0; depth--) {
    const dir = parts.slice(0, depth).join('/');
    if (['lakefile.lean', 'lakefile.toml'].some((name) => existsSync(path.join(checkout, dir, name)))) return dir;
  }
  return null;
}

/** A file's module name, from the source roots Lake sets up (`LEAN_SRC_PATH`), or null. */
export function moduleNameFor(root, srcPath, file) {
  const real = (p) => { try { return realpathSync(p); } catch { return path.resolve(p); } };
  const base = real(root);
  const absolute = path.join(base, file);
  let best = null;
  for (const entry of (srcPath || '').split(path.delimiter).filter(Boolean)) {
    const relative = path.relative(real(path.resolve(base, entry)), absolute);
    if (relative.startsWith('..') || path.isAbsolute(relative)) continue;
    if (best === null || relative.length < best.length) best = relative;
  }
  return best === null ? null : best.replace(/\.lean$/, '').split(path.sep).join('.');
}

/** Whether a Lake project is Mathlib or depends on it (so `lake exe cache get` applies). */
export function usesMathlib(manifestText) {
  try {
    const manifest = JSON.parse(manifestText);
    return manifest.name === 'mathlib' || (manifest.packages || []).some((p) => p.name === 'mathlib');
  } catch {
    return false;
  }
}

// ---------------------------------------------------------------------------------------------
// Files and folders.

/** What is at a path, without following a link there: its `lstat`, or null when nothing is. */
const kind = (target) => { try { return lstatSync(target); } catch { return null; } };
/** Whether a path is a folder itself, not a link to one. */
const isRealDir = (target) => { const stat = kind(target); return Boolean(stat && stat.isDirectory()); };
const entries = (dir) => { try { return readdirSync(dir); } catch { return []; } };
/** Whether there is anything but empty folders at a path. */
const holdsFiles = (target) => !isRealDir(target) || entries(target).some((name) => holdsFiles(path.join(target, name)));
const realOrSame = (target) => { try { return realpathSync(target); } catch { return path.resolve(target); } };
// How a folder is removed with all that is in it (`rmSync(folder, GONE)`; a link is removed
// itself, never what it points to). A program still writing there, such as one that a stopped
// helper left running, makes removal fail with "directory not empty": it is tried again for a
// few seconds.
const GONE = { recursive: true, force: true, maxRetries: 12, retryDelay: 150 };

/**
 * One of the helper's own folders, made if it is missing, by its real path. Anything else at
 * that place, a link above all, is removed first: these are the folders the sandbox opens to a
 * project's code, so they have to be the helper's own and nowhere else.
 */
function ownDir(target) {
  const stat = kind(target);
  if (stat && !stat.isDirectory()) rmSync(target, { force: true });
  mkdirSync(target, { recursive: true });
  return realOrSame(target);
}

/**
 * The Lean version a project pins. The file has to be a plain file that names a version: its
 * content goes to elan, outside the sandbox, and a project could have a link to another file
 * there.
 */
export function toolchainOf(root) {
  const stat = kind(path.join(root, 'lean-toolchain'));
  if (!stat) throw new Error('This project has no lean-toolchain file, so its Lean version is unknown');
  const name = stat.isFile() ? readFileSync(path.join(root, 'lean-toolchain'), 'utf8').trim() : '';
  if (!/^[A-Za-z0-9][A-Za-z0-9._/:-]{0,119}$/.test(name)) throw new Error("This project's lean-toolchain file does not name a Lean version");
  return name;
}

export function formatBytes(bytes) {
  if (bytes >= 1e9) return `${(bytes / 1e9).toFixed(1)} GB`;
  if (bytes >= 1e6) return `${Math.round(bytes / 1e6)} MB`;
  return `${Math.max(1, Math.round(bytes / 1e3))} KB`;
}

/** Free space on the disk a folder is on, in bytes, or null when the system doesn't say. */
function freeBytes(dir) {
  try {
    const disk = statfsSync(dir);
    return Number(disk.bavail) * Number(disk.bsize);
  } catch {
    return null;
  }
}

/** Whether a process with this id is running. */
function alive(pid) {
  if (!Number.isInteger(pid) || pid <= 0) return false;
  try {
    process.kill(pid, 0);
    return true;
  } catch (error) {
    return error.code === 'EPERM'; // it exists, and belongs to someone else
  }
}

// ---------------------------------------------------------------------------------------------
// Running commands.

const tail = (text, n = 600) => (text.length > n ? `…${text.slice(-n)}` : text).trim();

// Commands in flight, so they can be stopped when the helper stops.
const runningCommands = new Set();

/** Stop a command and the programs it started in turn (each command is its own process group). */
function stopCommand(child) {
  try {
    process.kill(-child.pid, 'SIGKILL');
  } catch {
    try { child.kill('SIGKILL'); } catch { /* already gone */ }
  }
}

export function stopCommands() {
  for (const child of runningCommands) stopCommand(child);
}

/**
 * Run a command (never through a shell). Resolves to `{code, stdout, stderr}`. `input`, when
 * given, is what the command reads on its standard input.
 */
function run(command, args, { cwd, env, input, onLine, timeoutMs } = {}) {
  return new Promise((resolve) => {
    const child = spawn(command, args, {
      cwd,
      env: env || { ...process.env, GIT_TERMINAL_PROMPT: '0' },
      stdio: [input === undefined ? 'ignore' : 'pipe', 'pipe', 'pipe'],
      detached: true, // its own process group: see `stopCommand`
    });
    runningCommands.add(child);
    if (input !== undefined) {
      child.stdin.on('error', () => { /* it stopped reading: how it ends says why */ });
      child.stdin.end(input);
    }
    const kept = { stdout: '', stderr: '' };
    const feed = (which) => (chunk) => {
      const text = chunk.toString('utf8');
      kept[which] = (kept[which] + text).slice(-64 * 1024 * 1024);
      if (onLine) for (const line of text.split('\n')) if (line.trim()) onLine(line.trim());
    };
    child.stdout.on('data', feed('stdout'));
    child.stderr.on('data', feed('stderr'));
    const timer = timeoutMs ? setTimeout(() => stopCommand(child), timeoutMs) : null;
    const settle = (result) => {
      if (timer) clearTimeout(timer);
      runningCommands.delete(child);
      resolve(result);
    };
    child.on('error', (error) => settle({ code: -1, stdout: kept.stdout, stderr: error.message }));
    child.on('close', (code, signal) => settle({ code: code === null ? -1 : code, signal, stdout: kept.stdout, stderr: kept.stderr }));
  });
}

async function must(command, args, options) {
  const result = await run(command, args, options);
  if (result.code !== 0) {
    throw new Error(`\`${command} ${args.slice(0, 4).join(' ')}\` failed: ${tail(result.stderr || result.stdout) || `exit ${result.code}`}`);
  }
  return result;
}

/** Copy a directory tree without using more disk where the file system can share blocks. */
async function cloneTree(from, to) {
  const attempts = process.platform === 'darwin'
    ? [['cp', ['-cRp', from, to]], ['cp', ['-Rp', from, to]]]
    : [['cp', ['-a', '--reflink=auto', from, to]]];
  let last = null;
  for (const [command, args] of attempts) {
    last = await run(command, args);
    if (last.code === 0) return;
    rmSync(to, GONE);
  }
  throw new Error(`Could not copy ${from}: ${tail(last.stderr)}`);
}

/**
 * What a folder takes on disk, in bytes, as `du` counts it. Files that share their blocks with
 * others (the copy of a linked checkout's build) are counted in full, so this can be far more
 * than deleting the folder gives back.
 */
async function sizeOf(target) {
  const result = await run('du', ['-sk', target]);
  const kilobytes = Number.parseInt(result.stdout, 10);
  return Number.isFinite(kilobytes) ? kilobytes * 1024 : 0;
}

// ---------------------------------------------------------------------------------------------
// The sandbox. `lake` evaluates a project's lakefile and elaborating a file runs the code in it,
// so both run where they can do little: no network except while fetching dependencies, no
// writing outside the project's copy, and no reading of the user's own files.

function ancestorsOf(target) {
  const out = [];
  for (let dir = path.dirname(target); dir !== path.dirname(dir); dir = path.dirname(dir)) out.push(dir);
  return out;
}

/**
 * A macOS sandbox profile (for `sandbox-exec`). Under it a command can read system files and
 * the `readable` and `writable` paths, but nothing else under the home directories, mounted
 * volumes or the temporary directories; it can write only inside the `writable` folders, except
 * the `guarded` ones in them; and it has no network unless `network` is set. It also cannot
 * send Apple events to other applications.
 */
export function seatbeltProfile({ network = false, readable = [], writable = [], guarded = [], home = homedir() } = {}) {
  const quote = (target) => `"${target.replace(/[\\"]/g, '\\$&')}"`;
  const subpaths = (targets) => targets.map((target) => `(subpath ${quote(target)})`).join(' ');
  const literals = (targets) => targets.map((target) => `(literal ${quote(target)})`).join(' ');
  const visible = [...new Set([...readable, ...writable])];
  const above = [...new Set(visible.flatMap(ancestorsOf))];
  const hidden = [...new Set(['/Users', '/Volumes', '/private/tmp', '/private/var/folders', '/private/var/root', realOrSame(home)])];
  return [
    '(version 1)',
    '(allow default)',
    '(deny appleevent-send)',
    ...(network ? [] : ['(deny network*)']),
    '(deny file-write*)',
    `(allow file-write* (literal "/dev/null") (literal "/dev/zero") (literal "/dev/dtracehelper") (literal "/dev/tty") (regex #"^/dev/fd/") (regex #"^/dev/ttys[0-9]+")${writable.length ? ` ${subpaths(writable)}` : ''})`,
    // A writable folder itself stays what and where it is. Otherwise the code inside could move
    // it away, or put a link to some other place there, and the helper would later take that
    // place for its own: open it to the sandbox, or run `git` in it.
    ...(writable.length ? [`(deny file-write* ${literals(writable)})`] : []),
    ...(guarded.length ? [`(deny file-write* ${subpaths(guarded)})`] : []),
    `(deny file-read* ${subpaths(hidden)})`,
    // (An `allow` with no path would allow everything, so these lines need at least one.)
    ...(visible.length ? [`(allow file-read* ${subpaths(visible)})`] : []),
    ...(above.length ? [`(allow file-read-metadata ${literals(above)})`] : []),
  ].join('\n');
}

/** The system folders a confined command needs on Linux, as `bwrap` arguments. */
function linuxSystem() {
  const args = ['--ro-bind', '/usr', '/usr'];
  // `/bin`, `/lib` and the like are links into `/usr` on most systems, and folders on some.
  for (const dir of ['/bin', '/sbin', '/lib', '/lib32', '/lib64', '/libx32']) {
    const stat = kind(dir);
    if (stat && stat.isSymbolicLink()) args.push('--symlink', readlinkSync(dir), dir);
    else if (stat) args.push('--ro-bind', dir, dir);
  }
  // Of `/etc`, what programs need to find names, certificates and libraries. Not the rest:
  // a machine's settings can hold secrets.
  for (const name of ['resolv.conf', 'hosts', 'nsswitch.conf', 'passwd', 'group', 'ssl', 'ca-certificates', 'ca-certificates.conf', 'pki',
    'ld.so.cache', 'ld.so.conf', 'ld.so.conf.d', 'alternatives', 'localtime']) {
    args.push('--ro-bind-try', `/etc/${name}`, `/etc/${name}`);
  }
  return args;
}

/**
 * The same confinement on Linux, as arguments for `bwrap` (bubblewrap). The command gets a
 * file system of its own, made of the system folders and the `readable` paths, all read-only,
 * and the `writable` ones, with the `guarded` paths in them read-only. Nothing else exists
 * for it: no home folder, no other checkout, no credentials. It sees only its own processes,
 * and has no network unless `network` is set.
 */
export function bwrapArgs({ network = false, readable = [], writable = [], guarded = [], cwd = null, system = linuxSystem() } = {}) {
  return [
    '--unshare-all', ...(network ? ['--share-net'] : []), '--die-with-parent', '--new-session',
    '--proc', '/proc', '--dev', '/dev',
    ...system,
    ...readable.flatMap((target) => ['--ro-bind', target, target]),
    ...writable.flatMap((target) => ['--bind', target, target]),
    ...guarded.flatMap((target) => ['--ro-bind-try', target, target]),
    // What was put there above is all there is. The rest of this file system is empty, and
    // made read-only: it lives in memory, and without this a command could write there at will.
    '--remount-ro', '/',
    ...(cwd ? ['--chdir', cwd] : []),
  ];
}

/** How this machine can confine a command: 'seatbelt' (macOS), 'bwrap' (Linux), or null when it can't. */
async function detectSandbox() {
  if (process.platform === 'linux') {
    const probe = await run('bwrap', [...bwrapArgs(), '--', 'true']);
    return probe.code === 0 ? 'bwrap' : null;
  }
  if (process.platform !== 'darwin' || !existsSync('/usr/bin/sandbox-exec')) return null;
  const probe = await run('/usr/bin/sandbox-exec', ['-p', seatbeltProfile({ readable: ['/usr/bin'] }), '/usr/bin/true']);
  return probe.code === 0 ? 'seatbelt' : null;
}

// ---------------------------------------------------------------------------------------------
// What is kept between runs: settings, results, and for a while a repository's copy.

export function defaultCacheDir() {
  if (process.env.LEAN_LENS_CACHE) return process.env.LEAN_LENS_CACHE;
  if (process.platform === 'darwin') return path.join(homedir(), 'Library', 'Caches', 'lean-lens');
  return path.join(process.env.XDG_CACHE_HOME || path.join(homedir(), '.cache'), 'lean-lens');
}

function loadConfig(cacheDir) {
  const file = path.join(cacheDir, 'config.json');
  let config = {};
  try { config = JSON.parse(readFileSync(file, 'utf8')); } catch { /* first run */ }
  if (typeof config.token !== 'string' || config.token.length < 20) config.token = randomBytes(24).toString('base64url');
  if (!Array.isArray(config.allow)) config.allow = [];
  if (!config.links || typeof config.links !== 'object') config.links = {};
  // Lean versions the helper installed itself, so `clean` can take them away again.
  if (!Array.isArray(config.toolchains)) config.toolchains = [];
  const save = () => {
    mkdirSync(cacheDir, { recursive: true });
    writeFileSync(file, `${JSON.stringify(config, null, 2)}\n`, { mode: 0o600 });
    try { chmodSync(file, 0o600); } catch { /* best effort */ }
  };
  save();
  return { config, save };
}

// What the helper notes about a repository's copy. Kept outside the copy, which the project's
// own code can write to.
const stateDirOf = (cacheDir, repo) => path.join(cacheDir, 'state', sha256(repo).slice(0, 32));

/** The running helper that is using the copy noted in a state folder (its process id), or null. */
function ownerIn(stateDir) {
  try {
    const pid = Number.parseInt(readFileSync(path.join(stateDir, 'owner'), 'utf8'), 10);
    return alive(pid) ? pid : null;
  } catch {
    return null;
  }
}

// The folders in the cache, and what to call them. Everything but the settings and the results.
const CACHE_PARTS = [
  ['repos', 'copies of repositories with their builds'],
  ['extractors', 'SubVerso extractors'],
  ['work', 'scratch files'], ['state', 'scratch files'], ['home', 'scratch files'], ['tmp', 'scratch files'],
];

/**
 * Remove what the helper keeps on disk: the copies of repositories with their builds, the
 * SubVerso extractors, scratch files, and the Lean versions it installed itself. The settings
 * stay, and so do the results of earlier runs unless `results` is set.
 * Resolves to `{removed: [{what, bytes}], bytes, freed, toolchains}`: `bytes` is what `du`
 * counted, `freed` how much free space the disk gained (or null when the system doesn't say).
 */
export async function cleanCache(cacheDir, { results = false, force = false, buildsDir = null } = {}) {
  const dir = path.resolve(cacheDir || defaultCacheDir());
  const dirs = [...new Set([dir, path.resolve(buildsDir || dir)])];
  const { config, save } = loadConfig(dir);
  const users = [...new Set(dirs.flatMap((at) => entries(path.join(at, 'state')).map((name) => ownerIn(path.join(at, 'state', name)))))]
    .filter((pid) => pid !== null && pid !== process.pid);
  if (users.length && !force) {
    throw new Error(`A helper is running and using these files (process ${users.join(', ')}). Stop it first, which removes the builds, or pass --force.`);
  }
  const before = freeBytes(dir);
  const removed = [];
  const parts = dirs.flatMap((at) => CACHE_PARTS.map(([name, what]) => [path.join(at, name), what]));
  for (const [target, what] of [...parts, ...(results ? [[path.join(dir, 'data'), 'results of earlier runs']] : [])]) {
    if (!kind(target)) continue;
    const bytes = holdsFiles(target) ? await sizeOf(target) : 0;
    rmSync(target, GONE);
    if (!bytes) continue; // an empty folder: gone, and not worth a mention
    const same = removed.find((entry) => entry.what === what);
    if (same) same.bytes += bytes; else removed.push({ what, bytes });
  }
  const toolchains = [];
  for (const name of config.toolchains) {
    if ((await run('elan', ['toolchain', 'uninstall', name])).code === 0) toolchains.push(name);
  }
  config.toolchains = [];
  save();
  const after = freeBytes(dir);
  return {
    dir, removed, toolchains,
    bytes: removed.reduce((sum, entry) => sum + entry.bytes, 0),
    freed: before === null || after === null ? null : Math.max(0, after - before),
  };
}

// ---------------------------------------------------------------------------------------------
// The helper itself.

/**
 * @param {object} options `{cacheDir, buildsDir, jobs, subverso, subversoRev, cloneBase, sandbox,
 *   keepBuilds, tidyMinutes, log}`; and `detectSandbox`, which stands in for the check of what
 *   this system can confine a command with (the tests give its answer).
 * @returns `{config, allow, link, start, status, fileState, readData, handle, sandbox, idle, shutdown}`
 */
export function createHelper(options = {}) {
  const cacheDir = path.resolve(options.cacheDir || defaultCacheDir());
  // Where repositories' copies, their builds and scratch files go: the large, short-lived part.
  // In the cache folder unless another place suits it better (a codespace's temporary disk).
  const buildsDir = path.resolve(options.buildsDir || cacheDir);
  const { config, save } = loadConfig(cacheDir);
  const log = options.log || ((message) => console.log(`[${new Date().toTimeString().slice(0, 8)}] ${message}`));
  const poolSize = Math.max(1, Number(options.jobs) || Math.min(4, Math.ceil(availableParallelism() / 2)));
  const subverso = options.subverso || DEFAULT_SUBVERSO;
  const subversoRev = options.subversoRev || DEFAULT_SUBVERSO_REV;
  const cloneBase = (options.cloneBase || DEFAULT_CLONE_BASE).replace(/\/*$/, '/');
  const keepBuilds = Boolean(options.keepBuilds);
  const tidyMinutes = options.tidyMinutes === undefined ? DEFAULT_TIDY_MINUTES : Number(options.tidyMinutes);
  if (!Number.isFinite(tidyMinutes) || tidyMinutes < 0) throw new Error('The time to keep a build is a number of minutes, 0 or more');
  // 'seatbelt' or 'bwrap' when commands can be confined, 'none' when this system can't (then
  // nothing of a project is run), 'off' when asked not to.
  const sandboxWanted = options.sandbox !== false;
  let sandboxState = sandboxWanted ? 'checking' : 'off';
  const sandboxKind = sandboxWanted
    ? Promise.resolve().then(() => (options.detectSandbox || detectSandbox)()).catch(() => null).then((answer) => {
      // Anything but a sandbox `untrusted` knows how to use is no sandbox, and so is a check
      // that failed.
      const found = answer === 'seatbelt' || answer === 'bwrap' ? answer : null;
      sandboxState = found || 'none';
      return found;
    })
    : Promise.resolve(null);

  // Lean in codespaces instead of here (see codespaces.mjs, whose `createCodespaces` is passed in).
  const keepCodespaces = Boolean(options.keepCodespaces);
  const remote = options.codespaces
    ? options.codespaces({
      config, save, run, log, gh: options.gh, sandbox: sandboxWanted, keep: keepCodespaces, recordsDir: path.join(cacheDir, 'codespaces'),
      remotePort: options.remotePort, cloneBase: options.cloneBase, pollMs: options.pollMs, keepAliveMs: options.keepAliveMs, retryMs: options.retryMs,
      machine: options.machine,
    })
    : null;

  // Repositories that run on this machine even so (`--here`): ones a codespace cannot serve.
  const here = new Set(options.here || []);
  const away = (repo) => Boolean(remote) && !here.has(repo);

  const repoQueues = new Map(); // repo → promise of its last job (one checkout per repository)
  const latestJob = new Map(); // repo@sha → the job last started for that commit
  const fileStates = new Map(); // repo@sha:path → {state: 'queued' | 'running' | 'error', error}
  const extractorBuilds = new Map(); // directory → promise of the extractor binary

  const repoDir = (repo) => path.join(buildsDir, 'repos', ...repo.split('/'));
  // Scratch folders, one per run, named after this process so that a later helper can tell
  // which ones were left behind.
  const workRoot = path.join(buildsDir, 'work');
  const scratchDir = (label) => ownDir(path.join(workRoot, `${process.pid}-${label}`));
  // Results are kept by data format, so a newer helper never serves an older format.
  const dataFile = (repo, sha, file) => path.join(cacheDir, 'data', `v${DATA_FORMAT_VERSION}`, ...repo.split('/'), sha, `${file}.json`);
  const fileKey = (repo, sha, file) => `${repo}@${sha}:${file}`;

  function allow(repo) {
    if (!isRepo(repo)) throw new Error(`Not a repository name: ${repo}`);
    if (!config.allow.includes(repo)) { config.allow.push(repo); save(); log(`Allowed ${repo}`); }
  }

  /** Use an existing checkout as the starting point for a repository (its commits and its build). */
  function link(repo, checkout) {
    if (!isRepo(repo)) throw new Error(`Not a repository name: ${repo}`);
    const resolved = path.resolve(checkout);
    if (!existsSync(path.join(resolved, '.git'))) throw new Error(`${resolved} is not a git checkout`);
    config.links[repo] = resolved;
    save();
  }

  // --- Keeping little on disk ----------------------------------------------------------------
  // A repository's copy holds its build: about 10 GB when it uses Mathlib. It is only needed to
  // run Lean again, so it goes once it has not been used for a while, and when the helper
  // stops. What stays is the results, some hundred kilobytes for each Lean file.

  const active = new Map(); // repo → runs queued or under way
  const tidyTimers = new Map(); // repo → the timer that will remove its copy
  const owned = new Set(); // repositories whose copy this helper is using

  /** Note that this helper is the one using a repository's copy. */
  function claim(repo) {
    mkdirSync(stateDirOf(buildsDir, repo), { recursive: true });
    writeFileSync(path.join(stateDirOf(buildsDir, repo), 'owner'), `${process.pid}\n`);
    owned.add(repo);
  }

  /** Remove a repository's copy with its build, and what was noted about it. */
  function forgetCopy(repo, why) {
    const dir = repoDir(repo);
    if (why && kind(dir)) log(`Removing the copy of ${repo} and its build (${why}). The results stay.`);
    rmSync(dir, GONE);
    try { rmdirSync(path.dirname(dir)); } catch { /* other repositories of that owner are there */ }
    rmSync(stateDirOf(buildsDir, repo), GONE);
    owned.delete(repo);
  }

  /** The same without holding up requests: the copy is moved aside at once, then deleted. */
  async function discardCopy(repo, why) {
    const dir = repoDir(repo);
    let aside = null;
    if (kind(dir)) {
      log(`Removing the copy of ${repo} and its build (${why}). The results stay.`);
      aside = path.join(scratchDir('gone'), randomBytes(6).toString('hex'));
      try { renameSync(dir, aside); } catch { aside = null; }
    }
    forgetCopy(repo);
    if (aside) await rm(aside, GONE);
  }

  /** Once nothing is queued for a repository: remove its copy when it stays unused. */
  function tidyWhenIdle(repo) {
    clearTimeout(tidyTimers.get(repo));
    tidyTimers.delete(repo);
    if (away(repo) ? keepCodespaces : keepBuilds) return;
    const why = tidyMinutes ? `not used for ${tidyMinutes} minute${tidyMinutes === 1 ? '' : 's'}` : 'its run is over';
    const discard = () => {
      tidyTimers.delete(repo);
      // Queued like a run, so a run started meanwhile waits for it and then makes a fresh copy.
      // With Lean in a codespace there is no copy here: the codespace is what is stopped.
      const previous = repoQueues.get(repo) || Promise.resolve();
      repoQueues.set(repo, previous
        .then(() => (active.get(repo) ? null : (away(repo) ? remote.rest(repo, why) : discardCopy(repo, why))))
        .catch((error) => log(`${away(repo) ? 'The codespace' : 'The copy'} of ${repo} could not be ${away(repo) ? 'stopped' : 'removed'}: ${error.message}`)));
    };
    if (tidyMinutes === 0) { discard(); return; }
    const timer = setTimeout(discard, tidyMinutes * 60 * 1000);
    timer.unref();
    tidyTimers.set(repo, timer);
  }

  /** At start: remove what earlier helpers left and no running helper is using. */
  function sweep() {
    // What cannot be removed now (a program still at work there) is left for the next start: it
    // must not keep this helper from starting.
    const attempt = (what, act) => {
      try { act(); } catch (error) { log(`${what} could not be removed now (${error.code || error.message}); the next start tries again`); }
    };
    for (const name of entries(workRoot)) {
      if (!alive(Number.parseInt(name, 10))) attempt('A scratch folder', () => rmSync(path.join(workRoot, name), GONE));
    }
    // Scratch folders of earlier versions, which kept them between runs.
    for (const name of ['home', 'tmp']) attempt('A scratch folder', () => rmSync(path.join(cacheDir, name), GONE));
    if (keepBuilds) return;
    const repos = path.join(buildsDir, 'repos');
    for (const owner of entries(repos)) {
      for (const name of entries(path.join(repos, owner))) {
        const repo = `${owner}/${name}`;
        if (isRepo(repo) && ownerIn(stateDirOf(buildsDir, repo)) === null) attempt(`The copy of ${repo}`, () => forgetCopy(repo, 'no running helper is using it'));
      }
      try { rmdirSync(path.join(repos, owner)); } catch { /* still in use */ }
    }
  }

  /** Stop what is running, and remove what only a running helper needs. */
  function shutdown() {
    for (const timer of tidyTimers.values()) clearTimeout(timer);
    tidyTimers.clear();
    stopCommands();
    if (remote) remote.shutdown();
    // (Whatever cannot be removed now, the next helper removes when it starts.)
    if (!keepBuilds) for (const repo of [...owned]) { try { forgetCopy(repo, 'the helper is stopping'); } catch { /* next start */ } }
    for (const name of entries(workRoot)) {
      if (name.startsWith(`${process.pid}-`)) { try { rmSync(path.join(workRoot, name), GONE); } catch { /* next start */ } }
    }
  }

  /** Resolves once nothing is queued or running. */
  async function idle() {
    for (;;) {
      const pending = [...repoQueues.values()];
      await Promise.all(pending);
      const now = [...repoQueues.values()];
      if (now.length === pending.length && now.every((promise, i) => promise === pending[i])) return;
    }
  }

  // --- Preparing a checkout ------------------------------------------------------------------

  const depsStamp = (root) => sha256(['lean-toolchain', 'lake-manifest.json', 'lakefile.lean', 'lakefile.toml']
    .map((name) => { try { return readFileSync(path.join(root, name), 'utf8'); } catch { return ''; } }).join('\0'));
  // Which dependencies a project's copy was last prepared for.
  const stampFile = (repo, rootDir) => path.join(stateDirOf(buildsDir, repo), `${sha256(rootDir === '.' ? '' : rootDir).slice(0, 32)}.deps`);
  const writeStamp = (repo, rootDir, stamp) => {
    mkdirSync(stateDirOf(buildsDir, repo), { recursive: true });
    writeFileSync(stampFile(repo, rootDir), stamp);
  };

  async function ensureRepo(job, workDir) {
    const dir = repoDir(job.repo);
    if (isRealDir(dir) && isRealDir(path.join(dir, '.git'))) { claim(job.repo); return dir; }
    // Nothing usable is there (or something else is, where the copy should be): start again.
    forgetCopy(job.repo);
    claim(job.repo);
    // Built in a staging directory, so an interrupted first run is not taken for a finished one.
    const staging = path.join(workDir, 'clone');
    mkdirSync(path.dirname(dir), { recursive: true });
    const linked = config.links[job.repo];
    const remote = `${cloneBase}${job.repo}.git`;
    if (linked && existsSync(path.join(linked, '.git'))) {
      job.say(`Copying ${linked}`);
      await must('git', ['clone', '--quiet', '--no-checkout', linked, staging]);
      const origin = await run('git', ['-C', linked, 'remote', 'get-url', 'origin']);
      await must('git', ['-C', staging, 'remote', 'rename', 'origin', 'local']);
      await must('git', ['-C', staging, 'remote', 'add', 'origin', origin.code === 0 && origin.stdout.trim() ? origin.stdout.trim() : remote]);
      // The build too, so Lake only rebuilds what differs at the commit being read. (Not where
      // that build may be half made: a codespace whose own setup is still fetching it.)
      const lakefiles = options.linkedBuilds === false ? { stdout: '' } : await run('git', ['-C', linked, 'ls-files', '--', 'lakefile.lean', 'lakefile.toml', '*/lakefile.lean', '*/lakefile.toml']);
      for (const lakefile of lakefiles.stdout.split('\n').filter(Boolean)) {
        const root = path.dirname(lakefile);
        const built = path.join(linked, root, '.lake');
        if (!existsSync(built)) continue;
        job.say(`Copying the build in ${root === '.' ? 'the project' : root} (shares disk space where it can)`);
        mkdirSync(path.join(staging, root), { recursive: true });
        await cloneTree(built, path.join(staging, root, '.lake'));
        writeStamp(job.repo, root, depsStamp(path.join(linked, root)));
      }
    } else {
      job.say(`Cloning ${remote}`);
      await must('git', ['clone', '--quiet', '--filter=blob:none', '--no-checkout', remote, staging]);
    }
    renameSync(staging, dir);
    return dir;
  }

  async function checkout(dir, job) {
    // (No hooks, whatever the copy's `.git` says: this runs outside the sandbox.)
    const git = ['-C', dir, '-c', 'core.hooksPath=/dev/null', '-c', 'core.fsmonitor=false'];
    const has = async () => (await run('git', [...git, 'cat-file', '-e', `${job.sha}^{commit}`])).code === 0;
    if (!(await has())) {
      job.say(`Fetching ${job.sha.slice(0, 10)}`);
      const remotes = (await run('git', [...git, 'remote'])).stdout.split('\n').filter(Boolean);
      if (remotes.includes('local')) await run('git', [...git, 'fetch', '--quiet', 'local']);
      if (!(await has())) await run('git', [...git, 'fetch', '--quiet', 'origin', job.sha]);
      if (!(await has()) && job.pr) await run('git', [...git, 'fetch', '--quiet', 'origin', `pull/${job.pr}/head`]);
      if (!(await has())) throw new Error(`Commit ${job.sha.slice(0, 10)} was not found in ${job.repo}`);
    }
    await must('git', [...git, 'checkout', '--quiet', '--force', '--detach', job.sha]);
  }

  // --- Running a project's code --------------------------------------------------------------

  // The real `git`, for Lake's own cloning of dependencies: on macOS `/usr/bin/git` is a stub
  // that looks its tool up through files the sandbox hides.
  let gitDirectory = null;
  const gitDir = async () => {
    if (gitDirectory === null) {
      const found = process.platform === 'darwin' ? await run('/usr/bin/xcrun', ['-f', 'git']) : { code: 1 };
      gitDirectory = found.code === 0 && found.stdout.trim() ? path.dirname(found.stdout.trim()) : '';
    }
    return gitDirectory;
  };

  /**
   * Run a command that executes a project's code: `lake` (which evaluates the lakefile) or the
   * extractor (which elaborates a file). Its environment has none of the helper's own
   * variables, and its home and temporary directories are empty ones in `scratch`, a folder of
   * the run that goes when the run is over. Where the system has a sandbox, it can also read
   * only the Lean toolchain and the paths given, write only where told, and reach the network
   * only when `network` is set.
   */
  async function untrusted(command, args, { cwd, toolchain, scratch, network = false, readable = [], writable = [], env: extra = {}, onLine, timeoutMs } = {}) {
    if (!sandboxWanted) {
      return run(command, args, { cwd, env: { ...process.env, GIT_TERMINAL_PROMPT: '0', ...extra }, onLine, timeoutMs });
    }
    const home = ownDir(path.join(scratch, 'home'));
    const temporary = ownDir(path.join(scratch, 'tmp'));
    const env = {
      PATH: [toolchain && toolchain.bin, await gitDir(), '/usr/bin', '/bin', '/usr/sbin', '/sbin', '/opt/homebrew/bin', '/usr/local/bin'].filter(Boolean).join(path.delimiter),
      HOME: home,
      TMPDIR: temporary,
      LANG: process.env.LANG || 'en_US.UTF-8',
      GIT_TERMINAL_PROMPT: '0',
      ...extra,
    };
    // No sandbox on this system (on Linux, bubblewrap missing or not allowed to run): the code
    // would run with the reader's own permissions, so it does not run, unless they asked for
    // that (`--no-sandbox`, above).
    const confinement = await sandboxKind;
    if (!confinement) throw new Error(NO_SANDBOX);
    const allowed = [home, temporary, ...writable].map(realOrSame);
    const limits = {
      network,
      readable: [...(toolchain ? [toolchain.root] : []), ...readable].map(realOrSame),
      writable: allowed,
      // A checkout's own `.git` stays as it is: the helper runs `git` there later, outside the
      // sandbox, and a hook or setting planted now would run then.
      guarded: allowed.map((target) => path.join(target, '.git')),
    };
    if (confinement === 'bwrap') {
      return run('bwrap', [...bwrapArgs({ ...limits, cwd: cwd ? realOrSame(cwd) : null }), '--', command, ...args], { cwd, env, onLine, timeoutMs });
    }
    return run('/usr/bin/sandbox-exec', ['-p', seatbeltProfile(limits), command, ...args], { cwd, env, onLine, timeoutMs });
  }

  /**
   * Where the project's Lean lives: `{ lake, bin, root }`, the real programs rather than elan's
   * stand-ins, so they can be run directly. elan only reads the project's `lean-toolchain` here
   * (and downloads that version if it is missing); nothing of the project is run.
   */
  async function resolveToolchain(root, job) {
    const name = toolchainOf(root);
    // elan installs a missing version by itself, without a word, the moment it is asked about
    // it. So the helper looks first, says what is happening, and notes what it brought in.
    const versions = async () => {
      const listed = await run('elan', ['toolchain', 'list']);
      return listed.code === 0 ? listed.stdout.split('\n').map((line) => line.trim().split(/\s+/)[0]).filter(Boolean) : null;
    };
    const before = await versions();
    if (before && !before.includes(name)) {
      job.say(`Installing ${name} (about 3 GB)`);
      await must('elan', ['toolchain', 'install', name], { onLine: (line) => job.progress(line) });
      for (const added of (await versions() || []).filter((version) => !before.includes(version))) {
        if (!config.toolchains.includes(added)) { config.toolchains.push(added); save(); }
      }
    }
    let found = await run('elan', ['which', 'lake'], { cwd: root });
    // Without elan, whichever `lake` is installed.
    if (found.code !== 0) found = await must('/usr/bin/which', ['lake']);
    const lake = realOrSame(found.stdout.trim().split('\n').pop());
    return { lake, bin: path.dirname(lake), root: path.dirname(path.dirname(lake)) };
  }

  /** Whether Mathlib's prebuilt files are there (in a project that uses Mathlib, or is it). */
  const mathlibIsBuilt = (root) => [root, path.join(root, '.lake', 'packages', 'mathlib')].some((dir) =>
    ['lib/lean', 'lib'].some((lib) => existsSync(path.join(dir, '.lake', 'build', lib, 'Mathlib', 'Init.olean'))));

  async function ensureDependencies(root, rootDir, toolchain, job, workDir) {
    const stamp = depsStamp(root);
    try { if (readFileSync(stampFile(job.repo, rootDir), 'utf8') === stamp) return; } catch { /* not prepared yet */ }
    let manifest = '';
    try { manifest = readFileSync(path.join(root, 'lake-manifest.json'), 'utf8'); } catch { /* no dependencies */ }
    const mathlib = usesMathlib(manifest);
    const free = freeBytes(root);
    if (mathlib && free !== null && free < MATHLIB_ROOM_BYTES) {
      throw new Error(`Mathlib's build takes about 10 GB of disk space while it is in use, and ${formatBytes(free)} is free`);
    }
    // The one step with network access: Lake clones the packages the manifest lists, and for a
    // Mathlib project its `cache` tool downloads the prebuilt files. Those downloads go to a
    // folder of this run, not to the user's own Mathlib cache: other projects read that one, so
    // this project's code must not be able to write there. They are only needed for unpacking.
    const downloads = mathlib ? ownDir(path.join(workDir, 'mathlib')) : null;
    job.say(mathlib ? "Downloading Mathlib's build (about 10 GB on disk)" : "Fetching the project's dependencies");
    let result;
    try {
      result = await untrusted(toolchain.lake, mathlib ? ['exe', 'cache', 'get'] : ['env', 'true'], {
        cwd: root, toolchain, scratch: path.join(workDir, 'project'), network: true,
        writable: [job.dir, ...(downloads ? [downloads] : [])],
        env: downloads ? { MATHLIB_CACHE_DIR: downloads } : {},
        onLine: (line) => job.progress(line),
      });
    } finally {
      if (downloads) rmSync(downloads, GONE);
    }
    if (result.code !== 0) {
      const why = tail(result.stderr || result.stdout, 300) || `exit ${result.code}`;
      // Without Mathlib's prebuilt files, building the imports would compile Mathlib: hours.
      if (!mathlib) throw new Error(`The project's dependencies could not be fetched: ${why}`);
      if (!mathlibIsBuilt(root)) throw new Error(`Mathlib's build could not be downloaded: ${why}`);
      job.note(`\`lake exe cache get\` did not get everything: ${why}`);
      return; // and it is tried again on the next run
    }
    writeStamp(job.repo, rootDir, stamp);
  }

  async function buildImports(root, files, toolchain, job, scratch) {
    const imports = new Set();
    for (const file of files) {
      try { importsOf(readFileSync(path.join(root, file), 'utf8')).forEach((name) => imports.add(name)); } catch { /* reported when extracting */ }
    }
    if (!imports.size) return;
    job.say(`Building what ${files.length === 1 ? 'the file imports' : `${files.length} files import`}`);
    const result = await untrusted(toolchain.lake, ['build', ...[...imports].map((name) => `+${name}`)], {
      cwd: root, toolchain, scratch, writable: [job.dir], onLine: (line) => job.progress(line),
    });
    if (result.code !== 0) job.note(`\`lake build\` of the imports failed: ${tail(result.stderr || result.stdout, 400)}`);
  }

  /** The SubVerso extractor for a Lean version, built once and kept. */
  function ensureExtractor(root, toolchain, job, workDir) {
    const name = toolchainOf(root);
    const dir = path.join(cacheDir, 'extractors', `${name.replace(/[^A-Za-z0-9._-]+/g, '_')}-${subversoRev.slice(0, 12)}`);
    const binary = path.join(dir, '.lake', 'build', 'bin', 'subverso-extract-mod');
    if (existsSync(binary)) return Promise.resolve({ binary, dir });
    if (!extractorBuilds.has(dir)) {
      extractorBuilds.set(dir, (async () => {
        job.say(`Building the SubVerso extractor for ${name} (once per Lean version)`);
        rmSync(dir, GONE);
        mkdirSync(path.dirname(dir), { recursive: true });
        await must('git', ['clone', '--quiet', '--no-checkout', subverso, dir]);
        await must('git', ['-C', dir, 'checkout', '--quiet', subversoRev]);
        writeFileSync(path.join(dir, 'lean-toolchain'), `${name}\n`);
        // (Scratch folders of its own: nothing the project's code left behind is in reach.)
        const built = await untrusted(toolchain.lake, ['build', 'subverso-extract-mod'], {
          cwd: dir, toolchain, scratch: path.join(workDir, 'extractor'), writable: [dir], onLine: (line) => job.progress(line),
        });
        if (built.code !== 0 || !existsSync(binary)) {
          throw new Error(`SubVerso's extractor did not build for ${name}: ${tail(built.stderr || built.stdout, 300) || 'no output'}`);
        }
        return { binary, dir };
      })().finally(() => extractorBuilds.delete(dir)));
    }
    return extractorBuilds.get(dir);
  }

  /** The source roots Lake sets up for the project (`LEAN_SRC_PATH`), for naming modules. */
  async function sourceRoots(root, toolchain, job, scratch) {
    const result = await untrusted(toolchain.lake, ['env', 'printenv', 'LEAN_SRC_PATH'], { cwd: root, toolchain, scratch, writable: [job.dir] });
    return result.code === 0 ? result.stdout.trim().split('\n').pop() : '';
  }

  async function extract(root, file, context, job) {
    const key = fileKey(job.repo, job.sha, file.repoPath);
    fileStates.set(key, { state: 'running' });
    const output = path.join(context.out, `${sha256(file.repoPath)}.json`);
    try {
      const source = readFileSync(path.join(root, file.path), 'utf8');
      // The extractor runs under `lake env`, which gives it the project's modules.
      let args = ['env', context.extractor.binary];
      let cwd = root;
      let moduleName = moduleNameFor(root, context.srcPath, file.path);
      if (!moduleName) {
        // A file outside the project's libraries (a script, a test): elaborated on its own, from
        // its directory, against the project's built modules.
        moduleName = path.basename(file.path, '.lean');
        if (!/^[A-Za-z_][A-Za-z0-9_']*$/.test(moduleName)) throw new Error('This file is not part of a library of its Lake project');
        cwd = path.dirname(path.join(root, file.path));
        args = ['-d', root, 'env', 'env', '-u', 'LEAN_SRC_PATH', context.extractor.binary];
      }
      const result = await untrusted(context.toolchain.lake, [...args, moduleName, output], {
        cwd, toolchain: context.toolchain, scratch: context.scratch, readable: [context.extractor.dir], writable: [job.dir, context.out], timeoutMs: EXTRACT_TIMEOUT_MS,
      });
      if (result.code !== 0) throw new Error(`Lean could not process the file: ${tail(result.stderr || result.stdout, 400) || `exit ${result.code}`}`);
      // (The project's code can write in that folder: only a plain file is read.)
      const written = kind(output);
      if (!written || !written.isFile()) throw new Error('Lean wrote no output for the file');
      const data = convertModule(JSON.parse(readFileSync(output, 'utf8')), source);
      const target = dataFile(job.repo, job.sha, file.repoPath);
      mkdirSync(path.dirname(target), { recursive: true });
      writeFileSync(target, JSON.stringify({ ...data, hash: sha256(source), lean: context.name }));
      fileStates.delete(key);
    } catch (error) {
      fileStates.set(key, { state: 'error', error: error.message });
      log(`  ${file.repoPath}: ${error.message}`);
    } finally {
      rmSync(output, { force: true });
      job.done += 1;
    }
  }

  async function runJob(job) {
    job.phase = 'preparing'; // no longer waiting behind another run
    if (away(job.repo)) {
      // Lean runs in the repository's codespace; what comes back is kept here like any result.
      await remote.runJob(job, {
        store(file, data) {
          const target = dataFile(job.repo, job.sha, file);
          mkdirSync(path.dirname(target), { recursive: true });
          writeFileSync(target, JSON.stringify(data));
          fileStates.delete(fileKey(job.repo, job.sha, file));
        },
        fail(file, error) { fileStates.set(fileKey(job.repo, job.sha, file), { state: 'error', error }); },
      });
      return;
    }
    const workDir = scratchDir(randomBytes(6).toString('hex'));
    try {
      const dir = await ensureRepo(job, workDir);
      job.dir = realOrSame(dir);
      await checkout(dir, job);
      // Files grouped by the Lake project they belong to (usually one, at the repository root).
      const groups = new Map();
      for (const repoPath of job.paths) {
        const rootDir = existsSync(path.join(dir, repoPath)) ? lakeRootFor(dir, repoPath) : null;
        if (rootDir === null) {
          fileStates.set(fileKey(job.repo, job.sha, repoPath), {
            state: 'error',
            error: existsSync(path.join(dir, repoPath)) ? 'This file is not inside a Lake project' : 'This file does not exist at that commit',
          });
          job.done += 1;
          continue;
        }
        if (!groups.has(rootDir)) groups.set(rootDir, []);
        groups.get(rootDir).push({ repoPath, path: rootDir ? repoPath.slice(rootDir.length + 1) : repoPath });
      }
      const scratch = path.join(workDir, 'project');
      const out = ownDir(path.join(workDir, 'out'));
      for (const [rootDir, files] of groups) {
        const root = path.join(job.dir, rootDir);
        job.phase = 'preparing';
        // Refused before anything is installed for it (a Lean version is some 3 GB), not at the
        // first command that would run the project's code.
        if (sandboxWanted && !(await sandboxKind)) throw new Error(NO_SANDBOX);
        const toolchain = await resolveToolchain(root, job);
        await ensureDependencies(root, rootDir, toolchain, job, workDir);
        await buildImports(root, files.map((file) => file.path), toolchain, job, scratch);
        const extractor = await ensureExtractor(root, toolchain, job, workDir);
        const context = { extractor, toolchain, scratch, out, name: toolchainOf(root), srcPath: await sourceRoots(root, toolchain, job, scratch) };
        job.phase = 'elaborating';
        job.say(`Elaborating ${files.length} file${files.length === 1 ? '' : 's'}`);
        let next = 0;
        const worker = async () => { while (next < files.length) await extract(root, files[next++], context, job); };
        await Promise.all(Array.from({ length: Math.min(poolSize, files.length) }, worker));
      }
    } finally {
      rmSync(workDir, GONE);
    }
  }

  // --- What the extension asks for -----------------------------------------------------------

  /** Start elaborating files of a commit (those not done already). Returns the commit's status. */
  function start({ repo, sha, pr, paths }) {
    const todo = paths.filter((file) => {
      const state = fileStates.get(fileKey(repo, sha, file));
      return !existsSync(dataFile(repo, sha, file)) && !(state && (state.state === 'queued' || state.state === 'running'));
    });
    if (todo.length) {
      const job = {
        repo, sha, pr, paths: todo, phase: 'queued', message: 'Waiting for the previous run', notes: [], done: 0, error: null, finished: false,
        say(message) { this.message = message; log(`${repo}@${sha.slice(0, 7)}: ${message}`); },
        progress(line) { this.detail = line.slice(0, 200); },
        note(message) { this.notes.push(message); log(`${repo}@${sha.slice(0, 7)}: ${message}`); },
      };
      todo.forEach((file) => fileStates.set(fileKey(repo, sha, file), { state: 'queued' }));
      latestJob.set(`${repo}@${sha}`, job);
      active.set(repo, (active.get(repo) || 0) + 1);
      clearTimeout(tidyTimers.get(repo));
      tidyTimers.delete(repo);
      const previous = repoQueues.get(repo) || Promise.resolve();
      const current = previous.then(() => runJob(job)).then(
        () => { job.phase = 'done'; job.say(`Done (${todo.length} file${todo.length === 1 ? '' : 's'})`); },
        (error) => {
          job.phase = 'error';
          job.error = error.message;
          log(`${repo}@${sha.slice(0, 7)}: ${error.message}`);
          for (const file of todo) {
            const key = fileKey(repo, sha, file);
            const state = fileStates.get(key);
            if (state && state.state !== 'error') fileStates.set(key, { state: 'error', error: error.message });
          }
        },
      ).finally(() => {
        job.finished = true;
        active.set(repo, active.get(repo) - 1);
        if (!active.get(repo)) tidyWhenIdle(repo);
      });
      repoQueues.set(repo, current);
      job.promise = current;
    }
    return status(repo, sha);
  }

  function status(repo, sha) {
    const job = latestJob.get(`${repo}@${sha}`);
    if (!job) return { state: 'idle' };
    return {
      state: job.finished ? (job.error ? 'error' : 'done') : 'pending',
      phase: job.phase, message: job.message, detail: job.detail, done: job.done, total: job.paths.length,
      error: job.error || undefined, notes: job.notes.length ? job.notes : undefined,
    };
  }

  function fileState(repo, sha, file) {
    if (existsSync(dataFile(repo, sha, file))) return { state: 'ready' };
    const state = fileStates.get(fileKey(repo, sha, file));
    if (!state) return { state: 'missing' };
    if (state.state === 'error') return { state: 'error', error: state.error };
    return { ...status(repo, sha), state: 'pending' };
  }

  const readData = (repo, sha, file) => readFileSync(dataFile(repo, sha, file), 'utf8');

  /** Answer one request: `{status, body}` with `body` a JSON string. */
  function handle(method, url, body) {
    const json = (status, value) => ({ status, body: typeof value === 'string' ? value : JSON.stringify(value) });
    const { pathname, searchParams } = new URL(url, 'http://127.0.0.1');
    const request = body || {};
    if (method === 'GET' && pathname === '/status') {
      return json(200, {
        ok: true, name: 'lean-lens-helper', version: HELPER_VERSION, format: DATA_FORMAT_VERSION, allow: config.allow, sandbox: sandboxState,
        runs: remote ? 'codespaces' : 'here',
      });
    }
    if (method === 'POST' && pathname === '/allow') {
      if (!isRepo(request.repo)) return json(400, { error: 'Bad repository name' });
      allow(request.repo);
      return json(200, { ok: true, allow: config.allow });
    }
    const repo = method === 'GET' ? searchParams.get('repo') : request.repo;
    const sha = method === 'GET' ? searchParams.get('sha') : request.sha;
    if (!isRepo(repo) || !isSha(sha)) return json(400, { error: 'Bad repository or commit' });
    if (!config.allow.includes(repo)) return json(403, { state: 'not_allowed', repo });
    if (method === 'GET' && pathname === '/job') return json(200, status(repo, sha));
    if (method === 'POST' && pathname === '/run') {
      const paths = Array.isArray(request.paths) ? [...new Set(request.paths)] : [];
      if (!paths.length || paths.length > 500 || !paths.every(isLeanPath)) return json(400, { error: 'Bad file list' });
      const pr = Number.isInteger(Number(request.pr)) && Number(request.pr) > 0 ? Number(request.pr) : null;
      return json(200, start({ repo, sha, pr, paths }));
    }
    if (method === 'POST' && pathname === '/file') {
      if (!isLeanPath(request.path)) return json(400, { error: 'Bad file path' });
      const state = fileState(repo, sha, request.path);
      if (state.state !== 'ready') return json(200, state);
      return json(200, `{"state":"ready","data":${readData(repo, sha, request.path)}}`);
    }
    return json(404, { error: 'Unknown request' });
  }

  /** How a project's code is confined: 'seatbelt' or 'bwrap', 'none' (this system can't) or 'off'. */
  const sandbox = () => sandboxKind.then(() => sandboxState);

  sweep();
  // (`untrusted` is here for the tests: they check that it runs nothing without a sandbox.)
  return { cacheDir, buildsDir, config, allow, link, start, status, fileState, readData, handle, poolSize, sandbox, keepBuilds, keepCodespaces, tidyMinutes, remote, idle, shutdown, untrusted };
}

// ---------------------------------------------------------------------------------------------
// The local web server.

/** Whether a request may be answered: from this machine's extension, with the helper's token. */
export function authorized(headers, port, token) {
  const host = headers.host || '';
  if (host !== `127.0.0.1:${port}` && host !== `localhost:${port}`) return false; // DNS rebinding
  const origin = headers.origin;
  if (origin && !/^(?:chrome|moz)-extension:\/\//.test(origin)) return false; // a web page
  const given = Buffer.from(String(headers['x-lean-lens-token'] || ''));
  const expected = Buffer.from(token);
  return given.length === expected.length && timingSafeEqual(given, expected);
}

export function serve(helper, port = DEFAULT_PORT) {
  const server = http.createServer((request, response) => {
    const origin = request.headers.origin;
    const fromExtension = origin && /^(?:chrome|moz)-extension:\/\//.test(origin);
    const send = (status, body) => {
      response.writeHead(status, {
        'Content-Type': 'application/json; charset=utf-8',
        'Cache-Control': 'no-store',
        ...(fromExtension ? { 'Access-Control-Allow-Origin': origin, Vary: 'Origin' } : {}),
      });
      response.end(body);
    };
    if (request.method === 'OPTIONS') {
      response.writeHead(fromExtension ? 204 : 403, fromExtension ? {
        'Access-Control-Allow-Origin': origin,
        'Access-Control-Allow-Methods': 'GET, POST',
        'Access-Control-Allow-Headers': 'content-type, x-lean-lens-token',
        'Access-Control-Max-Age': '600',
        Vary: 'Origin',
      } : {});
      response.end();
      return;
    }
    if (!authorized(request.headers, port, helper.config.token)) {
      send(401, JSON.stringify({ error: 'Not authorized: check the helper token in the extension options' }));
      return;
    }
    const chunks = [];
    let size = 0;
    request.on('data', (chunk) => {
      size += chunk.length;
      if (size > MAX_BODY_BYTES) request.destroy(); else chunks.push(chunk);
    });
    request.on('end', () => {
      let body = null;
      try {
        if (chunks.length) body = JSON.parse(Buffer.concat(chunks).toString('utf8'));
      } catch {
        send(400, JSON.stringify({ error: 'The request body is not JSON' }));
        return;
      }
      try {
        const result = helper.handle(request.method, request.url, body);
        send(result.status, result.body);
      } catch (error) {
        send(500, JSON.stringify({ error: error.message }));
      }
    });
  });
  // It answers once it knows whether this system has a sandbox: until then `/status` would say
  // 'checking', which is neither the one nor the other to whoever asks.
  return helper.sandbox().then(() => new Promise((resolve, reject) => {
    server.once('error', reject);
    server.listen(port, '127.0.0.1', () => resolve(server));
  }));
}

// ---------------------------------------------------------------------------------------------
// Command line.

const USAGE = `Lean Lens helper: real Lean hovers and proof states for the extension.

  node lean-lens-helper.mjs [options]                  start the helper
  node lean-lens-helper.mjs run --repo owner/repo --sha COMMIT [--pr N] File.lean …
                                                       elaborate files once, without the extension
  node lean-lens-helper.mjs clean [--all]              remove what the helper keeps on disk
                                                       (--all: the results of earlier runs too)
  node lean-lens-helper.mjs codespaces [--stop | --delete]
                                                       list, stop or delete the codespaces it made

Options
  --port N                  port on 127.0.0.1 (default ${DEFAULT_PORT})
  --allow owner/repo        allow a repository (remembered; can be repeated)
  --link owner/repo=PATH    start from your existing checkout of a repository, so its commits
                            and its build are reused instead of downloaded (remembered)
  --commits-only            take a linked checkout's commits, but not its build
  --keep-builds             keep each repository's copy and build between runs (about 10 GB for
                            a project that uses Mathlib). Without it they are removed after
                            --tidy-after minutes without a run, and when the helper stops
  --tidy-after MINUTES      how long an unused build stays (default ${DEFAULT_TIDY_MINUTES}; 0: until its run is over)
  --codespaces              run Lean in GitHub Codespaces on your account instead of on this
                            machine: one codespace for each repository, made when you first
                            run Lean on it. Needs \`gh\`, signed in, with the codespace scope
  --here owner/repo         with --codespaces: run this repository on this machine all the same
                            (can be repeated). For one whose codespace cannot be set up
  --keep-codespaces         leave codespaces running when idle and when the helper stops
                            (not with --no-sandbox: each run's codespace is deleted after it)
  --codespace-machine NAME  the machine for codespaces it creates (default basicLinux32gb, two
                            cores; standardLinux32gb has four and uses the allowance twice as fast)
  --gh PATH                 the \`gh\` program to use
  --cache DIR               where settings, results and (unless --builds says otherwise) clones
                            and builds are kept
  --builds DIR              where clones and builds go instead: the large part, which is removed
                            again (see --keep-builds)
  --jobs N                  files elaborated at once
  --subverso URL-or-PATH    where to get SubVerso (default ${DEFAULT_SUBVERSO})
  --subverso-rev REV        SubVerso revision to build
  --clone-base URL          where repositories are cloned from (default ${DEFAULT_CLONE_BASE})
  --no-sandbox              run a project's code with your own permissions and environment
                            (without this, no working sandbox means no run)
`;

async function clean(values) {
  const result = await cleanCache(values.cache, { results: values.all, force: values.force, buildsDir: values.builds });
  if (!result.removed.length) {
    console.log(`Nothing to remove in ${result.dir}.`);
  } else {
    console.log(`Removed ${formatBytes(result.bytes)} from ${result.dir}: ${result.removed.map((entry) => `${entry.what} (${formatBytes(entry.bytes)})`).join(', ')}.`);
    if (result.freed !== null && result.bytes > 100e6 && result.freed < result.bytes / 2) {
      console.log(`The disk gained about ${formatBytes(result.freed)}: the copy of a linked checkout shares its space with the original.`);
    }
  }
  if (result.toolchains.length) console.log(`Uninstalled the Lean versions the helper had installed: ${result.toolchains.join(', ')}.`);
  console.log(values.all ? 'The settings are kept.' : 'The settings and the results of earlier runs are kept (`clean --all` removes the results too).');
}

async function codespacesCommand(values) {
  const { createCodespaces } = await import('./codespaces.mjs');
  const cacheDir = path.resolve(values.cache || defaultCacheDir());
  const { config, save } = loadConfig(cacheDir);
  const spaces = createCodespaces({ config, save, run, log: console.log, gh: values.gh, recordsDir: path.join(cacheDir, 'codespaces') });
  const ours = await spaces.ours();
  if (!ours.length) console.log('There are no Lean Lens codespaces.');
  for (const space of ours) {
    if (values.delete) {
      await spaces.remove(space.name);
      console.log(`Deleted ${space.name} (${space.repository})`);
    } else if (values.stop && space.state !== 'Shutdown') {
      await spaces.stop(space.name);
      console.log(`Stopped ${space.name} (${space.repository})`);
    } else {
      console.log(`${space.name}  ${space.repository}  ${space.state}  last used ${space.lastUsedAt || 'never'}`);
    }
  }
}

async function main() {
  const { values, positionals } = parseArgs({
    allowPositionals: true,
    options: {
      port: { type: 'string' }, cache: { type: 'string' }, builds: { type: 'string' }, jobs: { type: 'string' },
      allow: { type: 'string', multiple: true }, link: { type: 'string', multiple: true }, here: { type: 'string', multiple: true },
      subverso: { type: 'string' }, 'subverso-rev': { type: 'string' }, 'clone-base': { type: 'string' },
      repo: { type: 'string' }, sha: { type: 'string' }, pr: { type: 'string' }, 'no-sandbox': { type: 'boolean' },
      'keep-builds': { type: 'boolean' }, 'tidy-after': { type: 'string' }, all: { type: 'boolean' }, force: { type: 'boolean' },
      codespaces: { type: 'boolean' }, 'keep-codespaces': { type: 'boolean' }, gh: { type: 'string' }, 'codespace-machine': { type: 'string' },
      stop: { type: 'boolean' }, delete: { type: 'boolean' }, 'commits-only': { type: 'boolean' },
      help: { type: 'boolean', short: 'h' },
    },
  });
  if (values.help) { console.log(USAGE); return; }
  // What happens when the helper is told to stop (Ctrl-C, or the terminal closing).
  let stop = () => { stopCommands(); process.exit(130); };
  for (const signal of ['SIGINT', 'SIGTERM', 'SIGHUP']) process.on(signal, () => stop());

  if (positionals[0] === 'clean') { await clean(values); return; }
  if (positionals[0] === 'codespaces') { await codespacesCommand(values); return; }

  const helper = createHelper({
    cacheDir: values.cache, buildsDir: values.builds, jobs: values.jobs, subverso: values.subverso, subversoRev: values['subverso-rev'],
    cloneBase: values['clone-base'], sandbox: !values['no-sandbox'],
    keepBuilds: values['keep-builds'], tidyMinutes: values['tidy-after'], linkedBuilds: !values['commits-only'],
    codespaces: values.codespaces ? (await import('./codespaces.mjs')).createCodespaces : null,
    gh: values.gh, keepCodespaces: values['keep-codespaces'], machine: values['codespace-machine'], here: values.here,
  });
  for (const repo of values.here || []) if (!isRepo(repo)) throw new Error(`--here takes owner/repo, not ${repo}`);
  stop = () => { helper.shutdown(); process.exit(130); };
  if (helper.remote) await helper.remote.check(); // `gh` is there and may use codespaces
  // Codespaces an earlier helper made for runs without a sandbox and did not get to delete.
  if (helper.remote) helper.remote.tidy();
  const sandboxLine = helper.remote
    ? `Lean runs in GitHub Codespaces on your account, ${values['no-sandbox'] ? 'without a sandbox (--no-sandbox): each run gets a new codespace, deleted after it' : 'one for each repository'}, and not on this machine${(values.here || []).length ? ` (except for ${values.here.join(', ')})` : ''}`
    : `Sandbox ${{
      seatbelt: "on: the project's code runs without network access and cannot read or change your files",
      bwrap: "on: the project's code runs without network access and sees none of your files",
      none: 'not available on this system, so Lean will not run (on Linux, install bubblewrap; or start with --no-sandbox to run Lean with your permissions)',
      off: 'off (--no-sandbox): Lean runs with your permissions',
    }[await helper.sandbox()]}`;
  for (const entry of values.link || []) {
    const split = entry.indexOf('=');
    if (split < 1) throw new Error(`--link takes owner/repo=PATH, not ${entry}`);
    helper.link(entry.slice(0, split), entry.slice(split + 1));
  }
  for (const repo of values.allow || []) helper.allow(repo);

  if (positionals[0] === 'run') {
    const paths = positionals.slice(1);
    if (!isRepo(values.repo) || !isSha(values.sha) || !paths.length || !paths.every(isLeanPath)) {
      throw new Error('run needs --repo owner/repo, --sha with a full commit hash, and Lean files');
    }
    helper.allow(values.repo);
    console.log(sandboxLine);
    helper.start({ repo: values.repo, sha: values.sha, pr: Number(values.pr) || null, paths });
    await new Promise((resolve) => {
      const poll = setInterval(() => {
        const state = helper.status(values.repo, values.sha).state;
        if (state === 'done' || state === 'error') { clearInterval(poll); resolve(); }
      }, 300);
    });
    let failed = helper.status(values.repo, values.sha).state === 'error';
    for (const file of paths) {
      const state = helper.fileState(values.repo, values.sha, file);
      console.log(`${file}: ${state.state}${state.error ? ` (${state.error})` : ''}`);
      if (state.state !== 'ready') failed = true;
    }
    if (failed) process.exitCode = 1;
    await helper.idle();
    helper.shutdown();
    return;
  }

  const port = Number(values.port) || DEFAULT_PORT;
  const server = await serve(helper, port).catch(async (error) => {
    if (error.code !== 'EADDRINUSE') throw error;
    // Who has the port? A helper started earlier answers, to this one's token when they share
    // their settings and with its own refusal when they don't.
    const other = await fetch(`http://127.0.0.1:${port}/status`, { headers: { 'X-Lean-Lens-Token': helper.config.token }, signal: AbortSignal.timeout(2000) })
      .then((response) => response.json()).catch(() => null);
    throw new Error(other && (other.name === 'lean-lens-helper' || /helper token/.test(other.error || ''))
      ? `A Lean Lens helper is already running on port ${port}. Stop that one first (Ctrl-C in its terminal), then start this one: two cannot share the address the extension talks to.`
      : `Port ${port} is in use by another program. Start the helper on another port with --port, and put the new address in the extension's options.`);
  });
  stop = () => {
    console.log(`\nStopping.${helper.remote
      ? (helper.keepCodespaces ? '' : ' Stopping the codespaces that were used; the results stay here.')
      : (helper.keepBuilds ? '' : ' Removing the builds; the results stay.')}`);
    server.close();
    helper.shutdown();
    process.exit(0);
  };
  const minutes = `${helper.tidyMinutes} minute${helper.tidyMinutes === 1 ? '' : 's'}`;
  console.log(`Lean Lens helper is running.

  Address  http://127.0.0.1:${port}
  Token    ${helper.config.token}

Paste both into the extension's options, under "Real Lean".
${sandboxLine}.
Allowed repositories: ${helper.config.allow.length ? helper.config.allow.join(', ') : 'none yet (allow one from the extension, or with --allow owner/repo)'}
Kept in: ${helper.cacheDir} (${formatBytes(await sizeOf(helper.cacheDir))} now)${helper.buildsDir === helper.cacheDir ? '' : `\nBuilds go to: ${helper.buildsDir}`}
${helper.remote
    ? `Codespaces: ${helper.keepCodespaces
      ? 'left running (--keep-codespaces); GitHub stops an idle one by itself.'
      : `one is stopped ${helper.tidyMinutes ? `after ${minutes} without a run` : 'when its run is over'}, and when the helper stops. The results are kept here.`}`
    : `Builds: ${helper.keepBuilds
      ? 'kept between runs (--keep-builds). `clean` removes them.'
      : `a repository's copy and build are removed ${helper.tidyMinutes ? `after ${minutes} without a run` : 'when its run is over'}, and when the helper stops. The results stay.`}`}
`);
}

// Run as a program (not imported): compared by real path, since Node loads the file by its real
// path while the command line may name it through a link (`/var` on macOS is one).
if (process.argv[1] && realOrSame(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main().catch((error) => {
    console.error(error.message);
    process.exitCode = 1;
  });
}
