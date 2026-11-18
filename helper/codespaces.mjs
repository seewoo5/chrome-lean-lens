// Lean in a GitHub Codespace instead of on this machine.
//
// The local helper stays what the extension talks to, and keeps the results. What changes is
// where Lean runs: each repository gets a codespace of the reader's own, started on that
// repository, with this same helper running in it. A run is handed to that helper through
// `gh`'s port forwarding, its progress is mirrored here and its results are copied here, so
// they stay when the codespace stops. `gh` (signed in, with the `codespace` scope) does all
// the talking to GitHub, and this machine needs no Lean.
//
// GitHub's terms allow a codespace for developing or testing the repository it was started
// on, which is why there is one for each repository rather than one for everything.
//
// That one codespace is used again and again because the sandbox in it keeps a pull request's
// code from changing it. Without the sandbox (`--no-sandbox`) nothing does, so then every run
// gets a codespace of its own, made for it and deleted after it: see `runAlone`.

import { spawn, spawnSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import http from 'node:http';
import net from 'node:net';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

export const REMOTE_PORT = 5326;
const NODE_VERSION = '22.11.0';
const MACHINE = 'basicLinux32gb'; // the smallest: 2 cores, 8 GB of memory, 32 GB of disk
const RETENTION = '168h'; // a stopped codespace nobody comes back to is deleted after a week
// A codespace made for one run without a sandbox is deleted by the helper after the run. Should
// that never happen (the helper and its notes both lost), GitHub deletes it soon after it stops.
const RETENTION_ALONE = '1h';
const LIST_LIMIT = 200; // as many codespaces as `gh` is asked to list
// When builds have to go on the disk that is kept, they leave it before GitHub stops the
// codespace for being idle (30 minutes by default), so a stopped codespace takes little of the
// reader's storage allowance. On the temporary disk they stay while the codespace runs.
const REMOTE_TIDY_MINUTES = 15;
export const DISPLAY_PREFIX = 'Lean Lens';
// GitHub stops a codespace 30 minutes after the last sign of someone using it. Requests through
// a forwarded port are no such sign, and neither is Lean at work: a codespace was stopped while
// both went on. A connection over ssh is one. So during a run the helper connects now and then.
const KEEP_ALIVE_MS = 8 * 60 * 1000;

const here = path.dirname(fileURLToPath(import.meta.url));
const quote = (value) => `'${String(value).replace(/'/g, `'\\''`)}'`;
const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));
const tail = (text, n = 400) => (text.length > n ? `…${text.slice(-n)}` : text).trim();
const isRepoName = (repo) => typeof repo === 'string' && /^[A-Za-z0-9_.-]{1,100}\/[A-Za-z0-9_.-]{1,100}$/.test(repo);

/**
 * The name a repository's codespace is given, so it can be found again. GitHub takes 48
 * characters at most, and refuses some punctuation (a colon, for one).
 */
export const displayNameFor = (repo) => `${DISPLAY_PREFIX} ${repo.split('/')[1].replace(/[^A-Za-z0-9_-]+/g, '-')}`.slice(0, 48);
/**
 * The name shown for a codespace made for one run without a sandbox. It is there for the reader
 * to recognise it by, and differs from `displayNameFor` so that no such codespace is taken for
 * a repository's lasting one. The helper itself never looks for one of these by this name: it
 * goes by the identifier GitHub gave the codespace, which it noted (see `runAlone`).
 */
export const unsandboxedNameFor = (repo) => `${DISPLAY_PREFIX} unsandboxed ${repo.split('/')[1].replace(/[^A-Za-z0-9_-]+/g, '-')}`.slice(0, 48);

/** Whether this can be the identifier GitHub gives a codespace (it becomes an argument and a file name). */
const isCodespaceName = (name) => typeof name === 'string' && /^[A-Za-z0-9][A-Za-z0-9_-]{0,99}$/.test(name);

/** Whether a process is running (one that may not be signalled is). */
function alive(pid) {
  if (!Number.isInteger(pid) || pid <= 0) return false;
  try { process.kill(pid, 0); return true; } catch (error) { return error.code === 'EPERM'; }
}

/**
 * When a process started, as `ps` puts it, or null when that cannot be asked. It tells a
 * process from a later one that was given the same number (after a restart of the machine or
 * of a container, numbers come round again).
 */
function startOf(pid) {
  const asked = spawnSync('ps', ['-o', 'lstart=', '-p', String(pid)], { encoding: 'utf8', timeout: 10 * 1000, env: { ...process.env, LC_ALL: 'C' } });
  return asked.status === 0 && asked.stdout.trim() ? asked.stdout.trim() : null;
}
let ownStart; // of this process: asked once, when first needed
// The helpers of this process (their `instance`) that have not stopped.
const running = new Set();

/** Whether a helper that reports this sandbox keeps a pull request's code away from the rest. */
export const confines = (sandbox) => sandbox === 'seatbelt' || sandbox === 'bwrap';

// Run in the codespace over ssh: the script arrives on standard input, is saved, then run. It
// runs as a login shell would: that is where a codespace keeps what `git` needs to reach
// GitHub with the codespace's own credentials (a session over ssh starts without them), and the
// helper started from the script takes them along for fetching commits.
const BOOT_COMMAND = 'umask 077; mkdir -p "$HOME/.lean-lens" && cat > "$HOME/.lean-lens/bootstrap.sh" && bash -l "$HOME/.lean-lens/bootstrap.sh"';
// Stops the helper there and waits for it: as it stops, it removes the builds it kept.
const STOP_COMMAND = 'P="$(cat "$HOME/.lean-lens/helper.pid" 2>/dev/null)"; [ -n "$P" ] && kill "$P" 2>/dev/null; for _ in $(seq 1 150); do kill -0 "$P" 2>/dev/null || break; sleep 0.2; done; true';

/**
 * The script that sets up and starts the helper in a codespace: the helper's files, Node if
 * the codespace has none, elan, bubblewrap for the sandbox, then the helper itself with the
 * token chosen for this codespace. It prints `LEANLENS …` lines as it goes, and at the end
 * `LEANLENS READY {the helper's status}` or `LEANLENS-ERROR …`.
 */
export function bootstrapScript({ files, token, repo, port = REMOTE_PORT, tidyMinutes = REMOTE_TIDY_MINUTES, sandbox = true, cloneBase = null, nodeVersion = NODE_VERSION }) {
  const base64 = (text) => Buffer.from(text, 'utf8').toString('base64');
  const status = `fetch(process.argv[1], { headers: { "X-Lean-Lens-Token": process.argv[2] } }).then(async (r) => { if (!r.ok) process.exit(1); process.stdout.write(await r.text()); }, () => process.exit(1))`;
  const settings = `const fs = require("fs"); let c = {}; try { c = JSON.parse(fs.readFileSync(process.argv[1], "utf8")); } catch {} c.token = process.argv[2]; fs.writeFileSync(process.argv[1], JSON.stringify(c, null, 2) + "\\n", { mode: 0o600 });`;
  return `#!/usr/bin/env bash
# Lean Lens: sets up and starts the helper in this codespace. The helper on the reader's
# machine sends this each time it connects, so it is made to be run again and again.
umask 077
say() { printf 'LEANLENS %s\\n' "$*"; }
fail() { printf 'LEANLENS-ERROR %s\\n' "$*"; exit 1; }
fetch() { if command -v curl >/dev/null 2>&1; then curl -fsSL "$1"; else wget -qO- "$1"; fi; }
# When a repository's own dev container cannot be set up, GitHub starts the codespace in
# "recovery mode": a bare container in which Lean cannot be installed.
RECOVERY="\${LEAN_LENS_RECOVERY_FILE:-/workspaces/.codespaces/.persistedshare/RECOVERY-REASON-FILE}"
[ -f "$RECOVERY" ] && fail "RECOVERY $(head -c 160 "$RECOVERY" | tr '\n' ' ')"
DIR="$HOME/.lean-lens"
mkdir -p "$DIR/cache" && cd "$DIR" || fail "cannot use $DIR"

# The helper's own files, as the reader's machine has them. CHANGED says whether any differs
# from what is here already.
CHANGED=""
put() {
  printf '%s' "$2" | base64 -d > "$1.new" || return 1
  if cmp -s "$1.new" "$1" 2>/dev/null; then rm -f "$1.new"; else mv "$1.new" "$1" && CHANGED=1; fi
}
${Object.entries(files).map(([name, content]) => `put ${quote(name)} ${quote(base64(content))} || fail ${quote(`could not write ${name}`)}`).join('\n')}

# Node 20 or later: the codespace's own, or one downloaded next to the helper.
NODE=node
if ! node -e 'process.exit(Number(process.versions.node.split(".")[0]) >= 20 ? 0 : 1)' >/dev/null 2>&1; then
  NODE="$DIR/node/bin/node"
  if [ ! -x "$NODE" ]; then
    [ -n "\${LEAN_LENS_SKIP_INSTALL:-}" ] && fail "Node 20 or later is needed"
    say "Installing Node"
    case "$(uname -m)" in x86_64) ARCH=x64 ;; aarch64 | arm64) ARCH=arm64 ;; *) fail "there is no Node for $(uname -m)" ;; esac
    rm -rf node node.new && mkdir node.new &&
      fetch "https://nodejs.org/dist/v${nodeVersion}/node-v${nodeVersion}-linux-$ARCH.tar.gz" | tar -xz -C node.new --strip-components=1 &&
      mv node.new node || fail "Node could not be installed"
  fi
fi

# elan, which installs the Lean version each project asks for.
export PATH="$HOME/.elan/bin:$PATH"
if ! command -v elan >/dev/null 2>&1 && [ -z "\${LEAN_LENS_SKIP_INSTALL:-}" ]; then
  say "Installing elan, Lean's version manager"
  fetch https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none >/dev/null 2>&1 || fail "elan could not be installed"
fi

# bubblewrap, which confines the code of a pull request.
if ! command -v bwrap >/dev/null 2>&1 && [ -z "\${LEAN_LENS_SKIP_INSTALL:-}" ] && command -v apt-get >/dev/null 2>&1 && command -v sudo >/dev/null 2>&1; then
  say "Installing bubblewrap, the sandbox"
  (sudo -n apt-get update -qq && sudo -n env DEBIAN_FRONTEND=noninteractive apt-get install -y -qq bubblewrap) >/dev/null 2>&1 || true
fi

# Builds go where there is the most room. In a codespace that is its temporary disk: larger
# than the one that is kept and counted against the reader's storage, and emptied when the
# codespace stops, which suits files that are only needed while Lean runs.
free() { df -Pk "$1" 2>/dev/null | awk 'NR == 2 { print $4 }'; }
BUILDS="$DIR/cache"
KEEP="--tidy-after ${Number(tidyMinutes)}"
if [ -z "\${LEAN_LENS_SKIP_INSTALL:-}" ] && [ "$(free /tmp)" -gt "$(free "$DIR")" ] 2>/dev/null; then
  BUILDS="/tmp/lean-lens-$(id -u)"
  KEEP="--keep-builds"
  mkdir -p "$BUILDS" && [ -O "$BUILDS" ] && [ ! -L "$BUILDS" ] || fail "cannot use $BUILDS"
fi

# The codespace's own checkout is where the helper's copy starts from: its commits, not its
# build, which the codespace's own setup may still be fetching (mathlib4's does that).
CHECKOUT="\${LEAN_LENS_CHECKOUT:-\${CODESPACE_VSCODE_FOLDER:-/workspaces/${repo.split('/')[1]}}}"
set -- "$DIR/lean-lens-helper.mjs" --port ${Number(port)} --cache "$DIR/cache" --builds "$BUILDS" $KEEP --allow ${quote(repo)}${sandbox ? '' : ' --no-sandbox'}${cloneBase ? ` --clone-base ${quote(cloneBase)}` : ''}
[ -d "$CHECKOUT/.git" ] && set -- "$@" --commits-only --link ${quote(`${repo}=`)}"$CHECKOUT"

answers() { "$NODE" -e '${status}' "http://127.0.0.1:${Number(port)}/status" ${quote(token)} 2>/dev/null; }

# The same helper, still running from an earlier connection (the reader's machine slept, or its
# network went): it is left alone, and so are the runs it has under way.
OLD="$(cat helper.pid 2>/dev/null)"
if [ -z "$CHANGED" ] && [ "$(cat started-as 2>/dev/null)" = "$*" ] && [ -n "$OLD" ] && kill -0 "$OLD" 2>/dev/null; then
  STATUS="$(answers)" && { say "READY $STATUS"; exit 0; }
fi

# Otherwise a helper left from before stops first (it removes its builds as it goes).
if [ -n "$OLD" ] && kill -0 "$OLD" 2>/dev/null; then
  kill "$OLD" 2>/dev/null
  for _ in $(seq 1 150); do kill -0 "$OLD" 2>/dev/null || break; sleep 0.2; done
  kill -9 "$OLD" 2>/dev/null
fi

# Its token is the one the reader's machine chose for this codespace.
"$NODE" -e '${settings}' "$DIR/cache/config.json" ${quote(token)} || fail "could not write the settings"
printf '%s' "$*" > started-as

if command -v setsid >/dev/null 2>&1; then
  setsid nohup "$NODE" "$@" > helper.log 2>&1 < /dev/null &
else
  nohup "$NODE" "$@" > helper.log 2>&1 < /dev/null &
fi
echo $! > helper.pid

for _ in $(seq 1 300); do
  STATUS="$(answers)" && { say "READY $STATUS"; exit 0; }
  kill -0 "$(cat helper.pid)" 2>/dev/null || fail "the helper stopped: $(tail -n 3 helper.log | tr '\\n' ' ')"
  sleep 0.2
done
fail "the helper did not answer"
`;
}

/** A port on this machine that nothing is listening on. */
function freePort() {
  return new Promise((resolve, reject) => {
    const server = net.createServer();
    server.on('error', reject);
    server.listen(0, '127.0.0.1', () => {
      const { port } = server.address();
      server.close(() => resolve(port));
    });
  });
}

function stopChild(child) {
  try {
    process.kill(-child.pid, 'SIGKILL');
  } catch {
    try { child.kill('SIGKILL'); } catch { /* already gone */ }
  }
}

/** What `gh` said when it failed, with the way out where there is one. */
function explain(result) {
  const said = `${result.stderr || ''}\n${result.stdout || ''}`;
  if (result.code === -1 && /ENOENT/.test(said)) return 'The GitHub command line tool `gh` is not installed (https://cli.github.com)';
  if (/"codespace" scope/.test(said)) return '`gh` may not use codespaces yet. Run: gh auth refresh -h github.com -s codespace';
  if (/gh auth login/.test(said)) return '`gh` is not signed in. Run: gh auth login';
  if (/SSH server/i.test(said)) return "The codespace has no SSH server, so the helper cannot be started in it (the repository's own dev container lacks one)";
  // (Without gh's own notes, such as who pays for the codespace.)
  return tail(said.split('\n').filter((line) => !/^\s*✓/.test(line)).join('\n')) || `gh exited with ${result.code}`;
}

/**
 * @param {object} options
 *   `config`, `save`: the helper's settings (the codespace of each repository is remembered there);
 *   `run`: the helper's command runner; `log`; `gh`: the program to call;
 *   `sandbox`: false when the reader accepted running without one (`--no-sandbox`);
 *   `keep`: leave codespaces running when they are idle and when the helper stops;
 *   `recordsDir`: the folder where the codespaces made for runs without a sandbox are noted.
 * @returns `{check, runJob, rest, shutdown, ours, stop, remove, tidy}`
 */
export function createCodespaces({ config, save, run, log, gh = 'gh', sandbox = true, keep = false, recordsDir = null, remotePort = REMOTE_PORT, cloneBase = null, pollMs = 1500, keepAliveMs = KEEP_ALIVE_MS, retryMs = 10 * 1000, machine = MACHINE, helperDir = here }) {
  if (!/^[A-Za-z0-9]+$/.test(machine)) throw new Error(`Not a codespace machine name: ${machine}`);
  if (!config.codespaces || typeof config.codespaces !== 'object') config.codespaces = {};
  const sessions = new Map(); // repo → {name, token, port, tunnel, sandbox}
  const connecting = new Map(); // repo → promise of its session
  // The codespaces this helper made for runs without a sandbox and has not deleted yet:
  // identifier → {repo, session}. Each is also noted in `recordsDir` (see `note`).
  const alone = new Map();
  const instance = randomBytes(8).toString('hex'); // this helper, among those that share `recordsDir`
  running.add(instance);
  if (!Array.isArray(config.retired)) config.retired = [];

  async function must(args, options) {
    const result = await run(gh, args, options);
    if (result.code !== 0) throw new Error(explain(result));
    return result;
  }

  /** Whether `gh` is there and may use codespaces. Throws with what to do when it isn't. */
  async function check() {
    await must(['codespace', 'list', '--limit', '1', '--json', 'name']);
  }

  const list = async () => JSON.parse((await must(['codespace', 'list', '--limit', String(LIST_LIMIT), '--json', 'name,displayName,repository,state,lastUsedAt'])).stdout || '[]');
  /**
   * The codespaces this helper's settings and notes name, on whichever repository: each
   * repository's lasting one, those an earlier version used and this one no longer does
   * (`retire`), and those made for runs without a sandbox. They are found by the identifier
   * GitHub gave them, never by the name shown for them, which other codespaces can have too.
   * One whose run is under way in a helper that is still running comes with `busy` set.
   */
  async function ours() {
    const named = new Map(); // identifier → what to add to its listing
    for (const known of Object.values(config.codespaces)) if (known && isCodespaceName(known.name)) named.set(known.name, {});
    for (const old of config.retired) if (old && isCodespaceName(old.name)) named.set(old.name, {});
    for (const entry of notes()) named.set(entry.name, entry.instance !== instance && stillRuns(entry) ? { busy: entry.pid } : {});
    return (await list()).filter((space) => named.has(space.name)).map((space) => ({ ...space, ...named.get(space.name) }));
  }

  /** A request to the helper in the codespace, through the forwarded port. */
  function call(session, method, pathname, body, timeoutMs = 30000) {
    return new Promise((resolve, reject) => {
      const payload = body === undefined ? null : Buffer.from(JSON.stringify(body));
      const request = http.request({
        host: '127.0.0.1', port: session.port, method, path: pathname, timeout: timeoutMs,
        headers: {
          // The address the helper has in the codespace: it answers to no other name.
          Host: `127.0.0.1:${remotePort}`,
          'X-Lean-Lens-Token': session.token,
          ...(payload ? { 'Content-Type': 'application/json', 'Content-Length': payload.length } : {}),
        },
      }, (response) => {
        const chunks = [];
        response.on('data', (chunk) => chunks.push(chunk));
        response.on('error', reject);
        response.on('end', () => {
          let json = null;
          try { json = JSON.parse(Buffer.concat(chunks).toString('utf8')); } catch { /* not JSON */ }
          resolve({ status: response.statusCode, json });
        });
      });
      request.on('timeout', () => request.destroy(new Error('The codespace did not answer in time')));
      request.on('error', reject);
      request.end(payload || undefined);
    });
  }

  /** Set up and start the helper in a codespace (starting the codespace if it was stopped). */
  async function boot(name, repo, token, say) {
    const script = bootstrapScript({
      files: Object.fromEntries(['lean-lens-helper.mjs', 'convert.mjs'].map((file) => [file, readFileSync(path.join(helperDir, file), 'utf8')])),
      token, repo, port: remotePort, sandbox, cloneBase,
    });
    const result = await run(gh, ['codespace', 'ssh', '-c', name, '--', BOOT_COMMAND], {
      input: script,
      timeoutMs: 20 * 60 * 1000,
      onLine: (line) => { if (/^LEANLENS (?!READY )/.test(line)) say(line.slice(9)); },
    });
    const ready = result.stdout.match(/^LEANLENS READY (.*)$/m);
    if (!ready) {
      const failed = result.stdout.match(/^LEANLENS-ERROR (.*)$/m);
      if (failed && failed[1].startsWith('RECOVERY')) {
        const error = new Error(`GitHub could not set up ${repo}'s own dev container, and started the codespace in recovery mode, where Lean cannot be installed (${failed[1].slice(9).trim() || 'no reason given'}). To run this repository on your machine instead, start the helper with --here ${repo}.`);
        error.recovery = true;
        throw error;
      }
      throw new Error(failed ? `The helper could not be started in the codespace: ${failed[1]}` : explain(result));
    }
    return JSON.parse(ready[1]);
  }

  /** Forward the helper's port in the codespace to a port here. Resolves once it answers. */
  async function forward(name, token) {
    const port = await freePort();
    const tunnel = spawn(gh, ['codespace', 'ports', 'forward', `${remotePort}:${port}`, '-c', name], { stdio: ['ignore', 'pipe', 'pipe'], detached: true });
    let said = '';
    tunnel.stdout.on('data', (chunk) => { said = (said + chunk).slice(-4000); });
    tunnel.stderr.on('data', (chunk) => { said = (said + chunk).slice(-4000); });
    tunnel.on('error', (error) => { said += error.message; });
    for (let tries = 0; tries < 200; tries++) {
      if (tunnel.exitCode !== null || tunnel.signalCode !== null) throw new Error(`The connection to the codespace could not be made: ${tail(said) || 'gh stopped'}`);
      const answer = await call({ port, token }, 'GET', '/status', undefined, 3000).catch(() => null);
      if (answer && answer.status === 200) return { port, tunnel };
      if (answer && answer.status === 401) { stopChild(tunnel); throw new Error('The helper in the codespace did not accept its token'); }
      await sleep(200);
    }
    stopChild(tunnel);
    throw new Error('The helper in the codespace did not answer through the forwarded port');
  }

  /** Create a codespace on a repository. Resolves to the identifier GitHub gave it. */
  async function create(repo, displayName, retention, say) {
    say(`Creating a codespace for ${repo}`);
    const make = (size) => run(gh, ['codespace', 'create', '--repo', repo, '--machine', size, '--display-name', displayName,
      '--retention-period', retention, '--default-permissions'], { timeoutMs: 15 * 60 * 1000 });
    let created = await make(machine);
    // A repository can ask for more than the smallest machine (mathlib4 does). gh then names
    // the ones it allows: the first of those is taken, unless a machine was asked for by name.
    const offered = created.code === 0 ? null : /Available machines: \[([^\]]*)\]/.exec(`${created.stderr}\n${created.stdout}`);
    const larger = offered ? offered[1].split(/[\s,]+/).filter((size) => /^[A-Za-z0-9]+$/.test(size)) : [];
    if (larger.length && machine === MACHINE) {
      say(`${repo} needs a larger codespace than the smallest: using ${larger[0]}, which uses your allowance faster`);
      created = await make(larger[0]);
    }
    if (created.code !== 0) throw new Error(explain(created));
    const name = created.stdout.trim().split('\n').pop().trim();
    if (!name) throw new Error('`gh codespace create` did not say which codespace it made');
    // gh says whose allowance the codespace is charged to: worth passing on.
    const payer = (created.stderr || '').split('\n').find((line) => /paid for by/.test(line));
    if (payer) log(`${repo}: ${payer.replace(/^[\s✓]+/, '')}`);
    return name;
  }

  /**
   * Wait for GitHub to set a codespace up. A repository's own dev container can take many
   * minutes to build, longer than gh waits when asked to connect. So the wait is here.
   */
  async function settled(name, say) {
    for (let waited = 0; waited < 45 * 60 * 1000; waited += retryMs) {
      const now = (await list()).find((entry) => entry.name === name);
      if (!now || now.state !== 'Provisioning') break;
      if (!waited) say(`Waiting for GitHub to set up the codespace ${name}`);
      await sleep(retryMs);
    }
  }

  /**
   * Stop using the codespace the settings name for a repository. One that is still there and
   * that an earlier version of the helper used is kept in the settings as retired, so that
   * `codespaces --delete` finds it: under those versions, code could run in it without a
   * sandbox (with --no-sandbox, or where the codespace had none and the reader could not push
   * to the repository), and may have changed it. It is not deleted here: those versions also
   * took over a codespace by its name, so it need not be one the helper made.
   */
  function retire(repo, all) {
    const known = config.codespaces[repo];
    delete config.codespaces[repo];
    if (known && isCodespaceName(known.name) && known.confined !== true && all.some((entry) => entry.name === known.name)) {
      if (!config.retired.some((old) => old && old.name === known.name)) config.retired.push({ name: known.name, repo });
      log(`${repo}: the codespace ${known.name}, which an earlier version of the helper used, is not used any more: code may have run in it without a sandbox. A new one is made. To delete the old one: node lean-lens-helper.mjs codespaces --delete (or: gh codespace delete -c ${known.name})`);
    }
    save();
  }

  /** Connect to a repository's lasting codespace, where the sandbox confines each run. */
  async function connect(repo, say) {
    const all = await list();
    // The codespace these settings name for the repository, by the identifier GitHub gave it,
    // and only one that this version made (`confined`): in such a one, a pull request's code
    // has only ever run in the sandbox. No codespace is taken over because of its repository
    // and the name shown for it: that could be another helper's (the two would stop each
    // other's runs), or one in which code ran without a sandbox. Nor one noted as made for a
    // run without a sandbox, whatever it is called by now.
    let known = config.codespaces[repo];
    const noted = new Set(notes().map((entry) => entry.name));
    let space = known && known.confined === true && !noted.has(known.name) ? all.find((entry) => entry.name === known.name) : null;
    if (known && !space) {
      retire(repo, all);
      known = null;
    }
    if (!space) space = { name: await create(repo, displayNameFor(repo), RETENTION, say), state: 'Available' };
    if (!isCodespaceName(space.name)) throw new Error(`\`gh codespace create\` answered with something that is no codespace's identifier, so nothing is run: ${tail(space.name, 80)}`);
    const token = known && typeof known.token === 'string' ? known.token : randomBytes(24).toString('base64url');
    config.codespaces[repo] = { name: space.name, token, confined: true };
    save();
    await settled(space.name, say);
    say(space.state === 'Available' ? `Setting up Lean in the codespace ${space.name}` : `Starting the codespace ${space.name}`);
    const status = await boot(space.name, repo, token, say).catch(async (error) => {
      // A codespace in recovery mode is of no use: it is stopped rather than left running.
      if (error.recovery) await run(gh, ['codespace', 'stop', '-c', space.name], { timeoutMs: 3 * 60 * 1000 });
      throw error;
    });
    // Without a working sandbox there, no run: the code could use the codespace's GitHub token
    // and change the codespace, which later runs use. (The helper there refuses as well.)
    if (!confines(status.sandbox)) {
      await run(gh, ['codespace', 'ssh', '-c', space.name, '--', STOP_COMMAND], { timeoutMs: 60 * 1000 });
      throw new Error(`The codespace for ${repo} has no working sandbox, so a pull request's code is not run there. Starting the helper with --no-sandbox runs it all the same, in a new codespace for each run.`);
    }
    const { port, tunnel } = await forward(space.name, token);
    const session = { name: space.name, token, port, tunnel, sandbox: status.sandbox };
    sessions.set(repo, session);
    return session;
  }

  /** The connection to a repository's codespace, made if there is none (or it went away). */
  function ensure(repo, say) {
    const live = sessions.get(repo);
    if (live && live.tunnel.exitCode === null && live.tunnel.signalCode === null) return Promise.resolve(live);
    drop(repo);
    if (!connecting.has(repo)) connecting.set(repo, connect(repo, say).finally(() => connecting.delete(repo)));
    return connecting.get(repo);
  }

  function drop(repo) {
    const session = sessions.get(repo);
    if (session) stopChild(session.tunnel);
    sessions.delete(repo);
  }

  // --- Runs without a sandbox (`--no-sandbox`).
  //
  // Such a run can use its codespace's GitHub token and change anything in the codespace, the
  // helper there included. So it gets a codespace nothing else has used or will use: made for
  // the run, and deleted after it. Which codespace that is, is known by one thing only: the
  // identifier GitHub answered with when it was made. It is noted on disk before anything is
  // started in the codespace, used for every connection of the run, and is what is deleted.
  // Nothing here looks a codespace up by its repository or by the name shown for it, which
  // anyone with the account can change and other codespaces can share: those may be another
  // helper's run under way, a repository's lasting codespace, or the reader's own work.

  const noteFile = (name) => path.join(recordsDir, `${name}.json`);
  /** Note a codespace made for a run without a sandbox, with the helper that made it. */
  function note(name, repo) {
    mkdirSync(recordsDir, { recursive: true, mode: 0o700 });
    if (ownStart === undefined) ownStart = startOf(process.pid);
    writeFileSync(noteFile(name), `${JSON.stringify({ name, repo, pid: process.pid, started: ownStart, instance, created: new Date().toISOString() })}\n`, { mode: 0o600 });
  }
  /**
   * Whether the helper that wrote a note is still running. Its process number alone does not
   * say: a helper started anew in a container gets the same number again, and after a restart
   * of the machine the number is some other program's. So a note with this process's number
   * is of a running helper only if that helper is one of this process's; and for another
   * process, when it started has to be what the note says (where both are known).
   */
  function stillRuns(entry) {
    if (running.has(entry.instance)) return true;
    if (entry.pid === process.pid || !alive(entry.pid)) return false;
    const now = typeof entry.started === 'string' ? startOf(entry.pid) : null;
    return now === null || now === entry.started;
  }
  const forgetNote = (name) => { if (recordsDir && isCodespaceName(name)) rmSync(noteFile(name), { force: true }); };
  /** What is noted: `[{name, repo, pid, started, instance}]`. A file that is not such a note is passed over. */
  function notes() {
    if (!recordsDir) return [];
    let files = [];
    try { files = readdirSync(recordsDir); } catch { return []; }
    const found = [];
    for (const file of files) {
      try {
        const entry = JSON.parse(readFileSync(path.join(recordsDir, file), 'utf8'));
        if (entry && isCodespaceName(entry.name) && file === `${entry.name}.json`) found.push(entry);
      } catch { /* not a note */ }
    }
    return found;
  }

  /**
   * Delete a codespace this helper's notes name, and forget it once it is gone. When it cannot
   * be deleted, the note stays, and `tidy` tries again.
   */
  async function discard(name, repo, why) {
    const mine = alone.get(name);
    if (mine && mine.session) stopChild(mine.session.tunnel);
    alone.delete(name);
    log(`Deleting the codespace ${name}${repo ? ` for ${repo}` : ''}: ${why}. The results stay.`);
    const deleted = await run(gh, ['codespace', 'delete', '-c', name, '--force'], { timeoutMs: 3 * 60 * 1000 });
    if (deleted.code === 0) { forgetNote(name); return; }
    // Gone already (deleted by hand, or by GitHub): nothing is left to delete, only to forget.
    // (Only a listing that holds all the account's codespaces says so.)
    const all = await list().catch(() => null);
    if (all && all.length < LIST_LIMIT && !all.some((space) => space.name === name)) { forgetNote(name); return; }
    log(`The codespace ${name} could not be deleted (${explain(deleted)}). It is tried again at the next run and the next start; or delete it with: gh codespace delete -c ${name}`);
  }

  /**
   * Delete the noted codespaces that no running helper is using: those of a helper that stopped
   * before it could delete its own, and those this helper failed to delete. Only what is noted
   * in `recordsDir` is ever deleted here, by the identifier noted; a codespace that merely looks
   * like one of these is left alone, and so is one whose helper is still running.
   */
  let tidying = null;
  function tidy() {
    if (!tidying) {
      tidying = (async () => {
        for (const entry of notes()) {
          if (alone.has(entry.name)) continue; // this helper's run, under way
          if (entry.instance !== instance && stillRuns(entry)) continue; // another helper's, still running
          await discard(entry.name, isRepoName(entry.repo) ? entry.repo : null, entry.instance === instance
            ? 'it ran code without a sandbox, and could not be deleted before'
            : 'a helper that has stopped made it for a run without a sandbox');
        }
      })().catch((error) => log(`Codespaces left from runs without a sandbox could not be looked through: ${error.message}`)).finally(() => { tidying = null; });
    }
    return tidying;
  }

  /**
   * Run a job without a sandbox, in a codespace made for it and deleted after it. `--keep-codespaces`
   * does not apply: a codespace that ran code without a sandbox is not used again.
   */
  async function runAlone(job, outcomes) {
    const say = (message) => job.say(message);
    if (!recordsDir) throw new Error('There is nowhere to note the codespace of a run without a sandbox, so none is made');
    await tidy();
    const name = await create(job.repo, unsandboxedNameFor(job.repo), RETENTION_ALONE, say);
    if (!isCodespaceName(name)) throw new Error(`\`gh codespace create\` answered with something that is no codespace's identifier, so nothing is run: ${tail(name, 80)}`);
    const mine = { repo: job.repo, session: null };
    alone.set(name, mine);
    try {
      // Noted before anything is started in it. A codespace that cannot be noted is not used.
      note(name, job.repo);
      const token = randomBytes(24).toString('base64url');
      await settled(name, say);
      log(`${job.repo}: the codespace ${name} runs the code without a sandbox (--no-sandbox), and is deleted after the run`);
      const close = () => {
        if (mine.session) stopChild(mine.session.tunnel);
        mine.session = null;
      };
      await runThere(job, outcomes, {
        // The same codespace each time the connection has to be made again, by its identifier.
        async open() {
          if (mine.session && mine.session.tunnel.exitCode === null && mine.session.tunnel.signalCode === null) return mine.session;
          close();
          say(`Setting up Lean in the codespace ${name}`);
          const status = await boot(name, job.repo, token, say);
          const { port, tunnel } = await forward(name, token);
          mine.session = { name, token, port, tunnel, sandbox: status.sandbox };
          // (The helper stopped while the connection was being made: `shutdown` has deleted the codespace.)
          if (!alone.has(name)) { stopChild(tunnel); throw new Error('The helper is stopping'); }
          return mine.session;
        },
        close,
      });
    } finally {
      if (alone.has(name)) await discard(name, job.repo, 'its run without a sandbox is over');
    }
  }

  /**
   * Run a job in a codespace: what the helper does itself when Lean is here.
   * `store(file, data)` and `fail(file, error)` take each file's outcome.
   */
  function runJob(job, outcomes) {
    if (!sandbox) return runAlone(job, outcomes);
    const say = (message) => job.say(message);
    return runThere(job, outcomes, { open: () => ensure(job.repo, say), close: () => drop(job.repo) });
  }

  /** The run itself, over a connection that `link.open()` makes (again) and `link.close()` ends. */
  async function runThere(job, { store, fail }, link) {
    const say = (message) => job.say(message);
    let session = await link.open();
    // When a request fails, the connection went (this machine slept, its network changed) or the
    // codespace stopped. It is made again, a few times over: a network takes a moment to come
    // back. The helper there is left running if it still is, and the run with it.
    const send = async (method, pathname, body) => {
      let failure = null;
      for (let attempt = 0; attempt < 4; attempt++) {
        try {
          return await call(session, method, pathname, body);
        } catch (error) {
          failure = error;
        }
        link.close();
        if (attempt) await sleep(retryMs * attempt);
        try { session = await link.open(); } catch (error) { failure = error; }
      }
      throw failure;
    };
    const order = { repo: job.repo, sha: job.sha, pr: job.pr, paths: job.paths };
    let answer = await send('POST', '/run', order);
    if (answer.status === 403) {
      await send('POST', '/allow', { repo: job.repo });
      answer = await send('POST', '/run', order);
    }
    if (answer.status !== 200 || !answer.json) throw new Error(`The helper in the codespace refused the run: ${(answer.json && answer.json.error) || `HTTP ${answer.status}`}`);
    let status = answer.json;
    let last = null;
    let touched = Date.now();
    while (status.state === 'pending') {
      if (Date.now() - touched >= keepAliveMs) {
        // (See KEEP_ALIVE_MS: without this GitHub would stop the codespace under a long run.)
        touched = Date.now();
        run(gh, ['codespace', 'ssh', '-c', session.name, '--', 'true'], { timeoutMs: 60 * 1000 });
      }
      if (status.message && status.message !== last && status.phase !== 'queued') { last = status.message; say(status.message); }
      job.phase = status.phase === 'queued' ? 'preparing' : (status.phase || job.phase);
      job.detail = status.detail;
      job.done = Math.min(Number(status.done) || 0, job.paths.length);
      await sleep(pollMs);
      status = (await send('GET', `/job?repo=${encodeURIComponent(job.repo)}&sha=${job.sha}`)).json || { state: 'error', error: 'The helper in the codespace gave no status' };
    }
    for (const note of status.notes || []) job.note(note);
    // The results come here, where they stay when the codespace stops.
    let stored = 0;
    for (const file of job.paths) {
      const result = (await send('POST', '/file', { repo: job.repo, sha: job.sha, path: file })).json || {};
      if (result.state === 'ready' && result.data) { store(file, result.data); stored += 1; } else fail(file, result.error || status.error || 'Lean gave no result for this file');
    }
    job.done = job.paths.length;
    if (status.state === 'error' && !stored) throw new Error(status.error || 'The run failed in the codespace');
  }

  /** Stop a repository's codespace, after its helper has removed what it kept. */
  async function rest(repo, why) {
    const session = sessions.get(repo);
    if (!session || keep) return;
    drop(repo);
    log(`Stopping the codespace for ${repo} (${why}). It starts again with the next run.`);
    await run(gh, ['codespace', 'ssh', '-c', session.name, '--', STOP_COMMAND], { timeoutMs: 60 * 1000 });
    await run(gh, ['codespace', 'stop', '-c', session.name], { timeoutMs: 3 * 60 * 1000 });
  }

  /** When the helper stops: close the connections, and stop the codespaces it was using. */
  function shutdown() {
    running.delete(instance);
    for (const [repo, session] of [...sessions]) {
      drop(repo);
      if (keep) continue;
      log(`Stopping the codespace for ${repo}`);
      spawnSync(gh, ['codespace', 'ssh', '-c', session.name, '--', STOP_COMMAND], { stdio: 'ignore', timeout: 45 * 1000 });
      spawnSync(gh, ['codespace', 'stop', '-c', session.name], { stdio: 'ignore', timeout: 90 * 1000 });
    }
    // A codespace made for a run without a sandbox is deleted, whatever `keep` says. If that
    // fails, its note stays, and the next start deletes it (`tidy`).
    for (const [name, mine] of [...alone]) {
      if (mine.session) stopChild(mine.session.tunnel);
      alone.delete(name);
      log(`Deleting the codespace ${name} for ${mine.repo}: its run was without a sandbox`);
      const deleted = spawnSync(gh, ['codespace', 'delete', '-c', name, '--force'], { stdio: 'ignore', timeout: 90 * 1000 });
      if (deleted.status === 0) forgetNote(name);
    }
  }

  /** Stop one of this helper's codespaces by name. */
  const stop = (name) => must(['codespace', 'stop', '-c', name], { timeoutMs: 3 * 60 * 1000 });
  /** Delete one of this helper's codespaces by name, and forget it. */
  async function remove(name) {
    await must(['codespace', 'delete', '-c', name, '--force'], { timeoutMs: 3 * 60 * 1000 });
    for (const [repo, known] of Object.entries(config.codespaces)) if (known.name === name) delete config.codespaces[repo];
    config.retired = config.retired.filter((old) => old && old.name !== name);
    save();
    forgetNote(name);
  }

  return { check, runJob, rest, shutdown, ours, stop, remove, tidy, run };
}
