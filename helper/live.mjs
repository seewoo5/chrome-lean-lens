// Lean's language server, kept running on a commit for the extension's infoview.
//
// The infoview (the panel of goals and messages that editors show beside a Lean file) talks to
// a running Lean server: it asks for the goals at the cursor, and Lean answers as it elaborates.
// So for a commit the reader has started Lean on, the helper runs `lake serve` in the commit's
// copy, opens there the files the reader clicks in, and passes messages both ways. A session is
// that server with its open files. The extension sends it messages with `/live/send` and reads
// what Lean says with `/live/poll`, which waits until there is something to read.
//
// The server runs the project's code, like any run of Lean here: in the sandbox, on a
// repository the reader has allowed, and never before the reader asked for it. The files it
// opens are the commit's own, read from the copy: the page cannot hand it other text.

import { randomBytes } from 'node:crypto';
import { lstatSync, readFileSync, realpathSync } from 'node:fs';
import path from 'node:path';
import { pathToFileURL } from 'node:url';

export const LIVE_VERSION = 1;
// Files a session keeps open at once. Each has a Lean process of its own, with its imports in
// memory (some gigabytes for a Mathlib file): the one opened longest ago is closed for a new one.
const MAX_OPEN = 4;
// How long `/live/poll` waits for something to say.
const POLL_MAX_MS = 25 * 1000;
// A session nobody reads any more (the page was closed) ends after this long.
const GONE_MS = 3 * 60 * 1000;
// What Lean said and the page has not read yet. More than this and the page has stopped reading.
const UNREAD_MAX_BYTES = 96 * 1024 * 1024;
// What one answer to `/live/poll` carries at most.
const ANSWER_MAX_BYTES = 4 * 1024 * 1024;
const START_TIMEOUT_MS = 10 * 60 * 1000;

// What the page may not send: the server's life and its documents are the helper's to manage.
const HELPERS_OWN = new Set(['initialize', 'initialized', 'shutdown', 'exit', 'textDocument/didOpen', 'textDocument/didChange',
  'textDocument/didClose', 'textDocument/didSave', 'workspace/didChangeWatchedFiles', 'workspace/didChangeConfiguration']);

const tail = (text, n = 600) => (text.length > n ? `…${text.slice(-n)}` : text).trim();

/**
 * Splits a language server's output into its messages. Returns what to call with each chunk
 * read; `onMessage(text)` gets each message's JSON text.
 */
export function lspReader(onMessage) {
  let buffer = Buffer.alloc(0);
  return (chunk) => {
    buffer = buffer.length ? Buffer.concat([buffer, chunk]) : chunk;
    for (;;) {
      const head = buffer.indexOf('\r\n\r\n');
      if (head === -1) return;
      const length = /content-length:\s*(\d+)/i.exec(buffer.toString('latin1', 0, head));
      if (!length) { buffer = buffer.subarray(head + 4); continue; }
      const end = head + 4 + Number(length[1]);
      if (buffer.length < end) return;
      onMessage(buffer.toString('utf8', head + 4, end));
      buffer = buffer.subarray(end);
    }
  };
}

/** A message as a language server reads it. */
export function lspFrame(message) {
  const body = Buffer.from(typeof message === 'string' ? message : JSON.stringify(message), 'utf8');
  return Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`, 'latin1'), body]);
}

/**
 * @param {object} deps What the helper does for a session, each for a `job` (`{repo, sha, pr}`
 *   with `say`, `progress` and `note`, as a run has):
 *   `begin(job)`: the repository is in use. `checkout(job)`: its copy is at the commit
 *   (sets `job.dir`). `project(job, rootDir)`: the Lake project in that folder of the copy is
 *   ready to run: `{root, rootDir, …}`. `serve(job, project)`: `lake serve` started there, as a
 *   child process with pipes. `stop(child)`. `lakeRootFor(dir, file)`. `finish(job)`: the
 *   session is over.
 *   `quietMs`: a session nothing was asked of for this long ends (0: never).
 * @returns `{open, poll, send, close, release, shutdown, sessions}`
 */
export function createLive({ deps, log = () => {}, quietMs = 0, goneMs = GONE_MS, maxOpen = MAX_OPEN, pollMaxMs = POLL_MAX_MS, tickMs = 5000 }) {
  const sessions = new Map(); // repo → its session (one server for each repository: one copy)
  const byId = new Map();
  const gone = new Map(); // id → how a session that is over ended, for the page that still asks

  const describe = (session) => ({
    session: session.id, state: session.state, phase: session.phase, message: session.message, detail: session.detail,
    error: session.error || undefined, rev: session.rev,
  });

  /** Let those waiting in `/live/poll` answer (a moment later: what arrives together goes together). */
  function wake(session) {
    if (session.waking) return;
    session.waking = setImmediate(() => {
      session.waking = null;
      for (const answer of [...session.waiters]) answer();
    });
  }

  /** The session's state changed in a way the page shows. */
  function bump(session) {
    session.rev += 1;
    wake(session);
  }

  /** Something for the page to read: `fields` is the inside of a JSON object (`"t":"lsp",…`). */
  function emit(session, fields) {
    const text = `{"seq":${session.seq += 1},${fields}}`;
    session.events.push({ seq: session.seq, text });
    session.unread += text.length;
    if (session.unread > UNREAD_MAX_BYTES) { end(session, 'error', 'The page stopped reading what Lean says'); return; }
    wake(session);
  }
  const emitObject = (session, object) => emit(session, JSON.stringify(object).slice(1, -1));

  // --- The server ----------------------------------------------------------------------------

  const write = (server, message) => { if (!server.stopped) server.child.stdin.write(lspFrame(message)); };
  const notify = (server, method, params) => write(server, { jsonrpc: '2.0', method, params });
  /** A request of the helper's own (the page's requests are passed on as they are). */
  function request(server, method, params, timeoutMs = START_TIMEOUT_MS) {
    return new Promise((resolve, reject) => {
      const id = `h:${server.next += 1}`;
      const timer = setTimeout(() => { server.pending.delete(id); reject(new Error(`Lean's server did not answer \`${method}\``)); }, timeoutMs);
      server.pending.set(id, { resolve: (value) => { clearTimeout(timer); resolve(value); }, reject: (error) => { clearTimeout(timer); reject(error); } });
      write(server, { jsonrpc: '2.0', id, method, params });
    });
  }

  function fromServer(session, server, text) {
    let message = null;
    try { message = JSON.parse(text); } catch { return; }
    if (!message || typeof message !== 'object') return;
    const hasId = message.id !== undefined && message.id !== null;
    if (hasId && typeof message.method === 'string') {
      // The server asks something of its client (to register for file changes, to apply an
      // edit): there is no editor here, and it gets an empty answer.
      write(server, { jsonrpc: '2.0', id: message.id, result: null });
      return;
    }
    if (hasId && typeof message.id === 'string' && message.id.startsWith('h:')) {
      const waiting = server.pending.get(message.id);
      server.pending.delete(message.id);
      if (!waiting) return;
      if (message.error) waiting.reject(new Error(message.error.message || 'Lean refused the request'));
      else waiting.resolve(message.result);
      return;
    }
    if (session.server === server) emit(session, `"t":"lsp","m":${text}`);
  }

  async function startServer(session, project) {
    const child = await deps.serve(session.job, project);
    const server = { child, root: project.root, rootDir: project.rootDir, docs: new Map(), pending: new Map(), next: 0, said: '', stopped: false };
    session.server = server;
    child.stdin.on('error', () => { /* it stopped reading: how it ends says why */ });
    child.stdout.on('data', lspReader((text) => fromServer(session, server, text)));
    child.stderr.on('data', (chunk) => { server.said = (server.said + chunk.toString('utf8')).slice(-4000); });
    const over = (why) => {
      if (server.over) return;
      server.over = true;
      for (const waiting of server.pending.values()) waiting.reject(new Error(why));
      server.pending.clear();
      if (server.stopped || session.server !== server) return;
      end(session, 'error', why);
    };
    child.on('error', (error) => over(`Lean's server could not be started: ${error.message}`));
    child.on('close', (code) => over(`Lean's server stopped${tail(server.said) ? `: ${tail(server.said)}` : ` (exit ${code})`}`));
    const rootUri = pathToFileURL(project.root).href;
    const result = await request(server, 'initialize', {
      processId: null,
      clientInfo: { name: 'Lean Lens', version: String(LIVE_VERSION) },
      rootUri,
      workspaceFolders: [{ uri: rootUri, name: path.basename(project.root) }],
      capabilities: {
        textDocument: { publishDiagnostics: { relatedInformation: true } },
        // As Lean's editor extensions say: diagnostics meant for the infoview only, and the
        // current way of writing references in its answers.
        lean: { silentDiagnosticSupport: true, rpcWireFormat: 'v1' },
      },
      initializationOptions: { editDelay: 0, hasWidgets: true },
    });
    notify(server, 'initialized', {});
    server.initialize = result;
    emitObject(session, { t: 'server', initialize: result });
    return server;
  }

  function stopServer(session, why) {
    const server = session.server;
    if (!server) return;
    session.server = null;
    server.stopped = true;
    for (const [file, doc] of server.docs) emitObject(session, { t: 'closed', path: file, uri: doc.uri });
    emitObject(session, { t: 'stopped', message: why });
    deps.stop(server.child);
  }

  // --- Files ---------------------------------------------------------------------------------

  /** The text of a file of the commit, read from the copy: a plain file inside it, or an error. */
  function sourceOf(session, file) {
    const dir = session.job.dir;
    const target = path.join(dir, file);
    let stat = null;
    try { stat = lstatSync(target); } catch { /* not there */ }
    if (!stat) throw new Error('This file does not exist at that commit');
    // (The copy is the project's to write in. A link there could lead to the reader's own
    // files, and the text read here goes to the project's code.)
    let real = null;
    try { real = realpathSync(target); } catch { /* a link to nowhere */ }
    if (!stat.isFile() || real !== target) throw new Error('This file is not a plain file of the repository');
    return readFileSync(target, 'utf8');
  }

  function closeFile(session, server, file) {
    const doc = server.docs.get(file);
    if (!doc) return;
    server.docs.delete(file);
    notify(server, 'textDocument/didClose', { textDocument: { uri: doc.uri } });
    emitObject(session, { t: 'closed', path: file, uri: doc.uri });
  }

  /** Have a file of the commit open in the session's server (starting what that takes). */
  async function openFile(session, file, restart) {
    if (session.ended) return;
    try {
      if (!session.job.dir) {
        await deps.checkout(session.job);
        if (session.ended) return;
      }
      const text = sourceOf(session, file);
      const rootDir = deps.lakeRootFor(session.job.dir, file);
      if (rootDir === null) throw new Error('This file is not inside a Lake project');
      // One server, in one Lake project. A file of another project of the repository moves it there.
      if (session.server && session.server.rootDir !== rootDir) stopServer(session, 'Lean moved to another project of this repository');
      if (!session.server) {
        session.state = 'preparing';
        session.phase = 'preparing';
        bump(session);
        const project = await deps.project(session.job, rootDir);
        if (session.ended) return;
        session.job.say("Starting Lean's server");
        await startServer(session, project);
        if (session.ended) return;
        session.state = 'ready';
        session.phase = 'ready';
        session.job.say('Lean is running');
      }
      const server = session.server;
      const uri = pathToFileURL(path.join(session.job.dir, file)).href;
      if (server.docs.has(file) && restart) closeFile(session, server, file);
      if (server.docs.has(file)) {
        server.docs.delete(file); // (asked for again: the most recently used)
        server.docs.set(file, { uri });
      } else {
        server.docs.set(file, { uri });
        notify(server, 'textDocument/didOpen', { textDocument: { uri, languageId: 'lean4', version: 1, text }, dependencyBuildMode: 'always' });
        for (const oldest of [...server.docs.keys()].slice(0, Math.max(0, server.docs.size - maxOpen))) closeFile(session, server, oldest);
      }
      // (`dir`: the copy's own address, so the page can tell which files are the repository's.)
      emitObject(session, { t: 'opened', path: file, uri, dir: pathToFileURL(`${session.job.dir}${path.sep}`).href });
    } catch (error) {
      if (session.ended) return;
      // Without a server there is no session; with one, only this file has failed.
      if (!session.server) { end(session, 'error', error.message); return; }
      emitObject(session, { t: 'failed', path: file, error: error.message });
    }
  }

  // --- Sessions ------------------------------------------------------------------------------

  function end(session, state, why) {
    if (session.ended) return;
    session.ended = true;
    stopServer(session, why || 'Lean was stopped');
    session.state = state;
    session.phase = state;
    session.error = why || undefined;
    session.rev += 1;
    if (sessions.get(session.repo) === session) sessions.delete(session.repo);
    byId.delete(session.id);
    gone.set(session.id, session);
    for (const id of [...gone.keys()].slice(0, Math.max(0, gone.size - 20))) gone.delete(id);
    log(`${session.repo}@${session.sha.slice(0, 7)}: Lean's server ${state === 'error' ? `failed: ${why}` : `was stopped${why ? ` (${why})` : ''}`}`);
    wake(session);
    Promise.resolve().then(() => deps.finish(session.job)).catch(() => { /* its scratch files go at the next start */ });
  }

  /** Open a file of a commit, starting a session on that commit if there is none. */
  function open({ repo, sha, pr = null, path: file, restart = false }) {
    let session = sessions.get(repo);
    if (session && session.sha !== sha) {
      end(session, 'closed', 'Lean was started on another commit of this repository');
      session = null;
    }
    if (!session) {
      session = {
        id: randomBytes(12).toString('base64url'), repo, sha, pr,
        state: 'preparing', phase: 'queued', message: 'Waiting for the previous run', detail: undefined, error: undefined,
        rev: 0, seq: 0, events: [], unread: 0, waiters: new Set(), waking: null, server: null, ended: false,
        lastPoll: Date.now(), lastUse: Date.now(), queue: Promise.resolve(),
      };
      const current = session;
      session.job = {
        repo, sha, pr, dir: null,
        say(message) { current.message = message; current.detail = undefined; if (current.phase === 'queued') current.phase = 'preparing'; bump(current); log(`${repo}@${sha.slice(0, 7)}: ${message}`); },
        progress(line) { current.detail = line.slice(0, 200); bump(current); },
        note(message) { log(`${repo}@${sha.slice(0, 7)}: ${message}`); },
      };
      sessions.set(repo, session);
      byId.set(session.id, session);
      deps.begin(session.job);
    }
    const target = session;
    target.lastUse = Date.now();
    target.queue = target.queue.then(() => openFile(target, file, Boolean(restart)));
    return describe(target);
  }

  /**
   * What a session has to say since the page last read it: its state and the events after
   * number `after`. Waits up to `wait` milliseconds when there is nothing new (`rev` is the
   * state the page has seen). Resolves to JSON text.
   */
  function poll(id, { after = 0, rev = -1, wait = 0 } = {}) {
    const session = byId.get(id) || gone.get(id);
    if (!session) return Promise.resolve(JSON.stringify({ session: id, state: 'closed', events: [] }));
    session.lastPoll = Date.now();
    while (session.events.length && session.events[0].seq <= after) session.unread -= session.events.shift().text.length;
    const answer = () => {
      session.lastPoll = Date.now();
      const parts = [];
      let size = 0;
      for (const event of session.events) {
        if (parts.length && size + event.text.length > ANSWER_MAX_BYTES) break;
        parts.push(event.text);
        size += event.text.length;
      }
      return `${JSON.stringify(describe(session)).slice(0, -1)},"events":[${parts.join(',')}]}`;
    };
    const waits = Math.min(Number(wait) || 0, pollMaxMs);
    if (session.events.length || session.rev !== rev || session.ended || waits <= 0) return Promise.resolve(answer());
    return new Promise((resolve) => {
      const done = () => {
        clearTimeout(timer);
        session.waiters.delete(done);
        resolve(answer());
      };
      const timer = setTimeout(done, waits);
      session.waiters.add(done);
    });
  }

  /** Pass the page's messages on to Lean's server. */
  function send(id, messages) {
    const session = byId.get(id);
    if (!session) return { session: id, state: 'closed' };
    const server = session.server;
    if (!server || session.state !== 'ready') return { session: id, state: session.state, sent: 0 };
    let sent = 0;
    for (const message of Array.isArray(messages) ? messages : []) {
      if (!message || typeof message !== 'object' || typeof message.method !== 'string') continue;
      const hasId = message.id !== undefined && message.id !== null;
      // (An id is a number: the helper's own are text.)
      if (hasId && !Number.isSafeInteger(message.id)) continue;
      if (HELPERS_OWN.has(message.method)) {
        if (hasId) emitObject(session, { t: 'lsp', m: { jsonrpc: '2.0', id: message.id, error: { code: -32601, message: `\`${message.method}\` is not for the page to send` } } });
        continue;
      }
      if (message.method !== '$/lean/rpc/keepAlive') session.lastUse = Date.now();
      write(server, hasId
        ? { jsonrpc: '2.0', id: message.id, method: message.method, params: message.params }
        : { jsonrpc: '2.0', method: message.method, params: message.params });
      sent += 1;
    }
    return { session: id, state: session.state, sent };
  }

  function close(id) {
    const session = byId.get(id);
    if (session) end(session, 'closed', 'The infoview was closed');
    return { session: id, state: 'closed' };
  }

  /** Before the copy of a repository moves to another commit: the server on the old one stops. */
  function release(repo, sha) {
    const session = sessions.get(repo);
    if (session && session.sha !== sha) end(session, 'closed', 'Lean was run on another commit of this repository');
  }

  const ticker = setInterval(() => {
    const now = Date.now();
    for (const session of [...sessions.values()]) {
      if (now - session.lastPoll > goneMs && !session.waiters.size) end(session, 'closed', 'The page is no longer open');
      else if (quietMs > 0 && session.state === 'ready' && now - session.lastUse > quietMs) {
        const minutes = Math.round(quietMs / 60000);
        end(session, 'closed', `Lean was not used for ${minutes} minute${minutes === 1 ? '' : 's'}`);
      }
    }
  }, tickMs);
  ticker.unref();

  function shutdown() {
    clearInterval(ticker);
    for (const session of [...sessions.values()]) end(session, 'closed', 'The helper is stopping');
  }

  return { open, poll, send, close, release, shutdown, sessions };
}

/**
 * The same for a repository whose Lean runs in a codespace: the session is the helper's there,
 * and this one passes the requests on. Until the codespace answers (it may have to be made and
 * set up first), the session here says how that is going.
 *
 * @param {object} options `remote`: codespaces.mjs's (`request`, `notify`, `touch`);
 *   `begin(repo)` and `finish(repo)`: the repository is in use, and no longer.
 */
export function createLiveRelay({ remote, begin, finish, log = () => {}, pollMaxMs = POLL_MAX_MS, keepAliveMs = 8 * 60 * 1000 }) {
  const sessions = new Map(); // repo → session
  const byId = new Map();
  const ended = new Map(); // id → the last state of a session that is over

  const describe = (session) => ({
    session: session.id, state: session.state, phase: session.phase, message: session.message, detail: session.detail,
    error: session.error || undefined, rev: session.rev, events: [],
  });

  /** `there`: the session in the codespace is over already (it said so), and need not be told. */
  function end(session, state, why, there = false) {
    if (session.ended) return;
    session.ended = true;
    session.state = state;
    session.phase = state;
    session.error = why || undefined;
    session.rev += 1;
    clearInterval(session.keepAlive);
    if (sessions.get(session.repo) === session) sessions.delete(session.repo);
    byId.delete(session.id);
    ended.set(session.id, session);
    for (const id of [...ended.keys()].slice(0, Math.max(0, ended.size - 20))) ended.delete(id);
    for (const answer of [...session.waiters]) answer();
    // (Left unsaid when the codespace is not connected: the session there ends by itself.)
    if (session.remoteId && !there) remote.notify(session.repo, '/live/close', { repo: session.repo, sha: session.sha, session: session.remoteId });
    Promise.resolve().then(() => finish(session.repo)).catch(() => { /* nothing to undo */ });
  }

  /** A request to the helper in the codespace about this session. */
  async function ask(session, pathname, body, timeoutMs) {
    const order = { repo: session.repo, sha: session.sha, ...body };
    let answer = await remote.request(session.repo, session.say, 'POST', pathname, order, timeoutMs);
    if (answer.status === 403) {
      await remote.request(session.repo, session.say, 'POST', '/allow', { repo: session.repo });
      answer = await remote.request(session.repo, session.say, 'POST', pathname, order, timeoutMs);
    }
    if (answer.status === 404) throw new Error('The helper in the codespace is older than this one, and has no infoview');
    if (answer.status !== 200 || !answer.json) throw new Error(`The helper in the codespace refused: ${(answer.json && answer.json.error) || `HTTP ${answer.status}`}`);
    return answer.json;
  }

  function open({ repo, sha, pr = null, path: file, restart = false }) {
    let session = sessions.get(repo);
    if (session && session.sha !== sha) {
      end(session, 'closed', 'Lean was started on another commit of this repository');
      session = null;
    }
    if (!session) {
      session = {
        id: randomBytes(12).toString('base64url'), repo, sha, pr, remoteId: null,
        state: 'preparing', phase: 'preparing', message: 'Connecting to the codespace', detail: undefined, error: undefined,
        rev: 0, waiters: new Set(), ended: false, queue: Promise.resolve(),
      };
      const current = session;
      session.say = (message) => {
        current.message = message;
        current.rev += 1;
        log(`${repo}@${sha.slice(0, 7)}: ${message}`);
        for (const answer of [...current.waiters]) answer();
      };
      // (GitHub stops a codespace nobody has connected to for a while: see codespaces.mjs.)
      session.keepAlive = setInterval(() => remote.touch(repo), keepAliveMs);
      session.keepAlive.unref();
      sessions.set(repo, session);
      byId.set(session.id, session);
      begin(repo);
    }
    const target = session;
    target.queue = target.queue.then(async () => {
      if (target.ended) return;
      try {
        const answer = await ask(target, '/live/open', { pr, path: file, restart: Boolean(restart) }, 60 * 1000);
        if (target.ended) return;
        // (The session there may be a new one: the codespace was stopped and started meanwhile.)
        target.remoteId = answer.session;
        for (const waiting of [...target.waiters]) waiting();
      } catch (error) {
        end(target, 'error', error.message);
      }
    });
    return describe(target);
  }

  async function poll(id, { after = 0, rev = -1, wait = 0 } = {}) {
    const session = byId.get(id) || ended.get(id);
    if (!session) return { session: id, state: 'closed', events: [] };
    const waits = Math.min(Number(wait) || 0, pollMaxMs);
    if (!session.remoteId && !session.ended && session.rev === rev && waits > 0) {
      await new Promise((resolve) => {
        const done = () => { clearTimeout(timer); session.waiters.delete(done); resolve(); };
        const timer = setTimeout(done, waits);
        session.waiters.add(done);
      });
    }
    if (session.ended || !session.remoteId) return describe(session);
    try {
      const answer = await ask(session, '/live/poll', { session: session.remoteId, after, rev, wait: waits }, waits + 30 * 1000);
      if (answer.state === 'closed' || answer.state === 'error') end(session, answer.state, answer.error, true);
      return { ...answer, session: session.id };
    } catch (error) {
      end(session, 'error', error.message);
      return describe(session);
    }
  }

  async function send(id, messages) {
    const session = byId.get(id);
    if (!session) return { session: id, state: 'closed' };
    if (!session.remoteId) return { session: id, state: session.state, sent: 0 };
    try {
      return { ...(await ask(session, '/live/send', { session: session.remoteId, messages }, 60 * 1000)), session: id };
    } catch (error) {
      end(session, 'error', error.message);
      return { session: id, state: 'error', error: error.message };
    }
  }

  function close(id) {
    const session = byId.get(id);
    if (session) end(session, 'closed', 'The infoview was closed');
    return { session: id, state: 'closed' };
  }

  function shutdown() {
    for (const session of [...sessions.values()]) end(session, 'closed', 'The helper is stopping');
  }

  return { open, poll, send, close, shutdown, sessions };
}
