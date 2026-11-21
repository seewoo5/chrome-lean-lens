/**
 * The page around Lean's infoview, in the panel beside the code on GitHub.
 *
 * The infoview (frame.html) is written for an editor. This page is that editor: it keeps the
 * connection to Lean's server, which the local helper runs on the commit being read
 * (helper/live.mjs), passes the infoview's requests to it and Lean's answers back, and tells
 * the infoview where the cursor is when the reader clicks in the code (content/infoview_panel.js
 * says where).
 *
 * Lean runs a commit's code. So it starts here only from the Start button, which is in this
 * page: an extension's page, which the page on GitHub cannot click or script.
 */
(function (scope) {
  const POLL_WAIT_MS = 20000;
  const KEEP_ALIVE_MS = 10000;
  const CONFIG_KEY = 'lean_lens_infoview_config';
  // Notifications whose last one for each file is kept, for an infoview that asks after it came.
  const REPLAYED = new Set(['textDocument/publishDiagnostics', '$/lean/fileProgress']);

  const short = (sha) => String(sha || '').slice(0, 7);
  const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

  /** Where a file of the repository's copy is in the repository, from its address there; or null. */
  function pathInRepo(dir, uri) {
    if (typeof dir !== 'string' || typeof uri !== 'string' || !uri.startsWith(dir)) return null;
    try {
      const path = decodeURIComponent(uri.slice(dir.length));
      // (What Lake fetched or built there is not a file of the repository.)
      return !path || path.startsWith('.lake/') || path.split('/').includes('..') ? null : path;
    } catch (err) {
      return null;
    }
  }

  /**
   * The editor for one page.
   *
   * @param {object} env
   *   `request(path, body, timeoutMs)`: a request to the helper: its JSON answer, or `{state}`
   *     ('off', 'not_local', 'offline', 'unauthorized', 'not_allowed', 'old', 'error') when there is none.
   *   `frame`: `{create(onMessage), destroy(), post(message)}`: the infoview's frame.
   *   `panel(message)`: tell the page on GitHub something (`{type: 'reveal', …}`).
   *   `render(view)`: show the state. `loadConfig()`, `saveConfig(config)`: the infoview's settings.
   */
  class Editor {
    constructor(env) {
      this.env = env;
      this.page = null; // {repo, sha, pr, current}: what the page on GitHub shows
      this.cursor = null; // {repo, sha, pr, path, line, character}: the last click in the code
      this.session = null;
      this.ended = null; // why the last session is over
      this.refused = null; // what the helper said when it could not start
      this.notice = '';
      this.lspId = 0;
      this.installed = true; // whether the infoview's own files are there (`npm install` makes them)
    }

    setInstalled(installed) {
      this.installed = Boolean(installed);
      this.render();
    }

    // --- What the page on GitHub says ----------------------------------------------------------

    setPage(page) {
      this.page = page && page.repo && page.sha ? page : null;
      const session = this.session;
      if (session && (!this.page || this.page.repo !== session.repo || this.page.sha !== session.sha)) {
        this.stop('The page moved to another commit');
      }
      if (this.cursor && (!this.page || this.cursor.repo !== this.page.repo || this.cursor.sha !== this.page.sha)) this.cursor = null;
      this.render();
    }

    /** The reader clicked in the code: the infoview's cursor goes there, if Lean runs on that commit. */
    setCursor(cursor) {
      if (!cursor || !cursor.repo || !cursor.sha || !cursor.path) return;
      this.cursor = cursor;
      this.notice = '';
      const session = this.session;
      if (session && session.repo === cursor.repo && session.sha === cursor.sha) {
        if (session.docs.has(cursor.path)) this.sendLocation();
        else this.openFile(cursor.path);
      }
      this.render();
    }

    // --- Starting and stopping -----------------------------------------------------------------

    /** The file Lean would start on: where the reader clicked, else the file in view. */
    target() {
      const page = this.page;
      if (!page) return null;
      const cursor = this.cursor;
      const path = cursor && cursor.repo === page.repo && cursor.sha === page.sha ? cursor.path : page.current;
      return path ? { repo: page.repo, sha: page.sha, pr: page.pr, path } : null;
    }

    /** The Start button. `allow` when the reader has just agreed to allow the repository. */
    async start(allow = false) {
      const target = this.target();
      if (!target || this.session || this.starting || !this.installed) return;
      this.starting = true;
      this.ended = null;
      this.refused = null;
      this.render();
      try {
        if (allow) {
          const allowed = await this.env.request('/allow', { repo: target.repo });
          if (!allowed || !allowed.ok) { this.refused = allowed || { state: 'offline' }; return; }
        }
        await this.openFile(target.path, false, target);
      } finally {
        this.starting = false;
        this.render();
      }
    }

    /** Ask the helper to open a file in Lean's server (starting the server if it is not running). */
    async openFile(path, restart = false, target = null) {
      const of = target || this.session;
      if (!of) return;
      const answer = await this.env.request('/live/open', { repo: of.repo, sha: of.sha, pr: of.pr || undefined, path, restart: restart || undefined });
      if (!answer || !answer.session) {
        // Not started (or no longer there): say why. A running session's own end comes from its poll.
        if (!this.session) this.refused = answer || { state: 'offline' };
        else this.notice = `${path} could not be opened`;
        this.render();
        return;
      }
      if (this.session && this.session.id === answer.session) return;
      if (this.session) this.endSession(null);
      this.beginSession(of, answer);
    }

    beginSession(of, answer) {
      const session = {
        id: answer.session, repo: of.repo, sha: of.sha, pr: of.pr,
        state: answer.state, message: answer.message, detail: answer.detail, rev: -1, after: 0,
        docs: new Map(), // path → the file's address in Lean's server
        paths: new Map(), // and back
        dir: null, // the address of the repository's copy
        initialize: null, frameReady: false, announced: false, fallback: null,
        serverSubs: new Map(), clientSubs: new Map(),
        requests: new Map(), // id of a request to Lean → the infoview's call, or what to do with the answer
        rpc: new Map(), // RPC session → the timer that keeps it alive
        last: new Map(), // method → file → the last notification kept for replay
        outbox: [], sending: Promise.resolve(), flushing: false,
      };
      this.session = session;
      this.ended = null;
      this.refused = null;
      this.env.frame.create((message) => this.fromFrame(session, message), () => this.frameLoaded(session));
      this.pollLoop(session);
      this.render();
    }

    /** The Stop button, and a page that went elsewhere. */
    stop(why) {
      const session = this.session;
      if (!session) return;
      this.env.request('/live/close', { repo: session.repo, sha: session.sha, session: session.id });
      this.endSession(why || null);
    }

    endSession(why, failed = false) {
      const session = this.session;
      if (!session) return;
      this.session = null;
      for (const timer of session.rpc.values()) clearInterval(timer);
      session.rpc.clear();
      this.env.frame.destroy();
      this.ended = why ? { why, failed } : null;
      this.render();
    }

    async pollLoop(session) {
      let failures = 0;
      while (this.session === session) {
        const answer = await this.env.request('/live/poll',
          { repo: session.repo, sha: session.sha, session: session.id, after: session.after, rev: session.rev, wait: POLL_WAIT_MS }, POLL_WAIT_MS + 20000);
        if (this.session !== session) return;
        if (!answer || typeof answer.rev !== 'number') {
          // The helper did not answer: once is a hiccup, several times it is gone.
          failures += 1;
          const state = answer && answer.state;
          if (failures > 3 || state === 'unauthorized' || state === 'not_allowed' || state === 'closed') {
            this.endSession(state === 'closed' ? 'Lean was stopped' : 'The helper stopped answering', state !== 'closed');
            return;
          }
          await sleep(800 * failures);
          continue;
        }
        failures = 0;
        Object.assign(session, { rev: answer.rev, state: answer.state, message: answer.message, detail: answer.detail });
        for (const event of answer.events || []) {
          session.after = event.seq;
          try { this.onEvent(session, event); } catch (err) { console.warn('[Lean Lens] infoview event failed:', err); }
          if (this.session !== session) return;
        }
        if (answer.state === 'closed' || answer.state === 'error') {
          this.endSession(answer.error || 'Lean was stopped', answer.state === 'error');
          return;
        }
        this.render();
      }
    }

    // --- What the helper says ------------------------------------------------------------------

    onEvent(session, event) {
      if (event.t === 'lsp') { this.fromServer(session, event.m); return; }
      if (event.t === 'server') {
        session.initialize = event.initialize;
        if (session.announced) this.toFrame(session, 'serverRestarted', [event.initialize]);
        else this.announce(session);
      } else if (event.t === 'opened') {
        session.docs.set(event.path, event.uri);
        session.paths.set(event.uri, event.path);
        if (event.dir) session.dir = event.dir;
        // Until the reader clicks somewhere, the infoview looks at the top of the first file.
        if (!session.fallback) session.fallback = { path: event.path, line: 0, character: 0 };
        this.sendLocation();
      } else if (event.t === 'closed') {
        session.docs.delete(event.path);
        session.paths.delete(event.uri);
        for (const kept of session.last.values()) kept.delete(event.uri);
        if (session.fallback && session.fallback.path === event.path) session.fallback = null;
        if (session.clientSubs.get('textDocument/didClose')) {
          this.toFrame(session, 'sentClientNotification', ['textDocument/didClose', { textDocument: { uri: event.uri } }]);
        }
      } else if (event.t === 'failed') {
        this.notice = `${event.path}: ${event.error}`;
      } else if (event.t === 'stopped') {
        for (const timer of session.rpc.values()) clearInterval(timer);
        session.rpc.clear();
        if (session.announced) this.toFrame(session, 'serverStopped', [{ message: event.message || 'Lean was stopped', reason: '' }]);
      }
    }

    fromServer(session, message) {
      if (!message || typeof message !== 'object') return;
      if (message.id !== undefined && message.id !== null && message.method === undefined) {
        const waiting = session.requests.get(message.id);
        session.requests.delete(message.id);
        if (!waiting) return;
        if (typeof waiting === 'function') waiting(message);
        else if (message.error) this.env.frame.post({ result: waiting.call, error: message.error });
        else this.env.frame.post({ result: waiting.call, value: message.result });
        return;
      }
      if (typeof message.method !== 'string') return;
      const uri = message.params && (message.params.uri || (message.params.textDocument && message.params.textDocument.uri));
      if (REPLAYED.has(message.method) && uri) {
        if (!session.last.has(message.method)) session.last.set(message.method, new Map());
        session.last.get(message.method).set(uri, message.params);
      }
      if (session.announced && session.serverSubs.get(message.method)) {
        this.toFrame(session, 'gotServerNotification', [message.method, message.params]);
      }
    }

    // --- What the infoview is told -------------------------------------------------------------

    toFrame(session, api, args) {
      if (this.session === session && session.frameReady) this.env.frame.post({ api, args });
    }

    /** Where the infoview's cursor is: `{uri, range}` for the last click if its file is open, else the fallback. */
    location(session) {
      const cursor = this.cursor && this.cursor.repo === session.repo && this.cursor.sha === session.sha ? this.cursor : null;
      const at = cursor && session.docs.has(cursor.path) ? cursor : session.fallback;
      if (!at || !session.docs.has(at.path)) return null;
      const position = { line: at.line, character: at.character };
      return { uri: session.docs.get(at.path), range: { start: position, end: position } };
    }

    /**
     * The infoview's first words from its editor, once all three are there: the frame, Lean's
     * server and a place to look at. In the order editors use: the place, then the server.
     */
    announce(session) {
      if (session.announced || !session.frameReady || !session.initialize) return;
      const loc = this.location(session);
      if (!loc) return;
      session.announced = true;
      this.toFrame(session, 'initialize', [loc]);
      this.toFrame(session, 'serverRestarted', [session.initialize]);
      this.render();
    }

    sendLocation() {
      const session = this.session;
      if (!session) return;
      if (!session.announced) { this.announce(session); return; }
      const loc = this.location(session);
      if (loc) this.toFrame(session, 'changedCursorLocation', [loc]);
    }

    async frameLoaded(session) {
      if (this.session !== session) return;
      session.frameReady = true;
      const config = await this.env.loadConfig();
      if (this.session !== session) return;
      if (config) this.toFrame(session, 'changedInfoviewConfig', [config]);
      this.announce(session);
    }

    // --- What the infoview asks for ------------------------------------------------------------

    /** Queue a message for Lean's server. Those queued together go together, in order. */
    toServer(session, message) {
      session.outbox.push(message);
      if (session.flushing) return;
      session.flushing = true;
      session.sending = session.sending.then(async () => {
        session.flushing = false;
        const messages = session.outbox.splice(0);
        if (!messages.length || this.session !== session) return;
        const answer = await this.env.request('/live/send', { repo: session.repo, sha: session.sha, session: session.id, messages }, 30000);
        if (answer && answer.sent === messages.length) return;
        // Not delivered (Lean is not running there): the requests among them fail.
        for (const message of messages) {
          if (message.id !== undefined) this.fromServer(session, { id: message.id, error: { code: -32002, message: 'Lean is not running' } });
        }
      });
    }

    /** A request of this page's own to Lean's server. Resolves to the answer message. */
    ask(session, method, params) {
      return new Promise((resolve) => {
        const id = this.lspId += 1;
        session.requests.set(id, resolve);
        this.toServer(session, { id, method, params });
      });
    }

    fromFrame(session, message) {
      if (this.session !== session || !message || typeof message !== 'object') return;
      if (typeof message.cancel === 'number') {
        for (const [id, waiting] of session.requests) {
          if (waiting && waiting.call === message.cancel) this.toServer(session, { method: '$/cancelRequest', params: { id } });
        }
        return;
      }
      if (typeof message.call !== 'number' || typeof message.method !== 'string') return;
      const args = Array.isArray(message.args) ? message.args : [];
      const reply = (value) => this.env.frame.post({ result: message.call, value });
      const fail = (text) => this.env.frame.post({ result: message.call, error: { code: -32603, message: text } });
      const count = (subs, by) => { subs.set(args[0], Math.max(0, (subs.get(args[0]) || 0) + by)); reply(); };
      switch (message.method) {
        case 'sendClientRequest': {
          if (typeof args[1] !== 'string') { fail('Not a request'); return; }
          const id = this.lspId += 1;
          session.requests.set(id, { call: message.call });
          this.toServer(session, { id, method: args[1], params: args[2] });
          return;
        }
        case 'sendClientNotification':
          if (typeof args[1] === 'string') this.toServer(session, { method: args[1], params: args[2] });
          reply();
          return;
        case 'subscribeServerNotifications': {
          count(session.serverSubs, 1);
          // What Lean said before the infoview asked: the last for each file.
          const kept = session.last.get(args[0]);
          if (kept && session.announced) for (const params of kept.values()) this.toFrame(session, 'gotServerNotification', [args[0], params]);
          return;
        }
        case 'unsubscribeServerNotifications': count(session.serverSubs, -1); return;
        case 'subscribeClientNotifications': count(session.clientSubs, 1); return;
        case 'unsubscribeClientNotifications': count(session.clientSubs, -1); return;
        case 'createRpcSession': {
          const uri = args[0];
          this.ask(session, '$/lean/rpc/connect', { uri }).then((answer) => {
            if (this.session !== session) return;
            const id = answer.result && answer.result.sessionId;
            if (answer.error || typeof id !== 'string') { this.env.frame.post({ result: message.call, error: answer.error || { code: -32603, message: 'Lean gave no RPC session' } }); return; }
            // Lean drops a session it hears nothing of: the editor keeps it alive.
            session.rpc.set(id, setInterval(() => this.toServer(session, { method: '$/lean/rpc/keepAlive', params: { uri, sessionId: id } }), KEEP_ALIVE_MS));
            reply(id);
          });
          return;
        }
        case 'closeRpcSession':
          clearInterval(session.rpc.get(args[0]));
          session.rpc.delete(args[0]);
          reply();
          return;
        case 'showDocument': {
          const show = args[0] || {};
          const path = pathInRepo(session.dir, show.uri);
          const start = show.selection && show.selection.start;
          if (path) {
            this.env.panel({ type: 'reveal', repo: session.repo, sha: session.sha, pr: session.pr, path, line: (start ? start.line : 0) + 1, character: start ? start.character : 0 });
          } else {
            this.notice = 'That place is outside this repository (in Lean or a dependency).';
            this.render();
          }
          reply();
          return;
        }
        case 'restartFile': {
          const path = session.paths.get(args[0]);
          if (path) this.openFile(path, true);
          reply();
          return;
        }
        case 'saveConfig':
          this.env.saveConfig(args[0]);
          reply();
          return;
        case 'copied':
          this.notice = args[0] ? 'Copied to the clipboard: the page on GitHub cannot be edited.' : 'The page on GitHub cannot be edited.';
          this.render();
          reply();
          return;
        default:
          fail(`The editor has no \`${message.method}\``);
      }
    }

    // --- What is shown -------------------------------------------------------------------------

    /** The state as the page shows it: `{dot, status, intro, detail, button, stop, frame, notice}`. */
    view() {
      const session = this.session;
      const view = { dot: 'off', status: 'Lean is not running', intro: '', detail: '', button: null, stop: false, frame: false, notice: this.notice };
      if (!this.installed) {
        return Object.assign(view, {
          dot: 'error', status: 'The infoview is not installed',
          intro: 'This copy of Lean Lens has no infoview yet.',
          detail: 'Run `npm install` in the extension’s folder (it fetches @leanprover/infoview from NPM), then reload the extension and this page.',
        });
      }
      if (session) {
        if (session.state === 'ready' && session.announced) {
          return Object.assign(view, { dot: 'ready', stop: true, frame: true, status: `Lean is running on ${session.repo}@${short(session.sha)}` });
        }
        return Object.assign(view, {
          dot: 'busy', stop: true, status: `Starting Lean on ${session.repo}@${short(session.sha)}`,
          intro: session.message || 'Starting Lean', detail: session.detail || '',
        });
      }
      if (this.starting) return Object.assign(view, { dot: 'busy', status: 'Asking the helper', intro: 'Asking the helper…' });
      const refused = this.refused;
      const target = this.target();
      if (refused && refused.state === 'not_allowed' && target) {
        return Object.assign(view, {
          intro: `The helper has not been allowed to run ${target.repo} yet.`,
          detail: 'Allowing a repository allows every pull request to it, from forks too: what runs is the code of the pull request’s author.',
          button: { label: `Allow ${target.repo} and start Lean`, allow: true },
        });
      }
      if (refused) {
        const said = {
          off: 'The helper is switched off. Switch on “Use the local helper” in Lean Lens’s options, and paste the helper’s address and token there.',
          not_local: 'The helper runs on this machine: its address in Lean Lens’s options starts with http://127.0.0.1 or http://localhost.',
          offline: 'The helper is not running. Start it with `node helper/lean-lens-helper.mjs`.',
          unauthorized: 'The helper did not accept the token. Paste the one it printed into Lean Lens’s options.',
          old: 'This helper is older than the extension and has no infoview. Stop it, and start the one in the extension’s folder.',
        }[refused.state] || refused.error || 'The helper could not start Lean.';
        return Object.assign(view, { dot: 'error', status: 'Lean could not be started', intro: said, button: target ? { label: 'Try again', allow: false } : null });
      }
      if (!target) {
        return Object.assign(view, { intro: 'Click in the Lean code of a pull request to choose where the infoview looks.' });
      }
      const ended = this.ended;
      return Object.assign(view, {
        dot: ended && ended.failed ? 'error' : 'off',
        status: ended ? (ended.failed ? 'Lean stopped' : 'Lean was stopped') : 'Lean is not running',
        intro: ended ? ended.why : `Start Lean on ${target.repo} at commit ${short(target.sha)} to see its goals and messages here.`,
        detail: `Lean will open ${target.path}. It runs that commit’s code, as “Run Lean” does. Once it runs, click in the code to move the infoview’s cursor.`,
        button: { label: ended ? 'Start Lean again' : 'Start Lean', allow: false },
      });
    }

    render() {
      this.env.render(this.view());
    }
  }

  scope.LeanLensInfoviewHost = { Editor, pathInRepo };

  // ---------------------------------------------------------------------------------------------
  // In the panel: the page's elements, the helper, the frame, and the page on GitHub.

  if (typeof document === 'undefined' || typeof chrome === 'undefined' || !chrome.runtime || !document.getElementById('frame-holder')) return;

  const $ = (id) => document.getElementById(id);
  let panelPort = null;
  let theme = 'light';

  const sendMessage = (message) => new Promise((resolve) => {
    try {
      chrome.runtime.sendMessage(message, (res) => resolve(chrome.runtime.lastError ? null : res));
    } catch (err) {
      resolve(null);
    }
  });

  // The helper's address and token, from the extension's settings (asked for again after a moment,
  // so a change in the options is taken up).
  let settings = null;
  let settingsAt = 0;
  async function helperSettings() {
    if (!settings || Date.now() - settingsAt > 3000) {
      const res = await sendMessage({ action: 'GET_SETTINGS' });
      settings = (res && res.settings) || {};
      settingsAt = Date.now();
    }
    return settings;
  }

  /**
   * One request to the helper: its JSON answer, or `{state}` when it gave none.
   *
   * This page is a frame in a tab of github.com, and what it asks of this machine may be stopped
   * for that: Firefox's local network access check refuses it ("Local Network Access permission
   * required", for the top-level site), and content blockers have filters against web pages that
   * probe the local network. The background script's requests, which the hovers use, are not
   * subject to either. So in Firefox the background script makes all of them; elsewhere the
   * request is made from here, and by the background script if that gets no answer, and the way
   * that worked is kept to.
   */
  let direct = location.protocol === 'moz-extension:' ? false : null; // true: from here; false: by the background script
  async function request(path, body, timeoutMs = 8000) {
    const s = await helperSettings();
    if (!s.enableHelper || !s.helperUrl || !s.helperToken) return { state: 'off' };
    // (As in the background script: the token goes only to an address on this machine.)
    let local = false;
    try { const at = new URL(s.helperUrl); local = at.protocol === 'http:' && (at.hostname === '127.0.0.1' || at.hostname === 'localhost'); } catch (err) { /* no address */ }
    if (!local) return { state: 'not_local' };
    if (direct !== false) {
      try {
        const response = await fetch(new URL(path, s.helperUrl).toString(), {
          method: 'POST',
          headers: { 'X-Lean-Lens-Token': s.helperToken, 'Content-Type': 'application/json' },
          body: JSON.stringify(body),
          signal: AbortSignal.timeout(timeoutMs),
          keepalive: path === '/live/close'
        });
        direct = true;
        if (response.status === 401) return { state: 'unauthorized' };
        const json = await response.json().catch(() => null);
        if (response.status === 403) return { state: 'not_allowed', repo: json && json.repo };
        if (response.status === 404) return { state: 'old' };
        if (!response.ok || !json) return { state: 'error', error: (json && json.error) || `The helper answered ${response.status}` };
        return json;
      } catch (err) {
        if (direct) return { state: 'offline' };
      }
    }
    const answer = await sendMessage({ action: 'HELPER_LIVE', path, body, timeout: timeoutMs });
    if (!answer || answer.state === 'offline') return { state: 'offline' };
    direct = false;
    return answer;
  }

  // The infoview's frame. It gets one end of a message channel once it has loaded. In Chrome
  // the manifest makes frame.html a sandboxed page, which can reach nothing else: so a file's
  // widgets (code that comes with the Lean file) can run there. Firefox has no such pages, and
  // does not load an extension's page into a frame sandboxed here: there the frame is a page
  // like this one, whose rules let in no code but the extension's own, so widgets do not run.
  const frame = {
    el: null, port: null, listener: null,
    create(onMessage, onReady) {
      this.destroy();
      const el = document.createElement('iframe');
      el.setAttribute('allow', 'clipboard-write');
      el.title = 'Lean infoview';
      this.listener = (event) => {
        if (event.source !== el.contentWindow || !event.data || event.data.leanLens !== 'infoview-loaded' || this.port) return;
        const channel = new MessageChannel();
        this.port = channel.port1;
        this.port.onmessage = (e) => {
          if (e.data && e.data.ready) onReady();
          else onMessage(e.data);
        };
        el.contentWindow.postMessage({ leanLens: 'infoview-port', theme }, '*', [channel.port2]);
      };
      window.addEventListener('message', this.listener);
      el.src = 'frame.html';
      this.el = el;
      $('frame-holder').appendChild(el);
    },
    destroy() {
      if (this.listener) window.removeEventListener('message', this.listener);
      if (this.port) this.port.close();
      if (this.el) this.el.remove();
      this.el = null;
      this.port = null;
      this.listener = null;
    },
    post(message) {
      if (this.port) this.port.postMessage(message);
    }
  };

  let button = null;
  const editor = new Editor({
    request,
    frame,
    panel: (message) => { if (panelPort) panelPort.postMessage(message); },
    loadConfig: () => new Promise((resolve) => {
      try { chrome.storage.local.get([CONFIG_KEY], (res) => resolve((res && res[CONFIG_KEY]) || null)); } catch (err) { resolve(null); }
    }),
    saveConfig: (config) => { try { chrome.storage.local.set({ [CONFIG_KEY]: config }); } catch (err) { /* kept for this page only */ } },
    render(view) {
      $('dot').className = view.dot;
      $('status').textContent = view.status;
      $('status').title = view.status;
      $('stop').hidden = !view.stop;
      $('notice').hidden = !view.notice;
      $('notice').textContent = view.notice || '';
      $('intro').hidden = view.frame;
      $('intro-text').textContent = view.intro;
      $('intro-detail').textContent = view.detail;
      $('start').hidden = !view.button;
      $('start').textContent = view.button ? view.button.label : '';
      button = view.button;
      $('frame-holder').hidden = !view.frame;
    }
  });

  // The infoview's files, which `npm install` puts in vendor/: without them there is nothing to show.
  fetch('vendor/version.json').then((response) => response.ok, () => false).then((there) => { if (!there) editor.setInstalled(false); });

  $('start').addEventListener('click', () => { if (button) editor.start(button.allow); });
  $('stop').addEventListener('click', () => editor.stop('You stopped Lean.'));
  // The page is going away: Lean's server need not wait to notice.
  window.addEventListener('pagehide', () => editor.stop());

  function setTheme(next) {
    theme = next === 'dark' ? 'dark' : 'light';
    document.body.classList.toggle('dark', theme === 'dark');
    document.body.classList.toggle('light', theme !== 'dark');
    frame.post({ theme });
  }

  editor.render();

  // The page on GitHub this panel is in. Its content script (content/infoview_panel.js) hands
  // over one end of a message channel, with the key the background gave it for this frame
  // (named in this page's address). The web page's own scripts can post here as well, but
  // they cannot ask the background for the key: without it, what they send is ignored.
  const key = sendMessage({ action: 'INFOVIEW_KEY', id: location.hash.slice(1) });
  window.addEventListener('message', async (event) => {
    const data = event.data;
    if (event.source !== window.parent || !data || data.leanLens !== 'infoview-panel' || !event.ports[0] || typeof data.key !== 'string') return;
    const answer = await key;
    if (!answer || !answer.key || data.key !== answer.key) return;
    if (panelPort) panelPort.close();
    panelPort = event.ports[0];
    panelPort.onmessage = (e) => {
      const message = e.data;
      if (!message || typeof message !== 'object') return;
      if (message.type === 'page') editor.setPage(message.page);
      else if (message.type === 'cursor') editor.setCursor(message.cursor);
      else if (message.type === 'theme') setTheme(message.theme);
    };
  });
})(typeof self !== 'undefined' ? self : globalThis);
