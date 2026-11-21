/**
 * The frame that shows Lean's infoview (@leanprover/infoview, in vendor/).
 *
 * The infoview is written for an editor: it asks the editor for what it needs (requests to
 * Lean's server, the clipboard, showing a place in a file) and the editor tells it what
 * happens (where the cursor is, what the server said). Here the editor is the page around this
 * frame (host.js), reached over a message channel it hands over when the frame has loaded.
 *
 * In Chrome this frame may run code that comes with the Lean file being read (its widgets). So
 * there it is a sandboxed page (see the manifest) and has nothing but that channel: no
 * extension APIs, no network, an origin of its own. Firefox has no such pages: there the rules
 * for an extension's pages let no such code in, and widgets do not load.
 */
import { renderInfoview } from './vendor/infoview.js';

let port = null;
let nextCall = 0;
const calls = new Map(); // number → {resolve, reject}

/** Ask the host to do one of the editor's jobs. `signal`, when given, withdraws the request. */
function call(method, args, signal) {
  return new Promise((resolve, reject) => {
    const n = nextCall += 1;
    calls.set(n, { resolve, reject });
    port.postMessage({ call: n, method, args });
    if (signal) signal.addEventListener('abort', () => port.postMessage({ cancel: n }), { once: true });
  });
}

/** Put text on the clipboard from here, where the click was. Returns whether it worked. */
async function copy(text) {
  try {
    await navigator.clipboard.writeText(text);
    return true;
  } catch (err) {
    // (No clipboard access in this frame: the old way, which a click allows.)
    const area = document.createElement('textarea');
    area.value = text;
    area.style.cssText = 'position:fixed;top:0;left:0;opacity:0';
    document.body.appendChild(area);
    area.select();
    let done = false;
    try { done = document.execCommand('copy'); } catch (e) { done = false; }
    area.remove();
    return done;
  }
}

const editorApi = {
  saveConfig: (config) => call('saveConfig', [config]),
  sendClientRequest: (uri, method, params, options) => call('sendClientRequest', [uri, method, params], options && options.abortSignal),
  sendClientNotification: (uri, method, params) => call('sendClientNotification', [uri, method, params]),
  subscribeServerNotifications: (method) => call('subscribeServerNotifications', [method]),
  unsubscribeServerNotifications: (method) => call('unsubscribeServerNotifications', [method]),
  subscribeClientNotifications: (method) => call('subscribeClientNotifications', [method]),
  unsubscribeClientNotifications: (method) => call('unsubscribeClientNotifications', [method]),
  copyToClipboard: async (text) => { await copy(String(text)); },
  // The page on GitHub cannot be edited: what would be inserted is copied instead, and the
  // host says so.
  insertText: async (text) => call('copied', [await copy(String(text))]),
  applyEdit: async (edit) => {
    const texts = [];
    const collect = (edits) => { for (const e of edits || []) if (e && typeof e.newText === 'string') texts.push(e.newText); };
    for (const edits of Object.values((edit && edit.changes) || {})) collect(edits);
    for (const change of (edit && edit.documentChanges) || []) collect(change && change.edits);
    return call('copied', [texts.length ? await copy(texts.join('\n')) : false]);
  },
  showDocument: (show) => call('showDocument', [show]),
  restartFile: (uri) => call('restartFile', [uri]),
  createRpcSession: (uri) => call('createRpcSession', [uri]),
  closeRpcSession: (sessionId) => call('closeRpcSession', [sessionId])
};

// What the host may tell the infoview (not `runTestScript`, which runs what it is given).
const FROM_EDITOR = new Set(['initialize', 'gotServerNotification', 'sentClientNotification', 'serverRestarted', 'serverStopped',
  'changedCursorLocation', 'changedInfoviewConfig', 'requestedAction']);

function setTheme(theme) {
  document.body.classList.toggle('vscode-dark', theme === 'dark');
  document.body.classList.toggle('vscode-light', theme !== 'dark');
}

function start() {
  const infoview = renderInfoview(editorApi, document.getElementById('infoview'));
  port.onmessage = (event) => {
    const message = event.data;
    if (!message || typeof message !== 'object') return;
    if (message.result !== undefined) {
      const waiting = calls.get(message.result);
      calls.delete(message.result);
      if (!waiting) return;
      if (Object.prototype.hasOwnProperty.call(message, 'error')) waiting.reject(message.error);
      else waiting.resolve(message.value);
    } else if (typeof message.api === 'string' && FROM_EDITOR.has(message.api)) {
      Promise.resolve(infoview[message.api](...(message.args || []))).catch((err) => console.error('[Lean Lens] infoview:', err));
    } else if (message.theme) {
      setTheme(message.theme);
    }
  };
  port.postMessage({ ready: true });
}

window.addEventListener('message', (event) => {
  if (port || event.source !== window.parent || !event.data || event.data.leanLens !== 'infoview-port' || !event.ports[0]) return;
  port = event.ports[0];
  setTheme(event.data.theme);
  start();
});
// The host waits for this before it hands over the channel.
window.parent.postMessage({ leanLens: 'infoview-loaded' }, '*');
