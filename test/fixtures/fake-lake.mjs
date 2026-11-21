#!/usr/bin/env node
// A stand-in for `lake` in the tests. `lake env …` does nothing, and `lake serve` is a language
// server that knows just enough to be talked to: it answers `initialize`, says a file it is
// given has been read (diagnostics and progress), opens RPC sessions, and answers
// `$/lean/plainGoal` with the position it was asked about.
const args = process.argv.slice(2);
if (args[0] !== 'serve') process.exit(0);

const send = (message) => {
  const body = Buffer.from(JSON.stringify({ jsonrpc: '2.0', ...message }), 'utf8');
  process.stdout.write(Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`), body]));
};
const open = new Map(); // uri → text
function handle(message) {
  const { id, method, params } = message;
  if (method === 'initialize') {
    send({ id, result: { capabilities: { experimental: { rpcProvider: { rpcWireFormat: 'v1' } } }, serverInfo: { name: 'fake Lean', version: '0.0.0' }, hasWidgets: params.initializationOptions.hasWidgets } });
  } else if (method === 'textDocument/didOpen') {
    const { uri, text } = params.textDocument;
    open.set(uri, text);
    // (As Lean does at times: something it asks of its client.)
    send({ id: 'server-1', method: 'client/registerCapability', params: { registrations: [] } });
    send({ method: '$/lean/fileProgress', params: { textDocument: { uri, version: 1 }, processing: [] } });
    send({ method: 'textDocument/publishDiagnostics', params: { uri, version: 1, diagnostics: [{ message: `read ${text.length} characters`, range: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } } }] } });
  } else if (method === 'textDocument/didClose') {
    open.delete(params.textDocument.uri);
  } else if (method === '$/lean/rpc/connect') {
    send({ id, result: { sessionId: `rpc-${open.size}` } });
  } else if (method === '$/lean/plainGoal') {
    if (!open.has(params.textDocument.uri)) send({ id, error: { code: -32801, message: 'not open' } });
    else send({ id, result: { goals: [`⊢ at ${params.position.line}:${params.position.character}`], rendered: '' } });
  } else if (method === 'crash') {
    process.stderr.write('the server fell over\n');
    process.exit(3);
  } else if (id !== undefined && method) {
    send({ id, error: { code: -32601, message: `no ${method}` } });
  }
}

let buffer = Buffer.alloc(0);
process.stdin.on('data', (chunk) => {
  buffer = Buffer.concat([buffer, chunk]);
  for (;;) {
    const head = buffer.indexOf('\r\n\r\n');
    if (head === -1) return;
    const length = Number(/content-length:\s*(\d+)/i.exec(buffer.toString('latin1', 0, head))[1]);
    if (buffer.length < head + 4 + length) return;
    const message = JSON.parse(buffer.toString('utf8', head + 4, head + 4 + length));
    buffer = buffer.subarray(head + 4 + length);
    handle(message);
  }
});
process.stdin.on('end', () => process.exit(0));
