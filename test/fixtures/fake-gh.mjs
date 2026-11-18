#!/usr/bin/env node
// A stand-in for `gh` in the tests. A "codespace" is a folder on this machine (its home
// folder), `ssh` runs the command here with that folder as home, and `ports forward` relays one
// local port to another. $FAKE_GH_DIR/state.json holds the codespaces and every call made.
import { spawn } from 'node:child_process';
import fs from 'node:fs';
import net from 'node:net';
import path from 'node:path';

const dir = process.env.FAKE_GH_DIR;
if (!dir) {
  console.error('FAKE_GH_DIR is not set');
  process.exit(2);
}
const stateFile = path.join(dir, 'state.json');
const load = () => {
  try { return JSON.parse(fs.readFileSync(stateFile, 'utf8')); } catch { return { codespaces: [], calls: [], push: false, scope: true }; }
};
const save = (state) => fs.writeFileSync(stateFile, JSON.stringify(state, null, 2));
const args = process.argv.slice(2);
const option = (name) => (args.includes(name) ? args[args.indexOf(name) + 1] : undefined);
const fail = (message) => {
  console.error(message);
  process.exit(1);
};
const state = load();
state.calls.push(args.slice(0, 2).join(' '));
(state.argv = state.argv || []).push(args); // every call in full: the tests check which codespace each one named
save(state);
const home = (name) => path.join(dir, 'homes', name);
const named = () => state.codespaces.find((space) => space.name === option('-c')) || fail(`no codespace named ${option('-c')}`);
/** Stop the helper running in a codespace, as stopping the codespace would. */
const stopHelper = (name) => {
  try { process.kill(Number(fs.readFileSync(path.join(home(name), '.lean-lens', 'helper.pid'), 'utf8')), 'SIGTERM'); } catch { /* none */ }
};

if (args[0] === 'api') {
  console.log(String(Boolean(state.push)));
} else if (args[0] !== 'codespace') {
  fail(`fake gh: no command ${args[0]}`);
} else if (!state.scope) {
  fail('error getting codespaces: HTTP 403: Must have admin rights to Repository.\nThis API operation needs the "codespace" scope. To request it, run:  gh auth refresh -h github.com -s codespace');
} else if (args[1] === 'list') {
  // A new codespace is "Provisioning" for as many listings as `slow` says.
  for (const space of state.codespaces) {
    if (space.slow > 0) { space.slow -= 1; space.state = space.slow ? 'Provisioning' : 'Available'; }
  }
  save(state);
  console.log(JSON.stringify(state.codespaces));
} else if (args[1] === 'create') {
  // A repository may allow only some machines, as mathlib4 does.
  if (state.machines && !state.machines.includes(option('--machine'))) {
    fail(`error getting machine type: there is no such machine for the repository: ${option('--machine')}\nAvailable machines: [${state.machines.join(' ')}]`);
  }
  const name = `fake-${state.created = (state.created || state.codespaces.length) + 1}`;
  state.codespaces.push({ name, displayName: option('--display-name'), repository: option('--repo'), state: state.slow ? 'Provisioning' : 'Available', slow: state.slow || 0, lastUsedAt: null, machine: option('--machine') });
  fs.mkdirSync(home(name), { recursive: true });
  save(state);
  console.log(name);
} else if (args[1] === 'ssh') {
  const space = named();
  space.state = 'Available'; // connecting starts a stopped codespace
  save(state);
  const child = spawn('bash', ['-c', args[args.indexOf('--') + 1]], {
    stdio: 'inherit',
    env: { ...process.env, HOME: home(space.name), LEAN_LENS_SKIP_INSTALL: '1' },
  });
  child.on('close', (code) => process.exit(code === null ? 1 : code));
} else if (args[1] === 'ports' && args[2] === 'forward') {
  named();
  const [remote, local] = args[3].split(':').map(Number);
  net.createServer((client) => {
    const there = net.connect(remote, '127.0.0.1');
    const end = () => { client.destroy(); there.destroy(); };
    client.on('error', end);
    there.on('error', end);
    client.pipe(there).pipe(client);
  }).listen(local, '127.0.0.1', () => console.log(`Forwarding ports: remote ${remote} <=> local ${local}`));
} else if (args[1] === 'stop') {
  const space = named();
  stopHelper(space.name);
  space.state = 'Shutdown';
  save(state);
} else if (args[1] === 'delete') {
  const space = named();
  if (state.undeletable) fail('error deleting codespace: HTTP 503');
  stopHelper(space.name);
  state.codespaces = state.codespaces.filter((entry) => entry !== space);
  fs.rmSync(home(space.name), { recursive: true, force: true });
  save(state);
} else {
  fail(`fake gh: no command codespace ${args[1]}`);
}
