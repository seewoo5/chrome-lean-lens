#!/usr/bin/env node
/**
 * Puts Lean's infoview (the NPM package @leanprover/infoview) where the extension loads it
 * from: infoview/vendor/. `npm install` runs this.
 *
 * The package ships the infoview and the React it uses as ES modules that import each other by
 * name (`import … from "react"`). A browser resolves such names only through an import map,
 * which an extension's page may not always have: so the names are rewritten here to the files
 * next to them. Nothing else in the files changes.
 *
 *   node scripts/build-infoview.mjs
 */
import fs from 'node:fs';
import path from 'node:path';
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
export const VENDOR_DIR = path.join(root, 'infoview', 'vendor');

// The modules, by the name others import them under: the package's file and ours.
export const MODULES = {
  '@leanprover/infoview': ['index.production.min.js', 'infoview.js'],
  react: ['react.production.min.js', 'react.js'],
  'react-dom': ['react-dom.production.min.js', 'react-dom.js'],
  'react/jsx-runtime': ['react-jsx-runtime.production.min.js', 'react-jsx-runtime.js'],
};
const OTHER_FILES = { 'index.css': 'infoview.css', 'codicon.ttf': 'codicon.ttf' };

/**
 * A module's source with the names it imports replaced by relative paths. `imports` are the
 * module's imports as es-module-lexer finds them. Throws on a name there is no file for.
 */
export function rewriteImports(source, imports, targets) {
  let out = '';
  let at = 0;
  for (const found of imports) {
    if (found.d !== -1) continue; // `import(…)` at run time: a widget's module, not one of these
    const name = found.n;
    if (name === undefined) continue;
    if (name.startsWith('./') || name.startsWith('../')) continue;
    if (!Object.prototype.hasOwnProperty.call(targets, name)) throw new Error(`No file for the import "${name}"`);
    out += source.slice(at, found.s) + targets[name];
    at = found.e;
  }
  return out + source.slice(at);
}

async function build() {
  const require = createRequire(path.join(root, 'package.json'));
  let manifestPath;
  try {
    manifestPath = require.resolve('@leanprover/infoview/package.json');
  } catch {
    throw new Error('@leanprover/infoview is not installed. Run `npm install` in this folder first.');
  }
  const { init, parse } = await import('es-module-lexer');
  await init;
  const dist = path.join(path.dirname(manifestPath), 'dist');
  const version = JSON.parse(fs.readFileSync(manifestPath, 'utf8')).version;
  const targets = Object.fromEntries(Object.entries(MODULES).map(([name, [, file]]) => [name, `./${file}`]));

  fs.rmSync(VENDOR_DIR, { recursive: true, force: true });
  fs.mkdirSync(VENDOR_DIR, { recursive: true });
  for (const [from, to] of Object.values(MODULES)) {
    const source = fs.readFileSync(path.join(dist, from), 'utf8');
    const rewritten = rewriteImports(source, parse(source)[0], targets);
    // What is written must import nothing by name any more.
    const left = parse(rewritten)[0].filter((found) => found.d === -1 && found.n !== undefined && !found.n.startsWith('./'));
    if (left.length) throw new Error(`${from} still imports ${left.map((found) => found.n).join(', ')}`);
    fs.writeFileSync(path.join(VENDOR_DIR, to), rewritten);
  }
  for (const [from, to] of Object.entries(OTHER_FILES)) fs.copyFileSync(path.join(dist, from), path.join(VENDOR_DIR, to));
  fs.writeFileSync(path.join(VENDOR_DIR, 'version.json'), `${JSON.stringify({ infoview: version }, null, 2)}\n`);
  fs.writeFileSync(path.join(VENDOR_DIR, 'NOTICE.txt'), [
    `These files come from the NPM package @leanprover/infoview ${version}`,
    '(https://github.com/leanprover/vscode-lean4, Apache License 2.0), unchanged but for the',
    'paths of the modules they import. They include React and React DOM (MIT License,',
    'Copyright (c) Meta Platforms, Inc. and affiliates), the Codicons font (CC BY 4.0,',
    'Microsoft) and Tachyons (MIT License).',
    '',
    'Made by scripts/build-infoview.mjs. Do not edit: `npm install` writes them again.',
    '',
  ].join('\n'));
  console.log(`Built ${path.relative(root, VENDOR_DIR)}/ from @leanprover/infoview ${version}.`);
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  build().catch((error) => {
    console.error(error.message);
    process.exitCode = 1;
  });
}
