#!/usr/bin/env node
/**
 * Builds the Firefox version of the extension into dist/firefox/.
 *
 * The code is shared with Chrome unchanged; only the manifest differs:
 * Firefox runs the background as an event page (background.scripts) instead of
 * a service worker, so the files the service worker pulls in with importScripts
 * are listed there in the same order. Firefox also needs an add-on id, and has no sandboxed
 * extension pages: the infoview's frame is sandboxed by the page that holds it instead.
 *
 * The infoview's own files (infoview/vendor/) are made by `npm install`: run that first.
 *
 *   node scripts/build-firefox.mjs          # writes dist/firefox/
 *   node scripts/build-firefox.mjs --zip    # also writes dist/lean-lens-firefox-<version>.zip
 */
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const out = path.join(root, 'dist', 'firefox');

// What the extension itself is made of; the helper, tests and scripts stay out.
const INCLUDE = ['background', 'content', 'icons', 'infoview', 'options', 'popup'];
const SKIP = /(?:^|\/)(?:\.DS_Store|__pycache__|.*\.py|.*\.pyc)$/;

export function firefoxManifest(chrome) {
  const manifest = structuredClone(chrome);
  manifest.background = {
    scripts: [
      'content/lean_terms.js',
      'content/binder_context.js',
      'content/pr_scanner.js',
      'content/lean_outline.js',
      'background/exact_data.js',
      'background/service_worker.js'
    ]
  };
  // Chrome's sandboxed pages, and the rules it gives them: Firefox knows neither. There the
  // infoview's frame runs under the rules of every extension page, which let no widget code
  // in. And unlike Chrome, Firefox lets the panel's page show that frame without a web page
  // being allowed to: so only the panel's page is open to GitHub's pages.
  delete manifest.sandbox;
  delete manifest.content_security_policy;
  manifest.web_accessible_resources = (manifest.web_accessible_resources || []).map((entry) => (
    { ...entry, resources: entry.resources.filter((resource) => resource !== 'infoview/frame.html') }));
  manifest.browser_specific_settings = {
    gecko: {
      id: 'lean-lens@seewoo5.github.io',
      strict_min_version: '140.0',
      data_collection_permissions: { required: ['none'] }
    }
  };
  return manifest;
}

function copyDir(from, to) {
  fs.mkdirSync(to, { recursive: true });
  for (const entry of fs.readdirSync(from, { withFileTypes: true })) {
    const src = path.join(from, entry.name);
    if (SKIP.test(src)) continue;
    const dst = path.join(to, entry.name);
    if (entry.isDirectory()) copyDir(src, dst);
    else fs.copyFileSync(src, dst);
  }
}

function build({ zip }) {
  const chrome = JSON.parse(fs.readFileSync(path.join(root, 'manifest.json'), 'utf8'));
  const manifest = firefoxManifest(chrome);
  for (const file of manifest.background.scripts) {
    if (!fs.existsSync(path.join(root, file))) throw new Error(`Missing background script: ${file}`);
  }

  if (!fs.existsSync(path.join(root, 'infoview', 'vendor', 'infoview.js'))) {
    console.warn('infoview/vendor/ is missing, so this build has no infoview. Run `npm install` first to include it.');
  }

  fs.rmSync(out, { recursive: true, force: true });
  for (const dir of INCLUDE) copyDir(path.join(root, dir), path.join(out, dir));
  fs.writeFileSync(path.join(out, 'manifest.json'), JSON.stringify(manifest, null, 2) + '\n');
  console.log(`Built ${path.relative(root, out)}/ (version ${manifest.version}).`);

  if (zip) {
    const archive = path.join(root, 'dist', `lean-lens-firefox-${manifest.version}.zip`);
    fs.rmSync(archive, { force: true });
    execFileSync('zip', ['-qr', '-X', archive, '.'], { cwd: out });
    console.log(`Packed ${path.relative(root, archive)}.`);
  }
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  build({ zip: process.argv.includes('--zip') });
}
