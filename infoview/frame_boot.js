/**
 * Runs before the infoview's modules load, in the frame that shows it (frame.html).
 *
 * A widget of a Lean file is a JavaScript module the infoview gets from Lean and imports while
 * running. Such a module imports React and the infoview by name, and those names have to mean
 * the very modules this page runs: an import map says so. A page may add one only where its
 * rules allow inline scripts, which this frame's do in Chrome (see the manifest's `sandbox`).
 * Elsewhere the map is refused, widgets fail to load, and the rest of the infoview works.
 */
(function () {
  const vendor = new URL('vendor/', document.baseURI).href;
  const map = document.createElement('script');
  map.type = 'importmap';
  map.textContent = JSON.stringify({
    imports: {
      '@leanprover/infoview': `${vendor}infoview.js`,
      react: `${vendor}react.js`,
      'react-dom': `${vendor}react-dom.js`,
      'react/jsx-runtime': `${vendor}react-jsx-runtime.js`
    }
  });
  document.head.appendChild(map);
  // Shown when the infoview's module does not load: the files are made by `npm install`.
  window.addEventListener('error', (event) => {
    const el = event.target;
    if (el && el.tagName === 'SCRIPT' && /frame\.js$/.test(el.src || '')) document.getElementById('infoview-missing').hidden = false;
  }, true);
})();
