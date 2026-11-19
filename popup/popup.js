/**
 * Popup logic for Lean Lens
 */

document.addEventListener('DOMContentLoaded', () => {
  const toggle = document.getElementById('extension-toggle');
  const toggleDesc = document.getElementById('toggle-desc');
  const statusDot = document.getElementById('status-dot');
  const statusText = document.getElementById('status-text');
  const prDeclsBox = document.getElementById('pr-decls-box');
  const prDeclsCount = document.getElementById('pr-decls-count');
  const prDeclsTags = document.getElementById('pr-decls-tags');

  const searchInput = document.getElementById('symbol-search-input');
  const searchBtn = document.getElementById('symbol-search-btn');
  const resultBox = document.getElementById('search-result-box');
  const resultKind = document.getElementById('result-kind');
  const resultName = document.getElementById('result-name');
  const resultSignature = document.getElementById('result-signature');
  const resultDocstring = document.getElementById('result-docstring');

  // Load Settings
  chrome.runtime.sendMessage({ action: "GET_SETTINGS" }, (res) => {
    if (res && res.settings) {
      toggle.checked = res.settings.enabled !== false;
      updateToggleLabel(toggle.checked);
    }
  });

  // Check Current Active Tab
  chrome.tabs.query({ active: true, currentWindow: true }, (tabs) => {
    const activeTab = tabs[0];
    if (!activeTab || !activeTab.url) {
      setStatus(false, "No active tab detected");
      return;
    }

    if (!activeTab.url.includes("github.com")) {
      setStatus(false, "Lean Lens is ready (open a GitHub Lean PR or file)");
      return;
    }

    // Ping content script for PR scan status
    chrome.tabs.sendMessage(activeTab.id, { action: "GET_PAGE_INFO" }, (pageInfo) => {
      if (chrome.runtime.lastError || !pageInfo) {
        setStatus(true, "Active on GitHub");
        return;
      }

      if (pageInfo.prDefinitionsCount > 0) {
        setStatus(true, `Lean PR: ${pageInfo.prDefinitionsCount} local definitions found`);
        renderPRDeclarations(pageInfo.declarations, pageInfo.prDefinitionsCount);
      } else if (pageInfo.isLeanDetected) {
        setStatus(true, "Lean file detected (Hover code to inspect)");
      } else {
        setStatus(true, "GitHub page ready");
      }
    });
  });

  // Toggle Extension Switch
  toggle.addEventListener('change', () => {
    const isEnabled = toggle.checked;
    updateToggleLabel(isEnabled);

    chrome.runtime.sendMessage({ action: "GET_SETTINGS" }, (res) => {
      const current = res?.settings || {};
      current.enabled = isEnabled;
      // (The helper's settings, when they could not be read, are not this page's to save.)
      if (res?.helperKept === 'unread') for (const key of ['enableHelper', 'helperUrl', 'helperToken']) delete current[key];
      chrome.runtime.sendMessage({ action: "SET_SETTINGS", settings: current }, () => {
        // Notify active tab
        chrome.tabs.query({ active: true, currentWindow: true }, (tabs) => {
          if (tabs[0]?.id) {
            chrome.tabs.sendMessage(tabs[0].id, { action: "SETTINGS_UPDATED" });
          }
        });
      });
    });
  });

  function updateToggleLabel(enabled) {
    toggleDesc.textContent = enabled ? "Active on GitHub PRs and files" : "Inspection paused";
  }

  function setStatus(active, text) {
    if (active) {
      statusDot.classList.add('active');
    } else {
      statusDot.classList.remove('active');
    }
    statusText.textContent = text;
  }

  function renderPRDeclarations(declarations, count) {
    if (!declarations || declarations.length === 0) return;
    prDeclsBox.classList.remove('hidden');
    prDeclsCount.textContent = count.toString();
    prDeclsTags.innerHTML = '';

    declarations.forEach((decl) => {
      const tag = document.createElement('span');
      tag.className = 'pr-decl-tag';
      tag.textContent = decl.shortName || decl.name;
      tag.title = `${decl.kind} ${decl.name}`;
      tag.addEventListener('click', () => {
        searchInput.value = decl.name;
        executeSearch(decl.name);
      });
      prDeclsTags.appendChild(tag);
    });
  }

  // Symbol Search Handler
  function executeSearch(query) {
    const token = (query || searchInput.value || '').trim();
    if (!token) return;

    resultBox.classList.remove('hidden');
    resultName.textContent = token;
    resultKind.textContent = '...';
    resultSignature.textContent = 'Looking up definition in Loogle...';
    resultDocstring.textContent = '';

    chrome.runtime.sendMessage({ action: "LOOKUP_TOKEN", token: token }, (res) => {
      if (res && res.success && res.data) {
        const d = res.data;
        resultKind.textContent = d.kind || 'def';
        resultName.textContent = d.name;
        resultSignature.textContent = d.typeSignature || `${d.kind} ${d.name}`;
        resultDocstring.textContent = d.docstring || '(No docstring)';
      } else {
        resultKind.textContent = 'none';
        resultSignature.textContent = 'Symbol not found in Loogle or local cache.';
        resultDocstring.textContent = 'Try searching in Mathlib 4 docs directly.';
      }
    });
  }

  searchBtn.addEventListener('click', () => executeSearch());
  searchInput.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') {
      executeSearch();
    }
  });
});
