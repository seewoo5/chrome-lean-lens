/**
 * Options Page Controller
 */

document.addEventListener('DOMContentLoaded', () => {
  const hoverDelayInput = document.getElementById('hover-delay');
  const hoverDelayVal = document.getElementById('hover-delay-val');
  const themeSelect = document.getElementById('theme-select');
  const enablePRScanner = document.getElementById('enable-pr-scanner');
  const enableBuiltins = document.getElementById('enable-builtins');
  const showOutline = document.getElementById('show-outline');
  const enableLoogle = document.getElementById('enable-loogle');
  const enableHelper = document.getElementById('enable-helper');
  const helperUrl = document.getElementById('helper-url');
  const helperToken = document.getElementById('helper-token');
  const testHelperBtn = document.getElementById('test-helper-btn');
  const helperTestResult = document.getElementById('helper-test-result');
  const clearCacheBtn = document.getElementById('clear-cache-btn');
  const saveStatus = document.getElementById('save-status');

  const statTotal = document.getElementById('stat-total');
  const statCache = document.getElementById('stat-cache');
  const statLoogle = document.getElementById('stat-loogle');

  let currentSettings = {};

  // Load existing settings and stats
  chrome.runtime.sendMessage({ action: "GET_SETTINGS" }, (res) => {
    if (res && res.settings) {
      currentSettings = res.settings;
      hoverDelayInput.value = currentSettings.hoverDelay || 250;
      hoverDelayVal.textContent = `${hoverDelayInput.value}ms`;
      themeSelect.value = currentSettings.theme || 'auto';
      enablePRScanner.checked = currentSettings.enablePRScanner !== false;
      enableBuiltins.checked = currentSettings.enableBuiltins !== false;
      showOutline.checked = currentSettings.showOutline !== false;
      enableLoogle.checked = currentSettings.enableLoogle !== false;
      enableHelper.checked = Boolean(currentSettings.enableHelper);
      helperUrl.value = currentSettings.helperUrl || 'http://127.0.0.1:5326';
      helperToken.value = currentSettings.helperToken || '';
    }

    if (res && res.stats) {
      statTotal.textContent = res.stats.totalQueries || 0;
      statCache.textContent = res.stats.cacheHits || 0;
      statLoogle.textContent = res.stats.loogleHits || 0;
    }
  });

  // Save Settings Function
  function saveSettings() {
    currentSettings = {
      ...currentSettings,
      hoverDelay: parseInt(hoverDelayInput.value, 10),
      theme: themeSelect.value,
      enablePRScanner: enablePRScanner.checked,
      enableBuiltins: enableBuiltins.checked,
      showOutline: showOutline.checked,
      enableLoogle: enableLoogle.checked,
      enableHelper: enableHelper.checked,
      helperUrl: helperUrl.value.trim(),
      helperToken: helperToken.value.trim()
    };

    chrome.runtime.sendMessage({ action: "SET_SETTINGS", settings: currentSettings }, (res) => {
      saveStatus.classList.add('visible');
      setTimeout(() => saveStatus.classList.remove('visible'), 1500);
      // The helper's address and token are kept where no web page can reach them. Where the
      // browser gives the extension no such place that lasts, they are not saved for good.
      if (res && res.helperKept && res.helperKept !== 'saved' && currentSettings.enableHelper) {
        helperTestResult.textContent = 'This browser gives the extension no private storage that lasts, so the helper\'s address and token are kept only '
          + (res.helperKept === 'session' ? 'until the browser closes' : 'for a short while (until the browser stops the extension\'s background, as it does when it is not in use)')
          + ': paste them again after that.';
        helperTestResult.style.color = '';
      }

      // Notify all tabs
      chrome.tabs.query({}, (tabs) => {
        tabs.forEach((tab) => {
          if (tab.id) {
            chrome.tabs.sendMessage(tab.id, { action: "SETTINGS_UPDATED" });
          }
        });
      });
    });
  }

  // Event Listeners for Live Updating
  hoverDelayInput.addEventListener('input', () => {
    hoverDelayVal.textContent = `${hoverDelayInput.value}ms`;
    saveSettings();
  });

  themeSelect.addEventListener('change', saveSettings);
  enablePRScanner.addEventListener('change', saveSettings);
  enableBuiltins.addEventListener('change', saveSettings);
  showOutline.addEventListener('change', saveSettings);
  enableLoogle.addEventListener('change', saveSettings);
  enableHelper.addEventListener('change', saveSettings);
  // Save while typing or pasting too: `change` waits for the field to lose focus, which never
  // happens when the page is closed right after pasting (Firefox's options sit in about:addons).
  let typingTimer = null;
  const saveSoon = () => { clearTimeout(typingTimer); typingTimer = setTimeout(saveSettings, 300); };
  for (const field of [helperUrl, helperToken]) {
    field.addEventListener('input', saveSoon);
    field.addEventListener('change', saveSettings);
  }

  // Test the connection to the local helper
  testHelperBtn.addEventListener('click', () => {
    helperTestResult.textContent = 'Testing connection...';
    helperTestResult.style.color = '#8b949e';

    chrome.runtime.sendMessage(
      { action: "TEST_HELPER", url: helperUrl.value.trim(), token: helperToken.value.trim() },
      (res) => {
        if (res && res.success) {
          const details = res.details || {};
          const allowed = details.allow || [];
          const sandbox = details.runs === 'codespaces'
            ? 'Lean runs in GitHub Codespaces, not on this machine.'
            : (details.sandbox === 'seatbelt' || details.sandbox === 'bwrap' ? 'Sandbox on.' : 'No sandbox: Lean runs with your permissions.');
          helperTestResult.textContent = `✓ Connected. ${sandbox} Allowed repositories: ${allowed.length ? allowed.join(', ') : 'none yet'}.`;
          helperTestResult.style.color = '#3fb950';
        } else if (res && res.state === 'unauthorized') {
          helperTestResult.textContent = '✗ The helper is running but rejected this token.';
          helperTestResult.style.color = '#f85149';
        } else if (res && res.state === 'not_local') {
          helperTestResult.textContent = '✗ The helper runs on this machine: its address starts with http://127.0.0.1 or http://localhost.';
          helperTestResult.style.color = '#f85149';
        } else {
          helperTestResult.textContent = '✗ Could not reach the helper. Start it with: node helper/lean-lens-helper.mjs';
          helperTestResult.style.color = '#f85149';
        }
      }
    );
  });

  // Clear Cache Button
  clearCacheBtn.addEventListener('click', () => {
    if (confirm('Are you sure you want to clear all cached definition data?')) {
      chrome.runtime.sendMessage({ action: "CLEAR_CACHE" }, () => {
        statCache.textContent = '0';
        alert('Cache cleared successfully.');
      });
    }
  });
});
