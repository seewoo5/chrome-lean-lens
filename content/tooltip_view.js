/**
 * Lean Lens hover tooltip view component.
 * Renders rich, interactive, syntax-highlighted tooltips in GitHub (styled like Lean's documentation hovers).
 */

(function () {
  class VersoTooltipView {
    constructor() {
      this.container = null;
      this.isPinned = false;
      this.currentTarget = null;
      this.currentData = null;
      this.currentExtras = null;
      this.hideTimer = null;
      // Where hovers are shown instead of beside the code (the bottom of the infoview's panel), or null.
      this.dock = null;
      // The code the hover shown is about, and whether the card is only a lookup's spinner.
      this.shownShade = null;
      this.loadingCard = false;
      this.initDOM();
      this.bindEvents();
    }

    /**
     * Show hovers in `el` (the bottom of the infoview's panel) instead of beside the code; with
     * no `el`, beside the code again. Docked, a hover stays until another one replaces it:
     * moving the pointer away does not close it, and a spot with nothing to show leaves it as
     * it is. Only Esc, the close button, or leaving the page clears it.
     */
    dockIn(el) {
      el = el || null;
      if (el === this.dock) return;
      const shown = this.isVisible() && !this.loadingCard;
      this.clearHideTimer();
      if (this.dock) this.dock.classList.remove('verso-dock-filled');
      this.dock = el;
      this.container.classList.toggle('verso-docked', Boolean(el));
      this.container.classList.remove('verso-loading');
      const card = this.container.querySelector('.verso-tooltip-card');
      if (card && card.style) card.style.maxHeight = '';
      this.container.style.left = '';
      this.container.style.top = '';
      (el || document.body).appendChild(this.container);
      const pinBtn = this.container.querySelector('#verso-pin-btn');
      const closeBtn = this.container.querySelector('#verso-close-btn');
      if (pinBtn) pinBtn.title = el ? 'Keep this hover while the pointer moves on (Alt)' : 'Pin tooltip (Alt)';
      if (closeBtn) closeBtn.title = el ? 'Clear (Esc)' : 'Close (Esc)';
      if (el && shown) {
        // The hover open beside the code moves into the panel, laid out for it.
        this.renderExtras(this.currentExtras);
        this.syncDock();
      } else {
        // Out of the panel, its hover goes: there is no place beside the code to put it.
        this.hide(true);
      }
    }

    /** Tell the dock whether it holds a hover (it shows a hint while it does not). */
    syncDock() {
      if (this.dock) this.dock.classList.toggle('verso-dock-filled', this.isVisible());
    }

    /**
     * Initialize tooltip DOM structure.
     */
    initDOM() {
      // A root left by an earlier version of the extension is rebuilt, so every part exists.
      const existing = document.getElementById('verso-hover-root');
      if (existing && existing.querySelector('#verso-col-state')) {
        this.container = existing;
        return;
      }

      this.container = existing || document.createElement('div');
      this.container.id = 'verso-hover-root';
      this.container.className = 'verso-hover-container verso-hidden';
      this.container.innerHTML = `
        <div class="verso-tooltip-card">
          <div class="verso-header">
            <div class="verso-header-left">
              <span class="verso-kind-badge" id="verso-kind">def</span>
              <span class="verso-ident-title" id="verso-title"></span>
            </div>
            <div class="verso-header-actions">
              <button class="verso-action-btn" id="verso-copy-btn" title="Copy symbol name">
                <svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><rect x="9" y="9" width="13" height="13" rx="2" ry="2"></rect><path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"></path></svg>
              </button>
              <button class="verso-action-btn" id="verso-pin-btn" title="Pin tooltip (Alt)">
                <svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><line x1="12" y1="17" x2="12" y2="22"></line><path d="M5 17h14v-2l-3-3V5a2 2 0 0 0-2-2h-4a2 2 0 0 0-2 2v7l-3 3v2z"></path></svg>
              </button>
              <button class="verso-action-btn" id="verso-close-btn" title="Close (Esc)">
                <svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><line x1="18" y1="6" x2="6" y2="18"></line><line x1="6" y1="6" x2="18" y2="18"></line></svg>
              </button>
            </div>
          </div>
          <div class="verso-module-bar" id="verso-module-bar">
            <span class="verso-module-name" id="verso-module"></span>
          </div>
          <div class="verso-body">
            <!-- What Lean's run says about this spot: the proof state and its messages. Beside
                 the definition (on its left) when there is a proof state, below it otherwise. -->
            <div class="verso-col verso-col-state" id="verso-col-state">
              <div class="verso-goals verso-hidden" id="verso-goals">
                <div class="verso-goals-title" id="verso-goals-title"></div>
                <pre class="verso-code-block verso-goals-block" id="verso-goals-body"></pre>
              </div>
              <div class="verso-messages verso-hidden" id="verso-messages"></div>
            </div>
            <div class="verso-col verso-col-def" id="verso-col-def">
              <div class="verso-signature-container">
                <pre class="verso-code-block" id="verso-signature"></pre>
              </div>
              <div class="verso-pr-banner verso-hidden" id="verso-pr-banner">
                <div class="verso-pr-badge">✨ Defined in this PR</div>
                <button class="verso-pr-jump-btn" id="verso-pr-jump-btn">Jump to definition &rarr;</button>
              </div>
              <div class="verso-docstring" id="verso-docstring"></div>
            </div>
          </div>
          <div class="verso-footer">
            <div class="verso-footer-source" id="verso-footer-source">Verso Documentation</div>
            <div class="verso-footer-links">
              <a href="#" target="_blank" rel="noopener noreferrer" class="verso-ext-link" id="verso-docs-link">Verso Docs &rarr;</a>
            </div>
          </div>
          <div class="verso-helper-bar verso-hidden" id="verso-helper-bar">
            <span class="verso-helper-text" id="verso-helper-text"></span>
            <button class="verso-helper-btn verso-hidden" id="verso-helper-btn"></button>
          </div>
        </div>
      `;

      if (!existing) document.body.appendChild(this.container);
    }

    /**
     * Bind hover and interactive actions.
     */
    bindEvents() {
      // Keep tooltip visible when mouse moves over it
      this.container.addEventListener('mouseenter', () => {
        this.clearHideTimer();
      });

      this.container.addEventListener('mouseleave', () => {
        if (!this.isPinned) {
          this.scheduleHide(150);
        }
      });

      // Pin button
      const pinBtn = this.container.querySelector('#verso-pin-btn');
      pinBtn?.addEventListener('click', (e) => {
        e.stopPropagation();
        this.togglePin();
      });

      // Close button
      const closeBtn = this.container.querySelector('#verso-close-btn');
      closeBtn?.addEventListener('click', (e) => {
        e.stopPropagation();
        this.hide(true);
      });

      // Copy symbol name
      const copyBtn = this.container.querySelector('#verso-copy-btn');
      copyBtn?.addEventListener('click', (e) => {
        e.stopPropagation();
        if (this.currentData?.name) {
          navigator.clipboard.writeText(this.currentData.name);
          copyBtn.classList.add('verso-btn-success');
          setTimeout(() => copyBtn.classList.remove('verso-btn-success'), 1200);
        }
      });

      // Jump to PR definition
      const jumpBtn = this.container.querySelector('#verso-pr-jump-btn');
      jumpBtn?.addEventListener('click', (e) => {
        e.stopPropagation();
        if (this.currentData?.element) {
          this.currentData.element.scrollIntoView({ behavior: 'smooth', block: 'center' });
          this.currentData.element.classList.add('verso-highlight-target');
          setTimeout(() => {
            this.currentData.element.classList.remove('verso-highlight-target');
          }, 2500);
        }
      });

      // Run Lean on this pull request (the local helper), from the status row.
      const helperBtn = this.container.querySelector('#verso-helper-btn');
      helperBtn?.addEventListener('click', (e) => {
        e.stopPropagation();
        const helper = this.currentExtras && this.currentExtras.helper;
        if (!helper || typeof helper.run !== 'function') return;
        helperBtn.classList.add('verso-hidden');
        this.container.querySelector('#verso-helper-text').textContent = 'Starting Lean…';
        helper.run();
      });

      // Stepping through a proof, and switching between the goals before and after a tactic.
      const goalsEl = this.container.querySelector('#verso-goals');
      goalsEl?.addEventListener('click', (e) => {
        const stepBtn = e.target.closest && e.target.closest('[data-step]');
        const sideBtn = e.target.closest && e.target.closest('[data-side]');
        if (!stepBtn && !sideBtn) return;
        e.stopPropagation();
        if (sideBtn) {
          this.goalsSide = sideBtn.getAttribute('data-side');
          this.renderExtras(this.currentExtras);
          this.keepPlace();
        } else {
          this.step(Number(stepBtn.getAttribute('data-step')));
        }
      });

      // Keyboard handler (Esc to dismiss, Alt to toggle pin, ← → to step through a proof)
      window.addEventListener('keydown', (e) => {
        const typing = Boolean(e.target && e.target.closest && e.target.closest('input, textarea, [contenteditable="true"]'));
        // Docked, a hover is nearly always shown: keys typed in a text field (Esc to leave a
        // comment, Option for a symbol) are the field's.
        if (this.dock && typing) return;
        if (e.key === 'Escape' && this.isVisible()) {
          this.hide(true);
        } else if (e.key === 'Alt' && this.isVisible()) {
          this.togglePin();
        } else if ((e.key === 'ArrowLeft' || e.key === 'ArrowRight') && this.isVisible() && this.isPinned &&
          this.currentExtras && this.currentExtras.stepper && !e.altKey && !e.metaKey && !e.ctrlKey && !typing) {
          e.preventDefault();
          this.step(e.key === 'ArrowLeft' ? -1 : 1);
        }
      });
    }

    /**
     * Shade the code a hover is about, like the editor's hover highlight in Lean's VS Code
     * extension, with the CSS Custom Highlight API (no extra elements; follows scrolling).
     */
    setShade(ranges) {
      try {
        if (typeof CSS === 'undefined' || !CSS.highlights || typeof Highlight === 'undefined') return;
        if (ranges && ranges.length) CSS.highlights.set('lean-lens-hover', new Highlight(...ranges));
        else CSS.highlights.delete('lean-lens-hover');
      } catch (err) {
        // Not supported here: the tooltip alone still works.
      }
    }

    /**
     * Show definition in tooltip anchored at boundingRect, shading `shade` (ranges) in the code.
     * `extras` is what the local helper's Lean run adds: `{goals, messages, helper, lean}`.
     * With no `data`, the card shows the proof state alone. With `opts.inPlace`, a card already
     * open stays where it is instead (stepping through a proof).
     */
    show(data, boundingRect, shade, extras = null, opts = {}) {
      this.clearHideTimer();
      const inPlace = Boolean(opts.inPlace) && this.isVisible();
      if (!data) {
        data = { name: 'Proof state', kind: 'goal', source: 'lean', lean: extras && extras.lean, bare: true };
      }
      this.currentData = data;
      this.goalsSide = 'after';
      this.setShade(shade);
      this.shownShade = shade || null;
      this.loadingCard = false;
      this.container.classList.remove('verso-loading');

      const titleEl = this.container.querySelector('#verso-title');
      const kindEl = this.container.querySelector('#verso-kind');
      const modEl = this.container.querySelector('#verso-module');
      const sigEl = this.container.querySelector('#verso-signature');
      const docEl = this.container.querySelector('#verso-docstring');
      const prBanner = this.container.querySelector('#verso-pr-banner');
      const sourceEl = this.container.querySelector('#verso-footer-source');
      const docsLink = this.container.querySelector('#verso-docs-link');

      // Populate Name & Kind (a term's text is already in its signature line)
      titleEl.textContent = data.kind === 'term' ? '' : (data.name || 'Unknown');
      const kind = (data.kind || 'def').toLowerCase();
      kindEl.textContent = kind;
      kindEl.className = `verso-kind-badge verso-kind-${kind}`;

      // Module
      if (data.module) {
        modEl.textContent = data.module;
        modEl.parentElement.classList.remove('verso-hidden');
      } else {
        modEl.parentElement.classList.add('verso-hidden');
      }

      // Type Signature with Lean syntax highlighting
      // A term's brackets are lists / sets, not binders: don't colour them as such.
      const noSignature = Boolean(data.bare) || (data.source === 'lean' && !data.typeSignature);
      sigEl.innerHTML = noSignature ? '' : this.highlightLean(data.typeSignature || `${kind} ${data.name}`, { binders: kind !== 'term' });
      sigEl.parentElement.classList.toggle('verso-hidden', noSignature);

      // PR Diff Banner
      if ((data.source === 'pr_diff' || data.source === 'lean') && data.element) {
        prBanner.classList.remove('verso-hidden');
        const jumpBtn = prBanner.querySelector('#verso-pr-jump-btn');
        if (jumpBtn) {
          jumpBtn.textContent = `Jump to line ${data.lineNumber || ''} in PR →`;
        }
      } else {
        prBanner.classList.add('verso-hidden');
      }

      // Docstring (a term's hover is just its type, as in Lean)
      if (data.docstring) {
        docEl.innerHTML = this.renderMarkdown(data.docstring, { softWrap: data.source === 'lean' });
        docEl.classList.remove('verso-hidden');
      } else if (data.kind === 'term' || data.source === 'lean' || data.source === 'outline') {
        // (Lean's own hover has a docstring only when the declaration does.)
        docEl.innerHTML = '';
        docEl.classList.add('verso-hidden');
      } else {
        docEl.innerHTML = '<span class="verso-no-doc">No docstring available.</span>';
        docEl.classList.remove('verso-hidden');
      }

      // Source & Docs Link
      if (data.source === 'lean') {
        // Elaborated by Lean itself, on this machine (the local helper).
        const version = (String(data.lean || '').match(/v?(\d+\.\d+\.\d+\S*)$/) || [])[1];
        sourceEl.textContent = `Lean${version ? ` ${version}` : ''} · run on this machine`;
        if (data.sourceUrl) {
          docsLink.href = data.sourceUrl;
          docsLink.textContent = data.sourceLabel || 'Mathlib Docs →';
          docsLink.classList.remove('verso-hidden');
        } else {
          docsLink.classList.add('verso-hidden');
        }
      } else if (data.source === 'pr_diff') {
        sourceEl.textContent = `PR Local Definition (${data.filePath || 'diff'})`;
        docsLink.classList.add('verso-hidden');
      } else if (data.source === 'builtin') {
        sourceEl.textContent = `Lean 4 Standard Library & Tactics`;
        docsLink.href = data.sourceUrl || `https://leanprover-community.github.io/mathlib4_docs/`;
        docsLink.textContent = `Mathlib Docs →`;
        docsLink.classList.remove('verso-hidden');
      } else if (data.source === 'project') {
        // Read from the repository at the PR's commit (a collapsed diff, or an imported project file).
        sourceEl.textContent = `${data.inPR ? 'Changed in this PR · ' : ''}${data.filePath}:${data.lineNumber}`;
        if (data.repo && data.sha) {
          docsLink.href = `https://github.com/${data.repo}/blob/${data.sha}/${data.filePath}#L${data.lineNumber}`;
          docsLink.textContent = 'View source →';
          docsLink.classList.remove('verso-hidden');
        } else {
          docsLink.classList.add('verso-hidden');
        }
      } else if (data.source === 'outline') {
        // `#where` at a declaration, read from the file's commands.
        sourceEl.textContent = `In force at line ${data.lineNumber}${data.isNew ? ' · added in this PR' : ''} (like #where)`;
        docsLink.classList.add('verso-hidden');
      } else if (data.source === 'term') {
        sourceEl.textContent = 'Type inferred from the source';
        docsLink.classList.add('verso-hidden');
      } else if (data.source === 'local_var') {
        sourceEl.textContent = data.declaredAt ? `Declared with \`variable\` (line ${data.declaredAt})` : 'Local variable';
        docsLink.classList.add('verso-hidden');
      } else {
        sourceEl.textContent = `Loogle / Mathlib docs`;
        docsLink.href = data.sourceUrl || `https://leanprover-community.github.io/mathlib4_docs/`;
        docsLink.textContent = `Mathlib Docs →`;
        docsLink.classList.remove('verso-hidden');
      }

      this.renderExtras(extras);

      // Position tooltip near hovered element (shown first, so its height can be measured)
      this.container.classList.remove('verso-hidden');
      this.container.classList.add('verso-visible');
      if (this.dock) {
        // Docked, a new hover is read from its top; stepping through a proof keeps the place.
        const body = this.container.querySelector('.verso-body');
        if (body && !inPlace) body.scrollTop = 0;
        this.syncDock();
      } else if (inPlace) {
        this.keepPlace();
      } else {
        this.positionTooltip(boundingRect);
      }
    }

    /**
     * What Lean's run adds to a hover: the proof state at the hovered tactic, Lean's messages
     * there, and a row saying whether Lean has run on this file (with a button to run it).
     */
    renderExtras(extras) {
      this.currentExtras = extras || null;
      const goalsEl = this.container.querySelector('#verso-goals');
      const goalsTitle = this.container.querySelector('#verso-goals-title');
      const goalsBody = this.container.querySelector('#verso-goals-body');
      const messagesEl = this.container.querySelector('#verso-messages');
      const bar = this.container.querySelector('#verso-helper-bar');
      const barText = this.container.querySelector('#verso-helper-text');
      const barBtn = this.container.querySelector('#verso-helper-btn');
      const esc = (str) => String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');

      const goals = extras && extras.goals;
      if (goals) {
        this.renderGoals(goals, extras.stepper, goalsTitle, goalsBody);
        goalsEl.classList.remove('verso-hidden');
      } else {
        goalsEl.classList.add('verso-hidden');
      }

      // Two columns when there is a proof state beside a definition: the state on the left, the
      // definition on the right (one column on a narrow window, or for a proof state alone, or
      // in the infoview's panel, which is narrow).
      const wide = (typeof window !== 'undefined' && window.innerWidth) || 1024;
      const twoColumns = Boolean(goals) && !(this.currentData && this.currentData.bare) && wide >= 720 && !this.dock;
      this.container.classList.toggle('verso-two-col', twoColumns);

      const messages = (extras && extras.messages) || [];
      messagesEl.innerHTML = messages.map((m) => {
        const severity = ['error', 'warning', 'info'].includes(m.severity) ? m.severity : 'info';
        return `<div class="verso-message verso-message-${severity}"><span class="verso-message-kind">${severity}</span><pre>${esc(m.text)}</pre></div>`;
      }).join('');
      messagesEl.classList.toggle('verso-hidden', messages.length === 0);

      const helper = extras && extras.helper;
      const estimated = Boolean(this.currentData) && this.currentData.source !== 'lean';
      // In the infoview's panel, Lean is started and stopped at the top: the hover says only
      // whether it was estimated, and offers no run of its own.
      const status = this.dock ? (estimated ? { text: 'Estimated: not checked by Lean' } : null)
        : helper ? this.helperStatus(helper, estimated) : null;
      if (status) {
        barText.textContent = status.text;
        barBtn.textContent = status.button || '';
        barBtn.classList.toggle('verso-hidden', !status.button || !helper || typeof helper.run !== 'function');
        bar.classList.remove('verso-hidden');
      } else {
        bar.classList.add('verso-hidden');
      }
    }

    /**
     * The proof state at a tactic. With the goals before it known, what it changed is marked as
     * in Lean's infoview: new in green in the goals after it, gone in red in the goals before it
     * (`goalsSide` picks which). `stepper` (`{go(delta)}`) moves to the proof's other tactics.
     */
    renderGoals(goals, stepper, titleEl, bodyEl) {
      const esc = (str) => String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
      const differ = typeof window !== 'undefined' && window.LeanGoalDiff;
      const compared = differ && !goals.at && Array.isArray(goals.before) ? differ.diffStates(goals.before, goals.goals) : null;
      // (A tactic that left the state as it was: its goals, said to be unchanged.)
      const unchanged = Boolean(compared && !compared.changed);
      const diff = unchanged ? null : compared;
      const side = diff && this.goalsSide === 'before' ? 'before' : 'after';
      const steps = stepper && goals.steps > 1 && goals.step >= 0
        ? `<span class="verso-steps"><button class="verso-step-btn" data-step="-1" title="Previous tactic (←)"${goals.step === 0 ? ' disabled' : ''}>◀</button>` +
          `<span class="verso-step-count">${goals.step + 1}/${goals.steps}</span>` +
          `<button class="verso-step-btn" data-step="1" title="Next tactic (→)"${goals.step === goals.steps - 1 ? ' disabled' : ''}>▶</button></span>`
        : '';
      const switcher = diff
        ? `<span class="verso-goal-sides">${['before', 'after'].map((s) =>
          `<button class="verso-side-btn${s === side ? ' verso-side-active' : ''}" data-side="${s}">${s === 'before' ? 'Before' : 'After'}</button>`).join('')}</span>`
        : '';
      const label = goals.at ? 'Goal at' : side === 'before' ? 'Before' : 'After';
      titleEl.innerHTML = `${steps}<span class="verso-goals-label">${label} <code class="verso-inline-code">${esc(goals.tactic)}</code>` +
        `${unchanged ? ' <span class="verso-goals-same">(no change)</span>' : ''}</span>${switcher}`;

      const shown = diff ? (side === 'before' ? diff.before : diff.after) : null;
      const texts = side === 'before' ? goals.before : goals.goals;
      if (!texts.length) {
        bodyEl.innerHTML = '<span class="verso-no-goals">No goals</span>';
      } else if (shown) {
        const mark = side === 'before' ? 'del' : 'ins';
        bodyEl.innerHTML = shown.map((view) => `<span class="verso-goal verso-goal-${view.status}">${view.lines.map((line) => {
          const wholeLine = line.status === 'ins' || line.status === 'del';
          const body = line.segments.map((seg) => (seg.changed && !wholeLine
            ? `<span class="verso-diff-${mark}">${this.highlightLean(seg.text, { binders: false })}</span>`
            : this.highlightLean(seg.text, { binders: false }))).join('');
          // A line that changed only by losing something (shown on the other side): a side bar.
          const touched = line.status === 'changed' && !line.segments.some((seg) => seg.changed);
          const cls = wholeLine ? ` verso-diff-line-${mark}` : touched ? ` verso-diff-line-touched-${mark}` : '';
          return `<span class="verso-goal-line${cls}">${body}</span>`;
        }).join('')}</span>`).join('');
      } else {
        bodyEl.innerHTML = texts.map((goal) => `<span class="verso-goal">${goal.split('\n').map((line) =>
          `<span class="verso-goal-line">${this.highlightLean(line, { binders: false })}</span>`).join('')}</span>`).join('');
      }
      this.goalsDiffShown = Boolean(diff && diff.changed);
      if (this.goalsDiffShown) this.revealChange(bodyEl);
    }

    /**
     * Scroll what a tactic changed into view: with many hypotheses, the changed target is
     * below the fold of the goals (or of their column).
     */
    revealChange(bodyEl) {
      const run = () => {
        const first = bodyEl.querySelector && bodyEl.querySelector('.verso-diff-ins, .verso-diff-del, .verso-diff-line-ins, ' +
          '.verso-diff-line-del, .verso-diff-line-touched-ins, .verso-diff-line-touched-del');
        if (!first || !first.getBoundingClientRect) return;
        for (let el = first.parentElement; el && el !== this.container; el = el.parentElement) {
          if (el.scrollHeight <= el.clientHeight + 1 || !/auto|scroll/.test(getComputedStyle(el).overflowY)) continue;
          const box = el.getBoundingClientRect();
          const at = first.getBoundingClientRect();
          if (at.top < box.top || at.bottom > box.bottom) el.scrollTop += at.top - box.top - Math.min(48, box.height / 3);
          return;
        }
      };
      if (typeof requestAnimationFrame === 'function') requestAnimationFrame(run); else run();
    }

    /** The status row's words (and button) for a state of the local helper, or null for no row. */
    helperStatus(helper, estimated) {
      const lead = estimated ? 'Estimated. ' : '';
      switch (helper.state) {
        case 'ready':
          return estimated ? { text: "Estimated: Lean's data has no hover for this spot." } : null;
        case 'missing':
          return { text: `${lead}Lean has not run on this file.`, button: 'Run Lean' };
        case 'pending': {
          const count = helper.total > 1 && helper.phase === 'elaborating' ? ` (${helper.done}/${helper.total})` : '';
          return { text: `Lean is running: ${helper.message || 'starting'}${count}` };
        }
        case 'not_allowed':
          return { text: `${lead}The helper may not run code from ${helper.repo || 'this repository'} yet.`, button: 'Allow and run' };
        case 'error':
          return { text: `Lean failed on this file: ${helper.error || 'unknown error'}`, button: 'Retry' };
        case 'offline':
          return { text: `${lead}The Lean helper is not running.` };
        case 'unauthorized':
          return { text: `${lead}The helper rejected the token (see the extension's options).` };
        default:
          return null;
      }
    }

    /** Move to another tactic of the proof shown (the tooltip stays open while stepping). */
    step(delta) {
      const stepper = this.currentExtras && this.currentExtras.stepper;
      if (!stepper || typeof stepper.go !== 'function') return;
      if (!this.isPinned) this.togglePin();
      stepper.go(delta);
    }

    /** Update what Lean's run adds while the tooltip stays open (progress of a run). */
    setExtras(extras) {
      if (!this.isVisible()) return;
      this.renderExtras(extras);
    }

    /**
     * Show a lightweight loading indicator at the hovered token.
     */
    showLoading(token, boundingRect, shade) {
      this.clearHideTimer();
      this.setShade(shade);
      if (this.dock && this.isVisible() && !this.loadingCard) {
        // Docked, the hover shown stays until the next one is ready; a bar says one is coming.
        this.container.classList.add('verso-loading');
        return;
      }
      this.loadingCard = true;
      this.currentData = null;
      const titleEl = this.container.querySelector('#verso-title');
      const kindEl = this.container.querySelector('#verso-kind');
      const sigEl = this.container.querySelector('#verso-signature');
      const docEl = this.container.querySelector('#verso-docstring');
      const prBanner = this.container.querySelector('#verso-pr-banner');
      const docsLink = this.container.querySelector('#verso-docs-link');

      titleEl.textContent = token;
      kindEl.textContent = '...';
      kindEl.className = 'verso-kind-badge';
      sigEl.parentElement.classList.remove('verso-hidden');
      this.renderExtras(null);
      sigEl.innerHTML = '<span class="verso-loading-spinner"></span> Resolving definition via Loogle...';
      docEl.innerHTML = '';
      prBanner.classList.add('verso-hidden');
      docsLink.classList.add('verso-hidden');

      this.positionTooltip(boundingRect);
      this.container.classList.remove('verso-hidden');
      this.container.classList.add('verso-visible');
      this.syncDock();
    }

    /**
     * Calculate optimal position for tooltip avoiding viewport boundaries and cursor overlap.
     */
    positionTooltip(rect) {
      if (!rect || this.dock) return;
      const card = this.container.querySelector('.verso-tooltip-card');
      const cardWidth = (card && card.offsetWidth) || 440;
      const viewportWidth = window.innerWidth;
      const viewportHeight = window.innerHeight;

      const margin = 12;
      const verticalGap = 10;
      let left = rect.left;

      // The card goes below the hovered code when it fits there, else on the side with more
      // room; if it is taller than that room, it is kept inside the window and scrolls.
      if (card && card.style) card.style.maxHeight = '';
      const natural = Math.min(card ? card.offsetHeight || 280 : 280, 480);
      const below = viewportHeight - rect.bottom - verticalGap - margin;
      const above = rect.top - verticalGap - margin;
      const placeBelow = natural <= below || below >= above;
      const room = Math.max(140, placeBelow ? below : above);
      const height = Math.min(natural, room);
      if (card && card.style && natural > room) card.style.maxHeight = `${Math.floor(room)}px`;
      const top = placeBelow ? rect.bottom + verticalGap : Math.max(margin, rect.top - verticalGap - height);

      // Check horizontal clearance:
      if (left + cardWidth > viewportWidth - margin) {
        left = viewportWidth - cardWidth - margin;
      }
      if (left < margin) {
        left = margin;
      }

      this.container.style.left = `${Math.round(left)}px`;
      this.container.style.top = `${Math.round(top)}px`;
    }

    /**
     * Keep the card where it is, by its top-left corner, while what it shows changes (stepping
     * through a proof: ◀ ▶ stay under the pointer). It stays inside the window: it moves left only
     * to make room for its widest, and scrolls when it is taller than the room below its top.
     */
    keepPlace() {
      if (this.dock) return;
      const left = parseFloat(this.container.style.left);
      const top = parseFloat(this.container.style.top);
      if (!Number.isFinite(left) || !Number.isFinite(top)) return;
      const card = this.container.querySelector('.verso-tooltip-card');
      const margin = 12;
      const viewportWidth = window.innerWidth;
      const viewportHeight = window.innerHeight;
      const style = typeof getComputedStyle === 'function' ? getComputedStyle(this.container) : null;
      const widest = (style && parseFloat(style.maxWidth)) || (card && card.offsetWidth) || 460;
      const x = left + widest > viewportWidth - margin ? Math.max(margin, viewportWidth - margin - widest) : left;
      if (card && card.style) card.style.maxHeight = '';
      const natural = Math.min(card ? card.offsetHeight || 280 : 280, 480);
      // (Moved up only when little of it would show below its top.)
      const least = Math.min(natural, 240);
      const y = viewportHeight - margin - top < least ? Math.max(margin, viewportHeight - margin - least) : top;
      const room = viewportHeight - margin - y;
      if (card && card.style && natural > room) card.style.maxHeight = `${Math.floor(room)}px`;
      this.container.style.left = `${Math.round(x)}px`;
      this.container.style.top = `${Math.round(y)}px`;
    }

    /**
     * Toggle pinned state.
     */
    togglePin() {
      this.isPinned = !this.isPinned;
      const pinBtn = this.container.querySelector('#verso-pin-btn');
      if (this.isPinned) {
        pinBtn?.classList.add('verso-btn-active');
        this.container.classList.add('verso-pinned');
      } else {
        pinBtn?.classList.remove('verso-btn-active');
        this.container.classList.remove('verso-pinned');
      }
    }

    /**
     * Schedule closing the tooltip with debounce.
     */
    scheduleHide(delay = 200) {
      // (Docked, a hover stays when the pointer moves away.)
      if (this.isPinned || this.dock) return;
      this.clearHideTimer();
      this.hideTimer = setTimeout(() => {
        this.hide(false);
      }, delay);
    }

    /**
     * Clear scheduled hide timer.
     */
    clearHideTimer() {
      if (this.hideTimer) {
        clearTimeout(this.hideTimer);
        this.hideTimer = null;
      }
    }

    /**
     * Immediately hide tooltip.
     */
    hide(force = false) {
      if (this.isPinned && !force) return;
      this.clearHideTimer();
      if (this.dock && !force && this.isVisible() && !this.loadingCard) {
        // Docked: a spot with nothing to show leaves the hover shown, and its code shaded.
        this.container.classList.remove('verso-loading');
        this.setShade(this.shownShade);
        return;
      }
      this.setShade(null);
      this.shownShade = null;
      this.loadingCard = false;
      this.isPinned = false;
      const pinBtn = this.container.querySelector('#verso-pin-btn');
      pinBtn?.classList.remove('verso-btn-active');
      this.container.classList.remove('verso-pinned');
      this.container.classList.remove('verso-loading');
      this.container.classList.remove('verso-visible');
      this.container.classList.add('verso-hidden');
      this.syncDock();
    }

    /**
     * Check if currently visible.
     */
    isVisible() {
      return this.container && !this.container.classList.contains('verso-hidden');
    }

    /**
     * Single-pass syntax highlighter for Lean 4 signatures.
     * Prevents regex corruption of injected HTML tags.
     */
    highlightLean(code, opts = {}) {
      if (!code) return '';
      const binders = opts.binders !== false;

      function escapeHtml(str) {
        return str
          .replace(/&/g, '&amp;')
          .replace(/</g, '&lt;')
          .replace(/>/g, '&gt;');
      }

      // Regex matching distinct Lean token types in priority order:
      // 1. Comments: -- ... or /- ... -/
      // 2. Strings: "..."
      // 3. Keywords: def, theorem, lemma, etc.
      // 4. Typeclass Instance Binders: [...]
      // 5. Implicit Binders: {...}
      // 6. Symbols & Operators: :=, →, ∀, ∃, etc.
      const tokenRegex = /(--[^\n]*|\/-[\s\S]*?-\/)|("(?:\\[\s\S]|[^"\\])*")|(\b(?:def|theorem|lemma|axiom|inductive|structure|class|instance|where|by|have|let|suffices|show|fun|match|with|if|then|else|namespace|section|variable|include|omit|open|universe|set_option)\b)|(@\[[^\]]*\])|(\[[^\]]+\])|(\{[^}]+\})|(:=|→|∀|∃|∧|∨|¬|↔|≤|≥|=|≠|∈|⊆|∪|∩|:)/g;

      let result = '';
      let lastIndex = 0;
      let match;

      while ((match = tokenRegex.exec(code)) !== null) {
        // Append any text between matched tokens (escaped)
        if (match.index > lastIndex) {
          result += escapeHtml(code.slice(lastIndex, match.index));
        }

        const [full, comment, str, kw, attr, inst, implicit, sym] = match;

        if (comment) {
          result += `<span class="v-comment">${escapeHtml(comment)}</span>`;
        } else if (str) {
          result += `<span class="v-str">${escapeHtml(str)}</span>`;
        } else if (kw) {
          result += `<span class="v-kw">${escapeHtml(kw)}</span>`;
        } else if (attr) {
          // An attribute (`@[simp]`, `@[expose]`), not an instance argument.
          result += `<span class="v-attr">${escapeHtml(attr)}</span>`;
        } else if (inst || implicit) {
          if (binders) {
            result += `<span class="${inst ? 'v-inst' : 'v-implicit'}">${escapeHtml(full)}</span>`;
          } else {
            // Highlight inside the brackets as ordinary code.
            result += full[0] + this.highlightLean(full.slice(1, -1), { binders: false }) + full[full.length - 1];
          }
        } else if (sym) {
          result += `<span class="v-sym">${escapeHtml(sym)}</span>`;
        }

        lastIndex = tokenRegex.lastIndex;
      }

      if (lastIndex < code.length) {
        result += escapeHtml(code.slice(lastIndex));
      }

      return result;
    }

    /**
     * Markdown renderer for docstrings. Code (fenced blocks, inline spans) is set aside first,
     * so `a * b` is not emphasis; lists (also indented, as in Lean's notation docs) come before
     * emphasis, so `* item` is not either.
     */
    renderMarkdown(text, opts = {}) {
      if (!text) return '';
      const esc = (str) => str.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
      const kept = [];
      const keep = (html) => `\u0000${kept.push(html) - 1}\u0000`;
      let src = text.replace(/```(?:lean)?[ \t]*\n?([\s\S]*?)```/g,
        (m, code) => `\n\n${keep(`<pre class="verso-code-block">${this.highlightLean(code.replace(/\s+$/, ''))}</pre>`)}\n\n`);
      src = src.replace(/`([^`\n]+)`/g, (m, code) => keep(`<code class="verso-inline-code">${esc(code)}</code>`));
      let html = esc(src);

      // (In hard-wrapped Markdown, a list item's indented continuation lines belong to it.)
      if (opts.softWrap) {
        html = html.replace(/^([ \t]*[*-][ \t]+.*)((?:\n[ \t]{2,}(?![*-][ \t])\S.*)+)/gm,
          (m, first, rest) => first + rest.replace(/\n[ \t]+/g, ' '));
      }

      // Bullet lists (`* item`, `- item`, indented or not), each list its own block.
      html = html.replace(/^[ \t]*[*-][ \t]+(.+)$/gm, '<li>$1</li>');
      html = html.replace(/(?:<li>.*<\/li>\n?)+/g, (m) => `\n\n<ul>${m.replace(/\n/g, '')}</ul>\n\n`);

      // Bold **…**, italic *…*
      html = html.replace(/\*\*([^*\n]+)\*\*/g, '<strong>$1</strong>');
      html = html.replace(/(^|[^\w*])\*(?=\S)([^*\n]*?\S)\*(?![\w*])/g, '$1<em>$2</em>');

      // Paragraphs
      html = html.split(/\n{2,}/).map(p => {
        p = p.trim();
        if (!p) return '';
        const block = /^<ul/.test(p) || (/^\u0000\d+\u0000$/.test(p) && kept[Number(p.slice(1, -1))].startsWith('<pre'));
        // (Lean's own docstrings are hard-wrapped Markdown, where a line end is a space.)
        return block ? p : `<p>${p.replace(/\n/g, opts.softWrap ? ' ' : '<br>')}</p>`;
      }).join('');

      return html.replace(/\u0000(\d+)\u0000/g, (m, i) => kept[Number(i)]);
    }
  }

  window.VersoTooltipView = new VersoTooltipView();
})();
