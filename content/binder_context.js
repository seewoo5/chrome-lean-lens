/**
 * Locals and the page around a hover: the binder of a hovered name in its declaration
 * (written, or inferred from `intro`, `obtain`, `fun`, a binder's use), anonymous
 * projections, named arguments, replaying `rw … at h` for a hypothesis' current type, and
 * where the hovered line lives (repository, commit, path, line) for file-level lookups.
 *
 * Terms come from lean_terms.js (`LeanTerms`); gap hovers are in term_hover.js. The service
 * worker loads this file too, for `variable` lookups.
 */

(function () {
  const {
    CLOSERS, OPENERS, annotateText, appParts, applicationHead, applicationTypeFrom, applyArgs, codomainOf,
    conclusionOf, displayType, domainOf, leanSignature, matchClose, matchTerm, namesIn, parseTerm,
    peelSignature, receiverResultType, replaceWord, residualSignature, rewriteTerm, ruleEquationFrom,
    showTerm, splitApp, splitTop, stripParens, tCore, topColon, topLevelIndexOf, typeHead, useOf
  } = (typeof window !== 'undefined' ? window : self).LeanTerms;

  const DECL_START = /^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|public|noncomputable|scoped|partial|nonrec|unsafe|meta)\s+)*(?:theorem|lemma|def|instance|example|abbrev|opaque|structure|class|inductive)\b/;

  const NAME_CHARS = "[^\\s:()\\[\\]{}⦃⦄⟨⟩,]+";

  const BINDER_NAMES = new RegExp(`^\\s*(${NAME_CHARS}(?:\\s+${NAME_CHARS})*)\\s*:(?!=)`);

  // A binder name: an identifier on the same line (not `=>`, not the next line's words).
  const BINDER_IDENT = "[A-Za-z_\\u0370-\\u03FF\\u1F00-\\u1FFF][\\w'!?\\u0370-\\u03FF\\u1F00-\\u1FFF\\u2080-\\u209C]*";
  const BINDER_KW = new RegExp(`(?:\\bfun|λ|∀|∃!?|Π|∑'?|∏'?|⋃|⋂|⨆|⨅|∫|∮|⨂\\[[^\\]\\n]*\\]|⨁)[ \\t]+(${BINDER_IDENT}(?:[ \\t]+${BINDER_IDENT})*)[ \\t]*:(?!=)`, 'g');

  // `have h : T`, `have h (x) : T`, `by_cases h : P`, `generalize h : e = x`, …
  const LOCAL_DECL = new RegExp(`\\b(?:have|haveI|replace|let|set|suffices|obtain|by_cases!?|generalize|wlog|if)\\s+(${NAME_CHARS})((?:\\s*[({\\[⦃][^(){}\\[\\]⦃⦄]*[)}\\]⦄])*)\\s*:(?!=)`, 'g');

  /** End of an unbracketed binder's type: first top-level `=>`, `↦` or `,`. */
  function binderBodyStart(text, start) {
    let depth = 0;
    for (let i = start; i < text.length; i++) {
      const ch = text[i];
      if (OPENERS[ch]) depth++;
      else if (CLOSERS.has(ch)) { if (depth === 0) return i; depth--; }
      else if (depth === 0 && (ch === ',' || ch === '↦' || text.startsWith('=>', i) || text.startsWith(' in ', i))) return i;
    }
    return text.length;
  }

  /** End of a `have h : T` type: first top-level `:=`, ` by`, or end of line. */
  function localDeclTypeEnd(text, start) {
    // The type may continue on following lines that are indented deeper than the `have`.
    const lineStart = text.lastIndexOf('\n', start - 1) + 1;
    const indent = (text.slice(lineStart).match(/^[ \t]*/) || [''])[0].length;
    let depth = 0;
    for (let i = start; i < text.length; i++) {
      const ch = text[i];
      if (OPENERS[ch]) depth++;
      else if (CLOSERS.has(ch)) depth = Math.max(0, depth - 1);
      else if (ch === '\n') {
        const nextIndent = (text.slice(i + 1).match(/^[ \t]*/) || [''])[0].length;
        if (depth === 0 && nextIndent <= indent) return i;
      } else if (depth === 0) {
        if (text.startsWith(':=', i)) return i;
        if (/^\sby\b/.test(text.slice(i, i + 4))) return i;
        if (/^\sthen\b/.test(text.slice(i, i + 6))) return i;
        if (/^\swith\b/.test(text.slice(i, i + 6))) return i; // `wlog h : P with H`
      }
    }
    return text.length;
  }

  /**
   * Find the declared type of local `name` in `text` (source order).
   * The last binder wins, as it shadows earlier ones.
   */
  function findBinderType(name, text) {
    const r = findBinder(name, text);
    return r ? r.type : null;
  }

  const STRUCTURE_START = /^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|public|noncomputable)\s+)*(?:structure|class)\b/;
  // A field line of a structure: `  lo hi : ℝ` (not `field := value`).
  const FIELD_LINE = /^[ \t]+([^\s:()⟨⟩/-][^\s:()⟨⟩]*(?:[ \t]+[^\s:()⟨⟩]+)*)[ \t]*:(?!=)[ \t]*(.+)$/gm;

  /** Like findBinderType, plus where the binder is: { type, pos }. */
  /** End of a declaration header (its top-level ` : `, `:=`, `where` or `|`), or -1 if `text` isn't a declaration. */
  function headerEnd(text) {
    const m = text.match(DECL_START);
    if (!m) return -1;
    let depth = 0;
    for (let i = m[0].length; i < text.length; i++) {
      const ch = text[i];
      if (OPENERS[ch]) depth++;
      else if (CLOSERS.has(ch)) depth = Math.max(0, depth - 1);
      else if (depth === 0) {
        if (ch === ':' || ch === '|') return i;
        if (/^\swhere\b/.test(text.slice(i, i + 7))) return i;
      }
    }
    return text.length;
  }

  /**
   * The declared type when `text` ends at the start of a declaration's value
   * (`def congr … : A ≃ₛₗ[σ] B :=` then `.ofLinearMap`), or null.
   */
  function declaredTypeBefore(text) {
    const m = (text || '').match(/:=\s*$/);
    if (!m) return null;
    const hdr = headerEnd(text);
    if (hdr <= 0 || text[hdr] !== ':') return null;
    const type = text.slice(hdr + 1, m.index).trim();
    return type && topLevelIndexOf(type, ':=') === -1 ? type : null;
  }

  /** Is the `(` at `i` (after the header) a binder, i.e. preceded by `fun`/`∀`/… possibly through other binder groups? */
  function binderKeywordBefore(text, i) {
    let k = i - 1;
    for (;;) {
      while (k >= 0 && /\s/.test(text[k])) k--;
      if (k < 0) return false;
      if (CLOSERS.has(text[k])) {
        // Skip a previous group `(x : T)` back to its opener.
        let depth = 0;
        for (; k >= 0; k--) {
          if (CLOSERS.has(text[k])) depth++;
          else if (OPENERS[text[k]]) { depth--; if (depth === 0) break; }
        }
        k--;
        continue;
      }
      return /(?:\bfun|λ|∀|∃!?|Π|∑'?|∏'?|⋃|⋂|⨆|⨅|∫|∮|⨂|⨁|\bhave\s+[^\s:()]+|\blet\s+[^\s:()]+)$/.test(text.slice(Math.max(0, k - 20), k + 1));
    }
  }

  function findBinder(name, text) {
    if (!name || !text) return null;
    let found = null;
    let foundPos = -1;
    const hdrEnd = headerEnd(text);
    // A structure's fields are in scope in the later ones (`lo_lt_hi : lo < hi`).
    const fieldsFrom = STRUCTURE_START.test(text) ? text.search(/\swhere\b/) : -1;
    // (A field's binders: `  (h : P)` or `  edgePerm_edgePerm (d : D) : …`.)
    const startsLine = (i) => /(^|\n)[ \t]*(?:[^\s:()⟨⟩{}[\]]+[ \t]+)?(?:[({⦃[][^\n]*[)}⦄\]][ \t]*)*$/.test(text.slice(Math.max(0, i - 300), i));

    for (let i = 0; i < text.length; i++) {
      const ch = text[i];
      if (ch !== '(' && ch !== '{' && ch !== '⦃' && ch !== '[') continue;
      const m = text.slice(i + 1).match(BINDER_NAMES);
      if (!m) continue;
      const names = m[1].trim().split(/\s+/);
      if (!names.includes(name)) continue;
      // `(map f p : Set _)` in a proof is a type ascription, not a binder (a field `(h : P)` is one).
      if (ch === '(' && hdrEnd !== -1 && i > hdrEnd && !binderKeywordBefore(text, i) &&
          !(fieldsFrom !== -1 && i > fieldsFrom && startsLine(i))) continue;
      let close = matchClose(text, i);
      // A binder whose type continues past the hovered line: take what we have.
      if (close === -1) close = text.length;
      found = text.slice(i + 1 + m[0].length, close);
      // Set-builder `{z : ℂ | P z}` / subtype `{x : α // P x}`: the type ends at ` | ` / ` // `.
      if (ch === '{') {
        const bar = found.search(/ \| | \/\/ /);
        if (bar !== -1) found = found.slice(0, bar);
      }
      foundPos = i;
    }

    if (fieldsFrom !== -1) {
      FIELD_LINE.lastIndex = fieldsFrom;
      let fm;
      while ((fm = FIELD_LINE.exec(text)) !== null) {
        if (fm.index > foundPos && fm[1].trim().split(/\s+/).includes(name)) {
          found = fm[2].replace(/\s+:=[\s\S]*$/, '').trim();
          foundPos = fm.index;
        }
      }
    }

    LOCAL_DECL.lastIndex = 0;
    let lm;
    while ((lm = LOCAL_DECL.exec(text)) !== null) {
      if (lm[1] !== name) continue;
      const start = lm.index + lm[0].length;
      // Keep whichever occurrence comes later in the text.
      if (lm.index > foundPos) {
        found = text.slice(start, localDeclTypeEnd(text, start));
        const params = (lm[2] || '').trim();
        if (params) found = `∀ ${params}, ${found.trim()}`;
        foundPos = lm.index;
      }
    }

    // Unbracketed binders: `fun g : T => …`, `∀ x y : T, …`, `∃ x : T, …`.
    BINDER_KW.lastIndex = 0;
    let bm;
    while ((bm = BINDER_KW.exec(text)) !== null) {
      if (!bm[1].trim().split(/\s+/).includes(name)) continue;
      if (bm.index <= foundPos) continue;
      const start = bm.index + bm[0].length;
      found = text.slice(start, binderBodyStart(text, start));
      foundPos = bm.index;
    }

    return found ? { type: found.replace(/\s+/g, ' ').trim(), pos: foundPos } : null;
  }

  /**
   * For text ending in `(…).`, the expression inside the parentheses (which may span
   * lines); null otherwise.
   */
  function parenReceiver(prefixText) {
    const t = (prefixText || '').replace(/\s+$/, '');
    if (!t.endsWith(').')) return null;
    const close = t.length - 2;
    let depth = 0;
    for (let k = close; k >= 0; k--) {
      const ch = t[k];
      if (ch === ')') depth++;
      else if (ch === '(') {
        depth--;
        if (depth === 0) return t.slice(k + 1, close).trim();
      }
    }
    return null;
  }

  /**
   * Namespace that `receiver.field` resolves in, given the declaration text up to the hover.
   */
  function inferReceiverNamespace(receiver, contextText) {
    const binderType = localType(receiver, contextText);
    if (!binderType) return null;
    const resolveVar = (v) => {
      if (v === receiver) return null;
      const vt = findBinderType(v, contextText);
      return vt ? typeHead(vt, null) : null;
    };
    return typeHead(binderType, resolveVar);
  }

  /** Lines (source order) from the enclosing declaration's start through `currentIdx`. */
  function declarationContext(rawLines, currentIdx, maxLines = 400) {
    // Hunk headers carry git's enclosing-function context after the second `@@`.
    const lines = rawLines.map(l => l.replace(/^@@[^@]*@@\s?/, ''));
    const from = Math.max(0, currentIdx - maxLines);
    let start = from;
    for (let i = currentIdx; i >= from; i--) {
      if (DECL_START.test(lines[i])) { start = i; break; }
    }
    // `have h :` with its type on the next lines: those lines too, up to its `:=`.
    let end = currentIdx;
    if (/(?:^|\s):\s*$/.test(lines[currentIdx] || '')) {
      const indent = (lines[currentIdx].match(/^\s*/) || [''])[0].length;
      for (let j = currentIdx + 1; j < lines.length && j <= currentIdx + 8; j++) {
        if (!lines[j].trim() || (lines[j].match(/^\s*/) || [''])[0].length <= indent) break;
        end = j;
        if (/:=|\bby\s*$/.test(lines[j])) break;
      }
    }
    return lines.slice(start, end + 1).join('\n');
  }

  const LINE_SELECTORS = [
    '.blob-code-inner',
    '[data-tag="diff-line"]',
    '[data-component="diff-line"]',
    '.react-code-text',
    'td.blob-code'
  ];

  const FILE_SELECTORS =
    '.file, .js-file, [data-details-container-group="file"], [data-component="diff-file"], ' +
    '[data-tag="diff-entry"], section[data-file-path], div[data-file-path], table, pre';

  function isDeletion(el) {
    return el.getAttribute('data-code-marker') === '-' ||
      (el.classList && (el.classList.contains('blob-code-deletion') || el.classList.contains('diff-line-deletion'))) ||
      Boolean(el.closest && el.closest('.blob-code-deletion, .diff-line-deletion'));
  }

  /**
   * The lines of the hovered DOM node's file in the diff, with the hovered line's index:
   * { lines, idx } or null. Deleted lines are skipped unless the hover is on one.
   */
  function domLines(node) {
    const d = domLineEls(node);
    return d ? { lines: d.els.map(d.text), idx: d.idx } : null;
  }

  /** Like `domLines`, with the line elements and a reader: { els, idx, text(el) } or null. */
  function domLineEls(node) {
    const el = node && (node.nodeType === 1 ? node : node.parentElement);
    if (!el || !el.closest) return null;
    for (const sel of LINE_SELECTORS) {
      const lineEl = el.closest(sel);
      if (!lineEl) continue;
      const fileEl = lineEl.closest(FILE_SELECTORS) || document;
      const onDeletion = isDeletion(lineEl);
      const all = Array.from(fileEl.querySelectorAll(sel)).filter(l => l === lineEl || isDeletion(l) === onDeletion);
      const idx = all.indexOf(lineEl);
      if (idx === -1) continue;
      return { els: all, idx, text: (l) => l.textContent || '' };
    }
    return rowLineEls(el);
  }

  /**
   * On or below a `#doc` line in view (a Verso document)? 'prose', or 'code' in a ```lean
   * block; null when no `#doc` line is in view at or above the node.
   */
  function versoAbove(node) {
    const d = domLines(node);
    if (!d) return null;
    const clean = (l) => l.replace(/^\n+/, '').replace(/^[+-](?!-)/, '');
    let doc = -1;
    for (let k = d.idx; k >= 0 && doc === -1; k--) if (/^#doc\b/.test(clean(d.lines[k]))) doc = k;
    const scanner = scope.LeanPRScanner;
    if (doc === -1 || !scanner || !scanner.versoRegions) return doc === -1 ? null : 'prose';
    const r = scanner.versoRegions(d.lines.slice(doc, d.idx + 1).map(clean).join('\n'));
    const line = d.idx - doc + 1;
    return r.fences.some(([a, b]) => line > a && line < b) ? 'code' : 'prose';
  }

  /** Declaration text around the hovered DOM node, read from the diff. */
  function contextFromDom(node) {
    const d = domLines(node);
    return d ? declarationContext(d.lines, d.idx) : '';
  }

  const ROW_SEL = 'tr, [role="row"]';

  const CELL_SEL = 'td, th, [role="gridcell"], [role="cell"]';

  const DELETION_HINT = /\b[\w-]*(deletion|deleted|removed)\b/i;

  function rowIsDeletion(row, cell) {
    if (!cell) return false;
    if (cell.getAttribute('data-code-marker') === '-') return true;
    for (let e = cell; e && e !== row.parentElement; e = e.parentElement) {
      if (typeof e.className === 'string' && DELETION_HINT.test(e.className)) return true;
    }
    // Newer views mark the line inside the cell: `<code class="… deletion">`.
    for (const d of cell.querySelectorAll('[class]')) {
      if (typeof d.className === 'string' && DELETION_HINT.test(d.className)) return true;
    }
    const marker = cell.querySelector('.diff-text-marker');
    return Boolean(marker && marker.textContent.trim() === '-');
  }

  /** Code text of a diff cell, without a rendered `+`/`-` marker. */
  function cellCodeText(cell) {
    const inner = cell.querySelector('.diff-text-inner, .blob-code-inner');
    return inner ? inner.textContent || '' : stripMarker(cell.textContent || '');
  }

  /** Strip a diff marker GitHub may render as text (`+theorem …`, `-  exact …`). */
  function stripMarker(text) {
    return text.replace(/^\n+/, '').replace(/^\+/, '').replace(/^-(?!-)/, '');
  }

  /** Up to `span` lines of the same diff column (and side) before and after the hovered row. */
  function nearbyRowLines(el, span) {
    const row = el.closest(ROW_SEL);
    const cell = el.closest(CELL_SEL);
    if (!row || !cell) return null;
    const cellsOf = (r) => Array.from(r.children).filter(c => c.matches(CELL_SEL));
    const col = cellsOf(row).indexOf(cell);
    if (col === -1) return null;
    const onDeletion = rowIsDeletion(row, cell);
    const take = (next) => {
      const out = [];
      for (let r = next(row); r && out.length < span; r = next(r)) {
        const c = cellsOf(r)[col];
        if (c && rowIsDeletion(r, c) === onDeletion) out.push(c);
      }
      return out;
    };
    const before = take(r => r.previousElementSibling).reverse();
    const after = take(r => r.nextElementSibling);
    const cells = [...before, cell, ...after];
    return { lines: cells.map(cellCodeText), cells, idx: before.length };
  }

  function rowLineEls(el) {
    const row = el.closest(ROW_SEL);
    const cell = el.closest(CELL_SEL);
    if (!row || !cell) return null;
    const table = row.closest('table, [role="grid"], [role="table"]') || row.parentElement;
    if (!table) return null;
    const cellsOf = (r) => Array.from(r.children).filter(c => c.matches(CELL_SEL));
    const col = cellsOf(row).indexOf(cell);
    if (col === -1) return null;
    const onDeletion = rowIsDeletion(row, cell);

    const cells = [];
    let idx = -1;
    for (const r of table.querySelectorAll(ROW_SEL)) {
      if (r.closest('table, [role="grid"], [role="table"]') !== table && r !== row) continue;
      const c = cellsOf(r)[col];
      if (!c) continue;
      if (r !== row && rowIsDeletion(r, c) !== onDeletion) continue;
      if (r === row) idx = cells.length;
      cells.push(c);
    }
    return idx === -1 ? null : { els: cells, idx, text: cellCodeText };
  }

  // --- Local variables: show the type of a hovered binder ---

  /**
   * The names a binder list binds (`fun \u2026`, `\u2200 \u2026`): `x y`, `(x y : T)`, `{x}`, `\u27E8x, hx\u27E9`,
   * `x : T`, not the names inside the types.
   */
  function binderListNames(s) {
    const out = [];
    const c = topColon(s);
    if (c !== -1) s = s.slice(0, c); // `fun p : R \u00D7 \u03A0 i, s i \u21A6`
    // A binder predicate binds only the names before it: `∀ y ∈ edgeSet T,` binds `y`.
    for (let k = 0, depth = 0; k < s.length; k++) {
      if (OPENERS[s[k]]) depth++;
      else if (CLOSERS.has(s[k])) depth = Math.max(0, depth - 1);
      else if (depth === 0 && /\s/.test(s[k]) && /^\s(?:∈|∉|<|≤|>|≥|≠|⊆|⊂|⊇|⊃)\s/.test(s.slice(k, k + 3))) { s = s.slice(0, k); break; }
    }
    for (let k = 0; k < s.length;) {
      const ch = s[k];
      if (/\s/.test(ch)) { k++; continue; }
      if (OPENERS[ch]) {
        const close = matchClose(s, k);
        const inner = s.slice(k + 1, close === -1 ? s.length : close);
        if (ch === '\u27E8') out.push(...binderListNames(inner.replace(/,/g, ' ')));
        else if (ch !== '[') { const ic = topColon(inner); out.push(...binderListNames(ic === -1 ? inner : inner.slice(0, ic))); }
        k = close === -1 ? s.length : close + 1;
        continue;
      }
      const m = s.slice(k).match(/^[^\s({\u2983[\u27E8\u27E9)}\u2984\]]+/);
      if (!m) { k++; continue; }
      out.push(...namesIn(m[0]).filter(n => n !== '_'));
      k += m[0].length;
    }
    return out;
  }

  /** `ext` / `rintro` names: patterns only (`x`, `\u27E8x, y\u27E9`, `(x | y)`), not a term after the lemma `ext`. */
  const PATTERN_TEXT = /^[\s\w'\u27E8\u27E9,|()\u0370-\u03FF\u1F00-\u1FFF\u2080-\u209C!?]*$/;

  const patternNames = (s) => (PATTERN_TEXT.test(s) ? namesIn(s) : []);

  const PATTERN_NAME = /^[A-Za-z_\u0370-\u03FF\u1F00-\u1FFF][\w'!?\u0370-\u03FF\u1F00-\u1FFF\u2080-\u209C]*$/;
  /**
   * The names an `intro` / `rintro` / `obtain` / `choose` pattern binds, up to `;`:
   * `m n (h : T)`, `⟨x, hx⟩ | h`, `(rfl | ⟨a, b⟩)`, `- h` (the types are left out).
   */
  function introNames(s) {
    const out = [];
    const walk = (t) => {
      for (let k = 0; k < t.length;) {
        const ch = t[k];
        if (/[\s,|]/.test(ch)) { k++; continue; }
        if (ch === '⟨' || ch === '(') {
          const close = matchClose(t, k);
          const inner = t.slice(k + 1, close === -1 ? t.length : close);
          const c = ch === '(' ? topColon(inner) : -1;
          walk(c === -1 ? inner : inner.slice(0, c));
          k = close === -1 ? t.length : close + 1;
          continue;
        }
        const m = t.slice(k).match(/^[^\s,|⟨⟩()]+/);
        if (!m) { k++; continue; }
        const n = m[0].replace(/^@/, '');
        if (PATTERN_NAME.test(n) && n !== 'rfl') out.push(n);
        k += m[0].length;
      }
    };
    walk((s || '').split(/;|<;>/)[0]);
    return out;
  }

  // Constructors match arms name on their own (`| zero =>`); a lone lower-case name binds.
  const ARM_CONSTRUCTORS = new Set(['zero', 'succ', 'nil', 'cons', 'none', 'some', 'inl', 'inr', 'true', 'false', 'unit',
    'mk', 'intro', 'refl', 'rfl', 'ofNat', 'negSucc', 'head', 'tail', 'node', 'leaf', 'empty', 'insert', 'base', 'step',
    'pos', 'neg', 'lt', 'eq', 'gt', 'up', 'down', 'single', 'pair']);
  /**
   * The names a match / induction arm binds (`| succ n ih =>`, `| n + 1 =>`, `| @insert a s ha ih =>`,
   * `| ⟨a, b⟩ =>`, `| .succ n =>`): its variables, not its constructors.
   */
  function armNames(s) {
    const out = [];
    for (const part of splitTop(s || '', ',')) {
      const toks = part.trim().match(/[⟨(](?:[^⟨⟩()]|[⟨(][^⟨⟩()]*[⟩)])*[⟩)]|[@.]?[A-Za-z_\u0370-\u03FF\u1F00-\u1FFF][\w'!?.\u0370-\u03FF\u1F00-\u1FFF\u2080-\u209C]*|\S/g) || [];
      toks.forEach((t, i) => {
        if (/^[⟨(]/.test(t)) { out.push(...armNames(t.slice(1, -1))); return; }
        if (/^[@.]/.test(t) || !PATTERN_NAME.test(t)) return; // `@insert`, `.succ`, operators, numerals
        const applied = i === 0 && toks.length > 1 && /^[@.A-Za-z_⟨(\u0370-\u03FF\u1F00-\u1FFF]/.test(toks[1]);
        if (applied || (toks.length === 1 && (ARM_CONSTRUCTORS.has(t) || /^[A-Z]/.test(t)))) return;
        out.push(t);
      });
    }
    return out;
  }

  /**
   * The names `text` uses free: not bound in it by `fun`, `\u2200`/`\u2203`/`\u2211`/\u2026 , a set-builder, a
   * tactic (`intro x`, `obtain \u27E8x, hx\u27E9`, `have h`), a match case, a structure field's
   * arguments (`toFun x := \u2026`); not a named argument `(x := \u2026)` or a field `e.symm`.
   * Scopes are approximate: a binder reaches the end of its bracket group and of the lines
   * indented under it (a tactic's names: the rest of its tactic block).
   */
  function freeNamesInText(text) {
    text = (text || '').replace(/--[^\n]*/g, (c) => ' '.repeat(c.length));
    const starts = [0];
    for (let k = 0; k < text.length; k++) if (text[k] === '\n') starts.push(k + 1);
    const lineOf = (pos) => { let lo = 0, hi = starts.length - 1; while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (starts[mid] <= pos) lo = mid; else hi = mid - 1; } return lo; };
    const lineText = (j) => text.slice(starts[j], j + 1 < starts.length ? starts[j + 1] - 1 : text.length);
    // Indentation of a line's content (`\u00B7 tac` counts from `tac`).
    const indentOf = (j) => { const m = lineText(j).match(/^(\s*)(\u00B7\s+)?/); return m[1].length + (m[2] ? m[2].length : 0); };
    const blank = (j) => !lineText(j).trim();
    // End of the lines under line j: indented more (strict) or at least as much.
    const blockEnd = (j, strict) => {
      const ind = strict ? lineText(j).match(/^\s*/)[0].length : indentOf(j);
      let k = j + 1;
      while (k < starts.length && (blank(k) || (strict ? lineText(k).match(/^\s*/)[0].length > ind : lineText(k).match(/^\s*/)[0].length >= ind))) k++;
      return k < starts.length ? starts[k] : text.length;
    };
    const groupEnd = (pos) => {
      for (let k = pos, d = 0; k < text.length; k++) {
        if (OPENERS[text[k]]) d++;
        else if (CLOSERS.has(text[k])) { if (d === 0) return k; d--; }
      }
      return text.length;
    };
    const bound = [];
    const bind = (re, namesFn, scope) => {
      re.lastIndex = 0;
      let m;
      while ((m = re.exec(text)) !== null) {
        const names = namesFn(m[1]);
        if (!names.length) continue;
        const to = scope(m.index, lineOf(m.index), m);
        names.forEach(n => bound.push({ n, from: m.index, to }));
        if (m[0].length === 0) re.lastIndex++;
      }
    };
    const termScope = (pos, j) => Math.min(groupEnd(pos), blockEnd(j, true));
    const tacticScope = (pos, j) => blockEnd(j, false);
    const lineScope = (pos, j) => blockEnd(j, true);
    bind(/\bfun\b([^\n]*?)(?:=>|\u21A6)/g, binderListNames, termScope);
    bind(/(?:\u2200|\u2203!?|\u03A0|\u03BB|\u2211'?|\u220F'?|\u22C3|\u22C2|\u2A06|\u2A05|\u222B|\u222E|\u2A02\[[^\]\n]*\]|\u2A01)\s*([^,\n]*?)\s*(?:,|\bin\b|\u2208)/g, binderListNames, termScope);
    bind(/\{\s*([^:{}|]+?)\s*(?::[^|{}]*)?\|(?!\|)/g, namesIn, termScope);
    bind(/\{\s*([^:{}|/]+?)\s*(?::[^|{}/]*)?\/\/(?!\/)/g, namesIn, termScope); // a subtype `{x // P x}`
    bind(/(?<![\w'.])(?:intro|intros|introv|rintro)\b([^\n]*)/g, introNames, tacticScope);
    bind(/(?<![\w'.])(?:let|have|haveI)\s+(⟨[^\n]*⟩)\s*:=/g, introNames, tacticScope);
    bind(/(?<![\w'.])(?:obtain|rcases\b[^\n]*?\bwith|cases'?\b[^\n]*?\bwith|induction'?\b[^\n]*?\bwith|filter_upwards\b[^\n]*?\bwith|split_ifs\b[^\n]*?\bwith|wlog\b[^\n]*?\bwith|choose!?)[ \t]+([^\n]*?)(?::=|\s:\s|\busing\b|$)/gm, introNames, tacticScope);
    bind(/(?<![\w'.])(?:ext1?|funext)[ \t]+([^:\n;]*?)[ \t]*(?=$|:|;|<;>)/gm, patternNames, tacticScope);
    bind(/(?<![\w'.])(?:have|haveI|let|set|replace|by_contra!?|by_cases!?|generalize[^\n]*?=|rename_i)[ \t]+([^\s:=()\u27E8,]+(?:[ \t]+[^\s:=()\u27E8,]+)*?)(?=[ \t]*(?::|$|\(|\{|\[))/gm, namesIn, tacticScope);
    bind(/^\s*\|([^\n]*?)=>/gm, armNames, lineScope);
    bind(/^[ \t]*[\w'\u2080-\u2089]+((?:[ \t]+[\w'\u0370-\u03FF\u2080-\u2089]+)+)[ \t]*:=/gm, namesIn, lineScope);
    bind(/(?:\{|,)\s*[\w']+((?:[ \t]+[\w'\u0370-\u03FF\u2080-\u2089]+)+)[ \t]*:=/g, (s) => (/\bwith\b/.test(s) ? [] : namesIn(s)), (pos) => groupEnd(pos + 1));
    // Named arguments `(x := v)`: the name is a parameter, not a use.
    bind(/\(\s*([\w'\u0370-\u03FF\u2080-\u2089]+)\s*:=/g, (s) => [s], (pos, j, m) => pos + m[0].length);
    const byName = new Map();
    for (const b of bound) { if (!byName.has(b.n)) byName.set(b.n, []); byName.get(b.n).push(b); }
    const out = new Set();
    const re = /(?<![.\w'\u0370-\u03FF\u1F00-\u1FFF\u2080-\u209C])[A-Za-z_\u0370-\u03FF\u1F00-\u1FFF\u2100-\u214F][\w'!?\u0370-\u03FF\u1F00-\u1FFF\u2080-\u209C\u2100-\u214F]*/g;
    let m;
    while ((m = re.exec(text)) !== null) {
      const n = m[0], p = m.index;
      if (out.has(n)) continue;
      const ranges = byName.get(n);
      if (!ranges || !ranges.some(b => b.from <= p && p < b.to)) out.add(n);
    }
    return out;
  }

  /**
   * How `name` is bound when the source gives no type: `intro x`, `fun x =>`,
   * `obtain ⟨x, hx⟩ := …`, `rcases h with ⟨x, hx⟩`, `| succ n ih =>`, `∀ x,`,
   * or `let/set x := v`. Returns { how, value? } for the latest binding, or null.
   */
  function findUntypedBinder(name, text) {
    if (!name || !text) return null;
    let best = null;
    const consider = (pos, how, value) => { if (!best || pos >= best.pos) best = { pos, how, value }; };
    const scan = (re, how, names = namesIn) => {
      re.lastIndex = 0;
      let m;
      while ((m = re.exec(text)) !== null) {
        if (names(m[1]).includes(name)) consider(m.index, how);
      }
    };
    // Tactics are words of their own: not `Exists.intro` / `MultilinearMap.ext`, and their
    // names are on the same line (`ext` alone doesn't bind the next line's words).
    scan(/(?<![\w'.])(?:intro|intros|introv|rintro)\b([^\n]*)/g, 'introduced by a tactic', introNames);
    scan(/(?<![\w'.])(?:let|have|haveI)\s+(⟨[^\n]*⟩)\s*:=/g, 'destructured by `let` / `have`', introNames);
    scan(/(?<![\w'.])choose!?[ \t]+([^\n]*?)[ \t]+using\b/g, 'introduced by `choose`', introNames);
    scan(/(?<![\w'.])(?:split_ifs|wlog|interval_cases|fin_cases|induction'|cases')\b[^\n]*\bwith\b([^\n|]*)$/gm, 'introduced by a tactic `with` clause', introNames);
    scan(/\bfun\b([^\n]*?)(?:=>|↦)/g, 'bound by `fun`', binderListNames);
    scan(/(?<![\w'.])obtain[ \t]+([^\n]*?)(?::=|\s:\s|$)/gm, 'destructured by `obtain`', introNames);
    scan(/(?<![\w'.])rcases\b[^\n]*\bwith\b([^\n]*)/g, 'destructured by `rcases`');
    scan(/(?<![\w'.])filter_upwards\b[^\n]*\bwith\b([^\n]*)/g, 'introduced by `filter_upwards`');
    scan(/(?:\]|^)[ \t]*with\b([^\n|]*)$/gm, 'introduced by a tactic `with` clause');
    scan(/(?<![\w'.])(?:induction|cases|ext|funext|choose|peel)\b[^\n]*\bwith\b([^\n|]*)$/gm, 'introduced by a tactic');
    scan(/^\s*\|([^\n]*?)=>/gm, 'bound in a match / induction case', armNames);
    scan(/(?:∀|∃!?|Π|λ)\s+([^:,\n]*?),/g, 'bound by a quantifier', binderListNames);
    scan(/(?:∑'?|∏'?|⋃|⋂|⨆|⨅|∫|∮|⨂\[[^\]\n]*\]|⨁)\s*([^:,\n]*?)\s*(?:\bin\b|∈|,)/g, 'bound by a big operator / integral', binderListNames);
    scan(/(?<![\w'.])(?:by_contra!?|by_contra'|contrapose!?|by_cases!?)[ \t]+([^\s:]+)[ \t]*$/gm, 'introduced by `by_contra` / `by_cases`');
    scan(/\{\s*([^:{}|]+?)\s*\|(?!\|)/g, 'bound in a set-builder');
    scan(/\{\s*([^:{}|/]+?)\s*\/\/(?!\/)/g, 'bound in a subtype');
    scan(/(?<![\w'.])set\s+[^\n]*?(?:\n[^\n]*?){0,2}\bwith\s+←?\s*([^\s]+)/g, 'introduced by `set … with`');
    scan(/(?<![\w'.])generalize\b[^\n]*?=[ \t]*([^\s:;,]+)/g, 'introduced by `generalize`');
    scan(/(?<![\w'.])(?:ext1?|funext)[ \t]+([^:\n;]*?)[ \t]*(?=$|:|;|<;>)/gm, 'introduced by `ext`', patternNames);
    scan(/^[ \t]*[\w'\u2080-\u2089]+((?:[ \t]+[\w'\u0370-\u03FF\u2080-\u2089]+)+)[ \t]*:=/gm, 'an argument of a structure field definition');
    // Untyped binder groups in a declaration header: `theorem coe_mk (f : …) (h₁ h₂) : …`;
    // only the binder list's own groups, not parenthesised terms inside a binder's type.
    const hdr = headerEnd(text);
    if (hdr > 0) {
      const header = text.slice(0, hdr);
      let depth = 0;
      for (let k = 0; k < header.length; k++) {
        const ch = header[k];
        if (OPENERS[ch]) {
          if (depth === 0 && '({⦃'.includes(ch)) {
            const close = matchClose(header, k);
            const inner = close === -1 ? '' : header.slice(k + 1, close);
            if (inner && namesIn(inner).includes(name) && !/[^\s\w'\u0370-\u03FF\u2080-\u2089]/.test(inner)) {
              consider(k, 'a binder of this declaration without a written type');
            }
          }
          depth++;
        } else if (CLOSERS.has(ch)) depth = Math.max(0, depth - 1);
      }
    }
    const defRe = /\b(?:let|set|have)\s+([^\s:=()]+)(?:\s*[({⦃[](?:[^(){}⦃⦄[\]]|[({[][^(){}[\]]*[)}\]])*[)}⦄\]])*\s*:=\s*([^\n]*?)(?:\bwith\b|$)/gm;
    let dm;
    while ((dm = defRe.exec(text)) !== null) {
      if (dm[1] === name) consider(dm.index, 'defined locally', dm[2].trim());
    }
    return best ? { how: best.how, value: best.value, pos: best.pos } : null;
  }

  // --- Type inference for locals without a written type ---

  /** rcases-style pattern → { name } | { alt: [...] } | { tuple: [...] } | { other }. */
  function parsePattern(p) {
    p = stripParens(p);
    const alts = splitTop(p, '|');
    if (alts.length > 1) return { alt: alts.map(parsePattern) };
    if (p.startsWith('⟨') && matchClose(p, 0) === p.length - 1) return { tuple: splitTop(p.slice(1, -1), ',').map(parsePattern) };
    if (/^[^\s()⟨⟩,|:]+$/.test(p)) return { name: p };
    return { other: p };
  }

  const LETTERS = ['first', 'second', 'third', 'fourth', 'fifth', 'sixth'];

  /** Element type of a set expression, when it shows: `{z : ℂ | …}`, `A ×ℂ B`, `Set.Icc (0 : ℝ) s`, `s : Set T`. */
  function elementTypeOf(setExpr, text, depth = 0) {
    const S = stripParens(setExpr);
    if (!S || depth > 3) return null;
    let m = S.match(/^\{\s*[^:{}|]+?\s*:\s*([^|{}]+?)\s*(?:\||\/\/)/);
    if (m) return m[1].trim();
    if (topLevelIndexOf(S, '×ℂ') > 0) return 'ℂ';
    const prod = topLevelIndexOf(S, '×ˢ');
    if (prod > 0) {
      const a = elementTypeOf(S.slice(0, prod), text, depth + 1);
      const b = elementTypeOf(S.slice(prod + 2), text, depth + 1);
      return a && b ? `${a} × ${b}` : null;
    }
    for (const op of ['∩', '∪', '\\']) {
      const i = topLevelIndexOf(S, op);
      if (i > 0) return elementTypeOf(S.slice(0, i), text, depth + 1) || elementTypeOf(S.slice(i + 1), text, depth + 1);
    }
    const [head, ...args] = splitApp(S);
    const key = (head || '').split('.').pop();
    if (/^(Icc|Ico|Ioc|Ioo|uIcc|uIoc|Ici|Iic|Ioi|Iio|uIoo)$/.test(key)) {
      for (const a of args) {
        const asc = a.match(/^\((.+) : (.+)\)$/);
        if (asc) return asc[2].trim();
        const t = /^[\w'Ͱ-Ͽ₀-ₜ]+$/.test(a) ? findBinderType(a, text) : null;
        if (t) return t;
      }
      return null;
    }
    if (args.length === 0 && /^[\w'Ͱ-Ͽ₀-ₜ]+$/.test(S)) {
      const t = findBinderType(S, text);
      m = t && t.match(/^(?:Set|Finset)\s+(.+)$/);
      if (m) return stripParens(m[1]);
    }
    return null;
  }

  /** Split the first component off a type for an anonymous-constructor pattern: [component, rest]. */
  function splitProduct(type, pat) {
    const t = stripParens(type);
    if (!t) return [null, null];
    if (t.startsWith('∃')) {
      const comma = topLevelIndexOf(t, ',');
      if (comma === -1) return [null, null];
      let binder = t.slice(1, comma).trim().replace(/^!/, '').trim();
      let body = t.slice(comma + 1).trim();
      binder = stripParens(binder);
      let v, ty = null, pred = null;
      const pm = binder.match(/^([^\s:]+)\s*(∈|∉|<|≤|>|≥|≠|⊆)\s*(.+)$/);
      if (pm) { v = pm[1]; pred = `${pm[2]} ${pm[3]}`; ty = pm[2] === '∈' ? elementTypeOf(pm[3], '') : null; }
      else {
        const c = binder.indexOf(':');
        const names = (c === -1 ? binder : binder.slice(0, c)).trim().split(/\s+/);
        v = names[0];
        ty = c === -1 ? null : binder.slice(c + 1).trim();
        if (names.length > 1) body = `∃ ${names.slice(1).join(' ')}${ty ? ' : ' + ty : ''}, ${body}`;
      }
      if (pred) body = `${v} ${pred} ∧ ${body}`;
      if (pat && pat.name && pat.name !== v) body = replaceWord(body, v, pat.name);
      return [ty, body];
    }
    const and = topLevelIndexOf(t, '∧');
    if (and > 0) return [stripParens(t.slice(0, and)), stripParens(t.slice(and + 1))];
    const iff = topLevelIndexOf(t, '↔');
    if (iff > 0) {
      const a = stripParens(t.slice(0, iff)), b = stripParens(t.slice(iff + 1));
      return [`${a} → ${b}`, `${b} → ${a}`];
    }
    return [null, null];
  }

  /** Assign types to the names in `pat` by destructuring a value of `type`. out: Map name → [{ type, tag }]. */
  function destructure(pat, type, out, tag = null) {
    const put = (n, t) => {
      if (['rfl', '_', '-'].includes(n)) return;
      if (!out.has(n)) out.set(n, []);
      out.get(n).push({ type: t || null, tag });
    };
    if (pat.name) return put(pat.name, type ? stripParens(type) : null);
    if (pat.alt) {
      const parts = [];
      let t = type ? stripParens(type) : null;
      for (let k = 0; k < pat.alt.length; k++) {
        if (!t) { parts.push(null); continue; }
        const i = k < pat.alt.length - 1 ? topLevelIndexOf(t, '∨') : -1;
        if (i > 0) { parts.push(stripParens(t.slice(0, i))); t = stripParens(t.slice(i + 1)); }
        else { parts.push(t); t = null; }
      }
      pat.alt.forEach((p, k) => destructure(p, parts[k], out, k + 1));
      return;
    }
    if (pat.tuple) {
      let t = type;
      pat.tuple.forEach((p, k) => {
        if (k === pat.tuple.length - 1) return destructure(p, t, out, tag);
        const [first, rest] = t ? splitProduct(t, p) : [null, null];
        destructure(p, first, out, tag);
        t = rest;
      });
    }
  }

  /** Peel binders/premises off goal `target` for `intro`-style patterns. */
  function peelGoal(target, patterns, text) {
    const out = new Map();
    let t = stripParens(target);
    let unfoldings = 0;
    for (let pi = 0; pi < patterns.length; pi++) {
      const pat = patterns[pi];
      t = stripParens(t);
      if (!t) { destructure(pat, null, out); continue; }
      if (/^(∀|Π)/.test(t)) {
        const comma = topLevelIndexOf(t, ',');
        if (comma === -1) { destructure(pat, null, out); t = null; continue; }
        const seg = t.slice(1, comma).trim();
        let body = t.slice(comma + 1).trim();
        // Binder list → [{ v, type, pred, bi }] (an instance `[Fintype ι]` binds no name: v null)
        const binders = [];
        if (OPENERS[seg[0]]) {
          let i = 0;
          while (i < seg.length) {
            while (seg[i] === ' ') i++;
            if (!OPENERS[seg[i]]) break;
            const close = matchClose(seg, i);
            if (close === -1) break;
            const g = seg.slice(i + 1, close);
            const c = topColon(g);
            if (seg[i] === '[' && c === -1) binders.push({ v: null, type: g.trim(), bi: '[' });
            else (c === -1 ? g : g.slice(0, c)).trim().split(/\s+/).forEach(v => binders.push({ v, type: c === -1 ? null : g.slice(c + 1).trim(), bi: seg[i] }));
            i = close + 1;
          }
        } else {
          const pm = seg.match(/^([\w'\u0370-\u03FF\u2080-\u209C\s]+?)\s*(∈|∉|<|≤|>|≥|≠|⊆)\s*(.+)$/);
          if (pm) {
            pm[1].trim().split(/\s+/).forEach(v => binders.push({
              v, type: pm[2] === '∈' ? elementTypeOf(pm[3], text) : null, pred: `${pm[2]} ${pm[3]}`
            }));
          } else {
            const c = seg.indexOf(':');
            const names = (c === -1 ? seg : seg.slice(0, c)).trim().split(/\s+/);
            names.forEach(v => binders.push({ v, type: c === -1 ? null : seg.slice(c + 1).trim() }));
          }
        }
        if (binders.length === 0) { destructure(pat, null, out); t = null; continue; }
        const [b, ...rest] = binders;
        if (rest.length) {
          const groups = rest.map(r => r.pred ? null
            : r.bi === '[' ? (r.v ? `[${r.v} : ${r.type}]` : `[${r.type}]`)
              : `${r.bi && r.bi !== '(' ? r.bi : '('}${r.v}${r.type ? ' : ' + r.type : ''}${r.bi && r.bi !== '(' ? OPENERS[r.bi] : ')'}`);
          if (groups.every(Boolean)) body = `∀ ${groups.join(' ')}, ${body}`;
          else body = `∀ ${rest.map(r => r.v).join(' ')} ${rest[0].pred}, ${body}`;
        }
        if (b.pred) body = `${b.v} ${b.pred} → ${body}`;
        // (`intro _` leaves the binder inaccessible: Lean shows it `R✝`.)
        if (pat.name && b.v && pat.name !== b.v) body = replaceWord(body, b.v, pat.name === '_' ? `${b.v}✝` : pat.name);
        destructure(pat, b.type, out);
        t = body;
        continue;
      }
      // Premise `A → B` (plain arrow, not a bundled-map notation).
      let depth = 0, cut = -1;
      for (let k = 0; k < t.length; k++) {
        const ch = t[k];
        if (OPENERS[ch]) depth++;
        else if (CLOSERS.has(ch)) depth = Math.max(0, depth - 1);
        else if (depth === 0 && ch === '→' && t[k + 1] === ' ') { cut = k; break; }
      }
      if (cut > 0) {
        destructure(pat, t.slice(0, cut), out);
        t = t.slice(cut + 1);
        continue;
      }
      if (t.startsWith('¬')) { destructure(pat, t.slice(1), out); t = 'False'; continue; }
      const notMem = topLevelIndexOf(t, '∉');
      if (notMem > 0) { destructure(pat, `${t.slice(0, notMem).trim()} ∈ ${t.slice(notMem + 1).trim()}`, out); t = 'False'; continue; }
      const sub = topLevelIndexOf(t, '⊆');
      if (sub > 0) {
        const A = stripParens(t.slice(0, sub)), B = stripParens(t.slice(sub + 1));
        destructure(pat, elementTypeOf(A, text) || elementTypeOf(B, text), out);
        const v = pat.name || 'x';
        t = `${v} ∈ ${A} → ${v} ∈ ${B}`;
        continue;
      }
      // A definition Lean sees through (`InfinitudeOfPrimes`, `s.Infinite`): unfold, try again.
      const unfolded = unfoldings < 4 ? unfoldProp(t, text) : null;
      if (unfolded) { unfoldings++; t = unfolded; pi--; continue; }
      destructure(pat, null, out);
      t = null;
    }
    return out;
  }

  // Prop-valued definitions that `intro` / `fun` see through, as Lean unfolds them.
  // (A function that isn't a name is applied in parentheses, not beta-reduced, as `intro` leaves
  // it: `h : (fun g ↦ f g + 1) a = (fun g ↦ f g + 1) b`.)
  const fnText = (f) => (/^[\w'.\u0370-\u03FF\u1F00-\u1FFF\u2080-\u209C]+$/.test(f) || (f.startsWith('(') && matchClose(f, 0) === f.length - 1) ? f : `(${f})`);
  const PROP_DEFS = {
    'Set.Infinite': (a) => a.length === 1 && `¬${fnText(a[0])}.Finite`,
    'Set.Nonempty': (a) => a.length === 1 && `∃ x, x ∈ ${a[0]}`,
    'Function.Injective': (a) => a.length === 1 && `∀ ⦃a₁ a₂⦄, ${fnText(a[0])} a₁ = ${fnText(a[0])} a₂ → a₁ = a₂`,
    'Function.Surjective': (a) => a.length === 1 && `∀ b, ∃ a, ${fnText(a[0])} a = b`,
    'Monotone': (a) => a.length === 1 && `∀ ⦃a b⦄, a ≤ b → ${fnText(a[0])} a ≤ ${fnText(a[0])} b`,
    'Antitone': (a) => a.length === 1 && `∀ ⦃a b⦄, a ≤ b → ${fnText(a[0])} b ≤ ${fnText(a[0])} a`,
    'StrictMono': (a) => a.length === 1 && `∀ ⦃a b⦄, a < b → ${fnText(a[0])} a < ${fnText(a[0])} b`,
    'StrictAnti': (a) => a.length === 1 && `∀ ⦃a b⦄, a < b → ${fnText(a[0])} b < ${fnText(a[0])} a`,
    'Irrational': (a) => a.length === 1 && `${a[0]} ∉ Set.range ((↑) : ℚ → ℝ)`
  };
  Object.setPrototypeOf(PROP_DEFS, null); // looked up by words from the source: no `constructor`, `toString`, … from Object
  /**
   * `t` with its head definition unfolded: Mathlib's in `PROP_DEFS`, or a `def … : Prop := …`
   * of the PR's files (`InfinitudeOfPrimes` is `{p : ℕ | p.Prime}.Infinite`). Text, or null.
   */
  function unfoldProp(t) {
    const n = tCore(parseTerm(t || ''));
    if (!n) return null;
    let head = null, args = [];
    if (n.k === 'id') head = n.v;
    else if (n.k === 'app' && tCore(n.f).k === 'id') { head = tCore(n.f).v; args = n.args.map(x => showTerm(x, 1025)); }
    else if (n.k === 'proj') {
      // `s.Infinite`: a field of the receiver's namespace (only the table's, by its last segment).
      const key = Object.keys(PROP_DEFS).filter(k => k.endsWith(`.${n.f}`));
      return key.length === 1 ? PROP_DEFS[key[0]]([showTerm(n.e, 1025)]) || null : null;
    }
    if (!head) return null;
    const table = PROP_DEFS[head] || PROP_DEFS[Object.keys(PROP_DEFS).find(k => k.endsWith(`.${head}`)) || ''];
    if (table) return table(args) || null;
    const scope = typeof window !== 'undefined' ? window : self;
    const decl = scope.LeanPRScanner && scope.LeanPRScanner.find(head);
    if (!decl || !decl.value) return null;
    const params = peelSignature(decl.signature || '').binders.filter(b => b.explicit).flatMap(b => b.names);
    if (params.length !== args.length) return null;
    return params.reduce((acc, p, i) => replaceWord(acc, p, args[i]), decl.value);
  }

  /** Line index and start offsets for `text`. */
  function lineTable(text) {
    const starts = [0];
    for (let i = 0; i < text.length; i++) if (text[i] === '\n') starts.push(i + 1);
    return starts;
  }

  /**
   * Goal of the `by` block an `intro`/`fun` at `pos` opens: the declaration's statement or a
   * `have`'s type, provided only other intros come before it in the block.
   * Returns { target, patterns } (all intro patterns of the block up to `pos`) or null.
   */
  function introGoal(text, pos, kind) {
    const starts = lineTable(text);
    let li = starts.length - 1;
    while (starts[li] > pos) li--;
    const lineAt = (i) => text.slice(starts[i], i + 1 < starts.length ? starts[i + 1] - 1 : text.length);
    const isIntroLine = (l) => /^\s*(?:·\s*)?(intro|intros|rintro)\b/.test(l);

    // Find the line whose `by` (or `:=` for term-mode `fun`) opens this block.
    let byLine = -1;
    const own = text.slice(starts[li], pos);
    if (/(?::=\s*by|\bby)\s*(?:·\s*)?(?:(?:exact|refine|apply)\s+)?$/.test(own) || (kind === 'fun' && /:=\s*$/.test(own))) {
      byLine = li;
    } else if (/^\s*(?:·\s*)?(?:(?:exact|refine|apply)\s+)?$/.test(own)) {
      let j = li - 1;
      while (j >= 0 && (isIntroLine(lineAt(j)) || !lineAt(j).trim())) j--;
      if (j >= 0 && (/\bby\s*$/.test(lineAt(j).replace(/--.*$/, '')) || (kind === 'fun' && /:=\s*$/.test(lineAt(j))))) byLine = j;
    }
    if (byLine === -1) return null;
    const byEnd = byLine + 1 < starts.length ? starts[byLine + 1] - 1 : text.length;
    const upToBy = text.slice(0, byEnd);
    const assign = upToBy.lastIndexOf(':=');
    if (assign === -1) return null;

    // `have h (params) : T := by` ending on the by-line (latest wins), else the declaration statement.
    let target = null;
    LOCAL_DECL.lastIndex = 0;
    let lm;
    while ((lm = LOCAL_DECL.exec(upToBy)) !== null) {
      const start = lm.index + lm[0].length;
      const end = localDeclTypeEnd(upToBy, start);
      if (end === assign || upToBy.slice(end, assign).trim() === '') {
        target = upToBy.slice(start, end);
        if ((lm[2] || '').trim()) target = null; // binders before the colon: skip, rare
      }
    }
    if (!target) {
      const hdr = headerEnd(text);
      if (hdr > 0 && text[hdr] === ':') {
        const stmtEnd = text.indexOf(':=', hdr);
        if (stmtEnd === assign) target = text.slice(hdr + 1, stmtEnd);
      }
    }
    if (!target) return null;

    // Patterns of every intro in the block, in order, up to and including the one at `pos`.
    const patterns = [];
    for (let i = byLine; i <= li; i++) {
      let l = lineAt(i);
      // On the opening line: after its `by`, or after its `:=` for term-mode `fun` (`:= fun h => by`).
      if (i === byLine) l = kind === 'fun' && l.includes(':=') ? l.slice(l.lastIndexOf(':=') + 2) : l.slice(l.search(/\bby\b|:=\s*$/) + 2);
      const m = kind === 'fun'
        ? l.match(/\bfun\s+(.*?)\s*(?:=>|↦)/)
        : l.match(/\b(?:intro|intros|rintro)\s+(.*)$/);
      if (!m) continue;
      splitTop(m[1].replace(/--.*$/, '').trim(), ' ').filter(Boolean).forEach(p => patterns.push(parsePattern(p)));
    }
    return { target, patterns };
  }

  /** Which `·` case of an `rcases`/`obtain` at `pos` contains the end of `text` (1-based), or 0. */
  function caseIndexAt(text, pos) {
    const starts = lineTable(text);
    let li = starts.length - 1;
    while (starts[li] > pos) li--;
    const lines = text.split('\n');
    const indent = (lines[li].match(/^\s*(?:·\s*)?/) || [''])[0].replace('·', ' ').length;
    let k = 0;
    for (let i = li + 1; i < lines.length; i++) {
      const m = lines[i].match(/^(\s*)·/);
      if (m && m[1].length === indent) k++;
      else if (lines[i].trim() && (lines[i].match(/^\s*/) || [''])[0].length < indent) return 0;
    }
    return k;
  }

  /**
   * Inferred type(s) of an untyped local `name`: { types: [{ type, tag }], source, pending? }.
   * `pending` asks the worker to type a constant application (`obtain h | h := le_or_gt b 1`).
   */
  function inferLocalType(name, text) {
    const untyped = findUntypedBinder(name, text);
    if (!untyped) return null;
    const pos = untyped.pos;
    const lineEnd = text.indexOf('\n', pos) === -1 ? text.length : text.indexOf('\n', pos);
    const line = text.slice(pos, lineEnd);
    const result = (map, source) => {
      const types = (map.get(name) || []).filter(x => x.type);
      return types.length ? { types, source } : null;
    };

    // intro / rintro / fun: peel the goal.
    if (/^(?:intro|intros|introv|rintro)\b/.test(line) || /^fun\b/.test(line)) {
      const goal = introGoal(text, pos, /^fun\b/.test(line) ? 'fun' : 'intro');
      if (goal) return result(peelGoal(goal.target, goal.patterns, text), `the goal \`${stripParens(goal.target).slice(0, 80)}\``);
      return null;
    }

    // obtain PAT := TERM / rcases TERM with PAT
    let pat = null, term = null;
    let m = line.match(/^obtain\s+(.+?)\s*:=\s*(.+)$/) || line.match(/^(?:let|have|haveI)\s+(⟨.+?⟩)\s*:=\s*(.+)$/);
    if (m) { pat = m[1]; term = m[2]; }
    m = !pat && line.match(/^rcases\s+(.+?)\s+with\s+(.+)$/);
    if (m) { term = m[1]; pat = m[2]; }
    if (pat && term) {
      const tree = parsePattern(pat);
      const caseIdx = /\|/.test(pat) ? caseIndexAt(text, pos) : 0;
      term = term.replace(/\s*--.*$/, '').trim();
      const head = applicationHead(term);
      const headType = head && /^[\w'Ͱ-Ͽ₀-ₜ]+$/.test(head) ? findBinderType(head, text) : null;
      if (headType) {
        // Local term: its type (after arguments, for `h x y`).
        const ty = splitApp(term).length > 1 ? conclusionOf(headType) : headType;
        const r = result((() => { const o = new Map(); destructure(tree, ty, o); return o; })(), `\`${term}\``);
        if (r) r.caseIdx = caseIdx;
        return r;
      }
      if (head) return { types: [], source: `\`${term}\``, caseIdx, pending: { pattern: pat, term, name } };
      return null;
    }

    // have x := TERM (no type): the type of TERM, from its head's signature.
    m = line.match(/^(?:have|haveI|let)\s+([^\s:=()]+)((?:\s*[({⦃[](?:[^(){}⦃⦄[\]]|[({[][^(){}[\]]*[)}\]])*[)}⦄\]])*)\s*:=\s*/);
    if (m && m[1] === name) {
      const term = fullTermAt(text, pos + m[0].length);
      if (!term || /^(by|fun|λ|⟨)\b|^[(⟨]/.test(term)) return null;
      const parts = appParts(term);
      if (!parts) return null;
      const params = m[2].trim(); // `have hag (i : ℕ) := …` has type `∀ (i : ℕ), …`
      const local = /^[\w'\u0370-\u03FF\u2080-\u209C]+$/.test(parts.head) ? localType(parts.head, text) : null;
      if (local) {
        const app = applicationTypeFrom(local, parts.positional, parts.named, text);
        return app ? { types: [{ type: params ? `∀ ${params}, ${app.type}` : app.type, tag: null }], source: `\`${parts.head}\`'s type` } : null;
      }
      return { types: [], source: `\`${term}\``, caseIdx: 0, pending: { pattern: name, term, name, params } };
    }

    // set x := v with hx
    m = line.match(/^set\s+([^\s:]+)\s*(?::\s*([^:=]+?))?\s*:=\s*(.+?)\s+with\s+←?\s*([^\s]+)/);
    if (m) {
      if (m[4] === name) return { types: [{ type: `${m[1]} = ${m[3].trim()}`, tag: null }], source: '`set … with`' };
      if (m[1] === name && m[2]) return { types: [{ type: m[2].trim(), tag: null }], source: '`set`' };
    }

    // filter_upwards [h₁, h₂] with x hx₁ hx₂: hxᵢ from hᵢ : ∀ᶠ y in l, P y
    m = text.slice(Math.max(0, text.lastIndexOf('filter_upwards', pos + 20)), lineEnd).match(/filter_upwards\s*\[([\s\S]*?)\]\s*with\s+(.+)$/);
    if (m) {
      const names = m[2].trim().split(/\s+/);
      const k = names.indexOf(name);
      const facts = splitTop(m[1], ',');
      if (k >= 1 && facts[k - 1]) {
        const ft = /^[\w'Ͱ-Ͽ₀-ₜ]+$/.test(facts[k - 1].trim()) ? findBinderType(facts[k - 1].trim(), text) : null;
        const ev = ft && ft.match(/^∀ᶠ\s+([^\s]+)(?:\s*:\s*[^,]+?)?\s+in\s+[^,]+,\s*([\s\S]+)$/);
        if (ev) return { types: [{ type: replaceWord(ev[2].trim(), ev[1], names[0]), tag: null }], source: `\`${facts[k - 1].trim()}\`` };
      }
    }
    return null;
  }

  // --- A binder's type from its use: `∀ i, AddCommMonoid (s i)` with `s : ι → Type*` gives `i : ι` ---

  /** Format inferred types for a tooltip: { typeSignature, note }. */
  function formatInferred(name, inferred) {
    const { types, caseIdx } = inferred;
    const tagged = types.filter(t => t.tag);
    if (tagged.length && caseIdx && types.find(t => t.tag === caseIdx)) {
      const t = types.find(x => x.tag === caseIdx);
      return { typeSignature: `${name} : ${t.type}`, note: `in the ${LETTERS[caseIdx - 1] || caseIdx + 'th'} case` };
    }
    if (tagged.length > 1) {
      return {
        typeSignature: `${name} : ${tagged[0].type}`,
        note: 'by case: ' + tagged.map(t => `${LETTERS[t.tag - 1] || t.tag}: \`${t.type}\``).join('; ')
      };
    }
    return { typeSignature: `${name} : ${types[0].type}`, note: null };
  }

  /** Tooltip data for a local variable hovered in `contextText`, or null if it isn't one. */
  function localVariableInfo(name, contextText) {
    // `rfl` in `rintro rfl` / `obtain rfl | h` is a pattern (it substitutes), not a variable.
    if (!name || name.includes('.') || !contextText || name === 'rfl') return null;
    let binder = findBinder(name, contextText);
    const later = binder && findUntypedBinder(name, contextText);
    let shadowed = null;
    if (later && later.pos > binder.pos) {
      // `intro x` after an earlier `∀ x : T`: prefer what the intro gives, else fall back to T.
      let inferred = null;
      try { inferred = inferLocalType(name, contextText); } catch (err) { inferred = null; }
      if (inferred && inferred.types.length) binder = null;
      else shadowed = binder;
    }
    if (shadowed) {
      return withReplay({
        name, kind: 'variable', source: 'local_var',
        typeSignature: `${name} : ${shadowed.type}`,
        docstring: `Local variable ${later.how}; shown with the type of the earlier binder \`${name} : ${shadowed.type}\`, which it most likely re-introduces.`
      }, shadowed.type, hypothesisChanges(name, contextText, later.pos));
    }
    if (binder) {
      return withReplay({
        name, kind: 'variable', source: 'local_var',
        typeSignature: `${name} : ${binder.type}`,
        docstring: 'Local variable / hypothesis bound in this declaration.'
      }, binder.type, hypothesisChanges(name, contextText, binder.pos));
    }
    const untyped = findUntypedBinder(name, contextText);
    if (untyped) {
      let inferred = null;
      try { inferred = inferLocalType(name, contextText); } catch (err) { inferred = null; }
      const changes = hypothesisChanges(name, contextText, untyped.pos);
      if (inferred && inferred.types.length) {
        const f = formatInferred(name, inferred);
        return withReplay({
          name, kind: 'variable', source: 'local_var',
          typeSignature: f.typeSignature,
          docstring: `Local variable ${untyped.how}; type inferred from ${inferred.source}${f.note ? ' (' + f.note + ')' : ''}.`
        }, f.typeSignature.slice(name.length + 3), changes);
      }
      // `∀ i, AddCommMonoid (s i)`, `fun i ↦ f i (x i)`: the type of the argument it is.
      const use = !untyped.value && !(inferred && inferred.pending) && /quantifier|big operator|`fun`|set-builder|subtype/.test(untyped.how) ? useOf(name, contextText, untyped.pos) : null;
      const pending = inferred && inferred.pending ? Object.assign({ caseIdx: inferred.caseIdx || 0 }, inferred.pending)
        : use ? { use, name, term: `${use.fn} … ${name}` } : null;
      const info = {
        name, kind: 'variable', source: 'local_var',
        typeSignature: untyped.value ? `${name} := ${untyped.value}` : `${name} : _`,
        docstring: `Local variable ${untyped.how}; its type isn't written in the source` +
          (pending ? ', so it is being worked out…' : ', so it would need Lean to elaborate.'),
        inferNeeded: pending
      };
      // A pending inference gets its base type from the worker; replay changes after that.
      return info.inferNeeded ? withReplay(info, null, changes) : info;
    }
    return null;
  }

  /**
   * Attach a replay request when tactics before the hover change the hypothesis
   * (`rw … at h`, `simp at h`, …): the type shown first is the declared one, and
   * `replayChanges` / `describeReplay` produce the current one (or say why they can't).
   */
  function withReplay(info, baseType, changes) {
    if (!changes || !changes.length) return info;
    const pendingText = changes.map(c => `\`${c.text.length > 60 ? c.text.slice(0, 57) + '…' : c.text}\``).join(', ');
    return Object.assign(info, {
      docstring: `${info.docstring}\n\n*Applying ${pendingText}…*`,
      replay: { baseType, changes, lead: info.docstring, projection: null }
    });
  }

  /** Type of a local, written or inferred (a single unambiguous type), or null. */
  function localType(name, text) {
    const b = findBinder(name, text);
    const later = b && findUntypedBinder(name, text);
    if (b && !(later && later.pos > b.pos)) return b.type;
    if (b) {
      let inferred = null;
      try { inferred = inferLocalType(name, text); } catch (err) { inferred = null; }
      if (!inferred || !inferred.types.length) return b.type;
    }
    let inferred = null;
    try { inferred = inferLocalType(name, text); } catch (err) { return null; }
    if (!inferred || !inferred.types.length) return null;
    if (inferred.types.length === 1) return inferred.types[0].type;
    const pick = inferred.caseIdx && inferred.types.find(x => x.tag === inferred.caseIdx);
    return pick ? pick.type : null;
  }

  // --- Anonymous projections: `h.1`, `h.2`, `p.2.1` ---

  // `x ∈ S a b` that unfold to a conjunction; `$x`, `$a`, `$b` are substituted.
  const MEMBERSHIP_CONJ = {
    'Icc': ['$a ≤ $x', '$x ≤ $b'], 'Ico': ['$a ≤ $x', '$x < $b'],
    'Ioc': ['$a < $x', '$x ≤ $b'], 'Ioo': ['$a < $x', '$x < $b'],
    'uIcc': ['$a ⊓ $b ≤ $x', '$x ≤ $a ⊔ $b'], 'uIoc': ['$a ⊓ $b < $x', '$x ≤ $a ⊔ $b']
  };
  Object.setPrototypeOf(MEMBERSHIP_CONJ, null);

  /**
   * Type of the n-th anonymous projection (`.1`, `.2`) of a value of type `type`, when the
   * shape tells us: `∧`, `↔`, `∃`, `×`, subtypes, `x ∈ s ∩ t` and interval membership.
   * Returns { type, note? } or null (e.g. a structure: the worker can read its `mk`).
   */
  function projectionType(type, n) {
    if (!type || (n !== 1 && n !== 2)) return null;
    let t = type.replace(/\s+/g, ' ').trim();
    while (t.startsWith('(') && matchClose(t, 0) === t.length - 1) t = t.slice(1, -1).trim();
    const strip = (x) => {
      x = x.trim();
      while (x.startsWith('(') && matchClose(x, 0) === x.length - 1) x = x.slice(1, -1).trim();
      return x;
    };
    const pick = (a, b) => ({ type: strip(n === 1 ? a : b) });

    const iff = topLevelIndexOf(t, '↔');
    if (iff > 0) {
      const a = strip(t.slice(0, iff));
      const b = strip(t.slice(iff + 1));
      return { type: n === 1 ? `${a} → ${b}` : `${b} → ${a}`, note: n === 1 ? '`Iff.mp`' : '`Iff.mpr`' };
    }
    if (t.startsWith('∃')) {
      const comma = topLevelIndexOf(t, ',');
      if (comma === -1) return null;
      const binder = t.slice(1, comma).trim().replace(/^\(|\)$/g, '');
      const colon = binder.indexOf(':');
      if (n === 1) return { type: colon === -1 ? '_' : binder.slice(colon + 1).trim(), note: 'the witness' };
      return { type: strip(t.slice(comma + 1)), note: `with \`${binder.split(/[\s:]/)[0]}\` the witness` };
    }
    if (/^\{[^{}]*\/\/.*\}$/.test(t)) {
      const inner = t.slice(1, -1);
      const sep = inner.indexOf('//');
      const binder = inner.slice(0, sep).trim();
      const colon = binder.indexOf(':');
      return n === 1 ? { type: colon === -1 ? '_' : binder.slice(colon + 1).trim() } : { type: inner.slice(sep + 2).trim() };
    }
    const and = topLevelIndexOf(t, '∧');
    if (and > 0) return pick(t.slice(0, and), t.slice(and + 1)); // ∧ is right-associative
    const prod = topLevelIndexOf(t, '×');
    if (prod > 0) return pick(t.slice(0, prod), t.slice(prod + 1));

    const mem = topLevelIndexOf(t, '∈');
    if (mem > 0) {
      const x = strip(t.slice(0, mem));
      const set = strip(t.slice(mem + 1));
      const inter = topLevelIndexOf(set, '∩');
      if (inter > 0) return { type: `${x} ∈ ${strip(n === 1 ? set.slice(0, inter) : set.slice(inter + 1))}` };
      const [head, a, b] = splitApp(set);
      const key = head && head.split('.').pop();
      if (MEMBERSHIP_CONJ[key] && a !== undefined && b !== undefined && /^(Set\.)?[A-Za-z]+$/.test(head)) {
        const tpl = MEMBERSHIP_CONJ[key][n - 1];
        return { type: tpl.replace(/\$x/g, x).replace(/\$a/g, a).replace(/\$b/g, b), note: `\`${x} ∈ ${set}\` unfolds to a conjunction` };
      }
    }
    return null;
  }

  /**
   * Tactic lines after position `after` that change hypothesis `name`:
   * `rw [...] at h`, `simp at h ⊢`, `norm_num at *`, `replace h := …`, `subst`, …
   */
  function laterChanges(name, text, after) {
    const changes = [];
    const re = /^[ \t]*(?:·\s*)?(.*\b(?:rw|rwa|erw|rewrite|nth_rw|nth_rewrite|simp|simp_rw|simpa|dsimp|norm_num|push_neg|push_cast|norm_cast|field_simp|ring_nf|unfold|change|conv|lift)\b[^\n]*\bat\b([^\n]*))$/gm;
    let m;
    while ((m = re.exec(text)) !== null) {
      if (m.index <= after) continue;
      const targets = namesIn(m[2].replace(/⊢/g, ' '));
      if (targets.includes(name) || /\bat\s+\*/.test(m[1])) changes.push(m[1].trim());
    }
    const rep = new RegExp(`\\breplace\\s+${name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\b[^\n]*`, 'g');
    while ((m = rep.exec(text)) !== null) if (m.index > after) changes.push(m[0].trim());
    return changes;
  }

  /**
   * Tooltip data for `h.1`, `h.2.1`, … where `h` is a local. Unknown shapes still get a
   * tooltip naming the base; `structureNeeded` asks the worker to read a structure's `mk`.
   */
  function projectionInfo(chain, contextText) {
    const segs = chain.split('.');
    if (segs.length < 2 || !/^\d+$/.test(segs[segs.length - 1]) || !segs.slice(1).every(x => /^\d+$/.test(x))) return null;
    let base = findBinder(segs[0], contextText);
    const untypedBase = findUntypedBinder(segs[0], contextText);
    if (base && untypedBase && untypedBase.pos > base.pos) base = null; // re-bound later (intro / obtain)
    if (!base) {
      if (!untypedBase) return null;
      const inferredType = localType(segs[0], contextText);
      if (!inferredType) {
        return {
          name: chain, kind: 'variable', source: 'local_var',
          typeSignature: `${chain} : _`,
          docstring: `Projection \`.${segs.slice(1).join('.')}\` of the local \`${segs[0]}\`, which is ${untypedBase.how}; its type isn't written in the source.`
        };
      }
      base = { type: inferredType, pos: untypedBase.pos };
    }
    const changes = hypothesisChanges(segs[0], contextText, base.pos);
    if (changes.length) {
      const info = {
        name: chain, kind: 'variable', source: 'local_var',
        typeSignature: `${chain} : _`,
        docstring: `Projection of \`${segs[0]}\`.`
      };
      withReplay(info, base.type, changes);
      info.replay.projection = segs.slice(1).map(Number);
      return info;
    }
    const warning = '';
    let type = base.type;
    const notes = [];
    for (let k = 1; k < segs.length; k++) {
      const proj = projectionType(type, parseInt(segs[k], 10));
      if (!proj) {
        return {
          name: chain, kind: 'variable', source: 'local_var',
          typeSignature: `${chain} : _`,
          docstring: `Projection \`.${segs.slice(k).join('.')}\` of \`${segs.slice(0, k).join('.')} : ${type}\`.` + warning,
          structureNeeded: { type, index: parseInt(segs[k], 10), rest: segs.slice(k + 1).map(Number) }
        };
      }
      if (proj.note) notes.push(proj.note);
      type = proj.type;
    }
    return {
      name: chain, kind: 'variable', source: 'local_var',
      typeSignature: `${chain} : ${type}`,
      docstring: `Projection of \`${segs[0]} : ${base.type}\`${notes.length ? ' (' + notes.join('; ') + ')' : ''}.` + warning
    };
  }

  // --- Named arguments: `foo (b := a)` ---

  const TACTIC_LEAD = /^(?:exact|refine'?|apply|use|exists|have\s+\S+\s*:=|show\s+.*\bfrom|calc|simpa\s+.*\busing|simpa\s+using|convert|specialize|obtain\s+.*:=|rcases|filter_upwards\s*\[|positivity|gcongr|linarith\s*\[|nlinarith\s*\[)\s*/;

  /**
   * For text ending in `… f a (`, where the hovered word is followed by `:=`, the
   * function being applied (`f`), possibly across lines; null if there is none.
   */
  function namedArgFunction(prefixText) {
    const t = (prefixText || '').replace(/\(\s*$/, '');
    if (t === prefixText) return null;
    let depth = 0;
    let k = t.length - 1;
    for (; k >= 0; k--) {
      const ch = t[k];
      if (CLOSERS.has(ch)) depth++;
      else if (OPENERS[ch]) { if (depth === 0) break; depth--; }
      else if (depth === 0 && (ch === ',' || ch === '←' || ch === '|' || (ch === '=' && t[k - 1] === ':'))) break;
    }
    let segment = t.slice(k + 1).replace(/\s+/g, ' ').trim();
    segment = segment.replace(TACTIC_LEAD, '');
    return applicationHead(segment);
  }

  /** Signature `fn`'s binder for named argument `arg`, as tooltip data (or null). */
  function namedArgInfo(arg, fn, signature) {
    const type = findBinderType(arg, signature || '');
    if (!type) return null;
    return {
      name: arg, kind: 'variable', source: 'local_var',
      typeSignature: `(${arg} : ${type})`,
      docstring: `Named argument \`${arg}\` of \`${fn}\`.`
    };
  }

  /**
   * The type a declaration builds (`def map … : SubMulAction R M where`), for
   * `field := …` lines in its `where` / `{ }` block. Returns the type's head or null.
   */
  function structureBeingBuilt(contextText) {
    const end = headerEnd(contextText);
    if (end === -1 || contextText[end] !== ':') return null;
    const rest = contextText.slice(end + 1);
    const stop = rest.search(/\swhere\b|:=/);
    return typeHead(stop === -1 ? rest : rest.slice(0, stop), null);
  }

  // --- Replaying `rw … at h`: a small term model ---
  //
  // Enough of Lean's notation to rewrite hypothesis types the way `rw` does: parse the type,
  // find the first instance of the rule's left side (pre-order, like `kabstract`), fix its
  // variables from that instance, replace every equal instance, and print the result.

  /**
   * Types for a pattern bound to a term with a constant head — `obtain h | h := le_or_gt b 1`,
   * `have hb := foo hx (c := M)` — given `sigOf(name)` for constants (PR declarations, Loogle).
   * Resolves to { typeSignature, note, from, conclusion, unresolved } or null.
   */
  async function inferPending(pending, text, sigOf, variableOf) {
    if (pending.use) {
      // An untyped binder: the domain of the function it is first applied to.
      const typeOfName = async (n) => {
        const segs = n.split('.');
        const t = localType(segs[0], text) || (variableOf ? await variableOf(segs[0]) : null);
        if (segs.length === 1 || !t) return t;
        // `e.symm` for an equivalence `e : A ≃ B` is a function on `B`.
        const e = tCore(parseTerm(t));
        if (segs.length === 2 && segs[1] === 'symm' && e && e.k === 'bin' && /^≃/.test(e.op)) return showTerm(Object.assign({}, e, { l: e.r, r: e.l }));
        return null;
      };
      const ft = await typeOfName(pending.use.fn);
      const dom = ft ? await domainOf(ft, pending.use.k, typeOfName) : null;
      return dom ? { typeSignature: `${pending.name} : ${dom}`, from: pending.use.fn, use: true } : null;
    }
    const parts = appParts(pending.term);
    if (!parts) return null;
    let sig = /^[\w'\u0370-\u03FF\u2080-\u209C]+$/.test(parts.head) ? localType(parts.head, text) : null;
    if (!sig && sigOf) sig = await sigOf(parts.head);
    if (!sig) return null;
    const app = applicationTypeFrom(sig, parts.positional, parts.named, text);
    if (!app) return null;
    const out = new Map();
    destructure(parsePattern(pending.pattern), app.type, out);
    const types = (out.get(pending.name) || []).filter(t => t.type)
      .map(t => (pending.params ? Object.assign({}, t, { type: `∀ ${pending.params}, ${t.type}` }) : t));
    if (!types.length) return null;
    const f = formatInferred(pending.name, { types, caseIdx: pending.caseIdx || 0 });
    return { typeSignature: f.typeSignature, note: f.note, from: parts.head, conclusion: app.type, unresolved: app.unresolved };
  }

  /** The term starting at `start`, including continuation lines indented deeper than its line. */
  function fullTermAt(text, start) {
    const ls = text.lastIndexOf('\n', start - 1) + 1;
    const indent = (text.slice(ls).match(/^\s*/) || [''])[0].length;
    let end = text.indexOf('\n', start);
    while (end !== -1) {
      const next = text.indexOf('\n', end + 1);
      const line = text.slice(end + 1, next === -1 ? text.length : next);
      if (!line.trim() || (line.match(/^\s*/) || [''])[0].length <= indent) break;
      end = next;
    }
    return text.slice(start, end === -1 ? text.length : end).replace(/--[^\n]*/g, '').replace(/\s+/g, ' ').trim();
  }

  /** Equation for one rule of `rw [...]`; `sigOf(name)` gives a constant's signature (may be async). */
  async function ruleEquation(rule, text, sigOf) {
    let term = rule.term.trim();
    let rev = Boolean(rule.rev);
    const show = term.match(/^\(?\s*show\s+([\s\S]+?)\s+(?:from|by)\b/);
    if (show) return ruleEquationFrom(show[1], [], {}, rev, text);
    const parts = appParts(term);
    if (!parts) return null;
    let head = parts.head;
    const { positional, named } = parts;
    if (/\.symm$/.test(head)) { rev = !rev; head = head.slice(0, -5); }
    let sig = /^[\w'Ͱ-Ͽ₀-ₜ]+$/.test(head) ? localType(head, text) : null;
    if (!sig && sigOf) sig = await sigOf(head);
    return sig ? ruleEquationFrom(sig, positional, named, rev, text) : null;
  }

  /** Does a tactic at `pos` still affect the hovered (last) line? Bullets, nesting and `by` blocks scope it. */
  function tacticInScope(text, pos, hoverStart) {
    const ls = text.lastIndexOf('\n', pos - 1) + 1;
    if (/\bby\b/.test(text.slice(ls, pos))) return false; // nested `by` on the same line: local to it
    const col = (text.slice(ls).match(/^\s*(?:·\s*)?/) || [''])[0].length;
    let p = text.indexOf('\n', pos);
    if (p === -1) return false;
    p++;
    while (p <= hoverStart && p < text.length) {
      const e = text.indexOf('\n', p);
      const line = text.slice(p, e === -1 ? text.length : e);
      if (line.trim() && (line.match(/^\s*/) || [''])[0].length < col) return false;
      if (e === -1) break;
      p = e + 1;
    }
    return true;
  }

  /**
   * Tactics before the hovered line that change hypothesis `name` after position `after`:
   * `{ kind: 'rw', rules, nth }` (rw / rwa / rewrite / erw / nth_rw), `{ kind: 'change', type }`,
   * or `{ kind: 'opaque' }` for tactics that can't be replayed from the text (simp, norm_num, …).
   */
  function hypothesisChanges(name, text, after) {
    const hoverStart = text.lastIndexOf('\n') + 1;
    const changes = [];
    const targets = (locs) => namesIn(locs.replace(/⊢/g, ' ')).includes(name) || /(^|\s)\*(\s|$)/.test(locs);
    const usable = (pos) => {
      if (pos <= after || pos >= hoverStart) return false;
      const ls = text.lastIndexOf('\n', pos - 1) + 1;
      return !/--/.test(text.slice(ls, pos)) && tacticInScope(text, pos, hoverStart);
    };
    const oneLine = (s) => s.replace(/\s+/g, ' ').trim();
    let m;
    const rwRe = /\b(rw|rwa|rewrite|erw|nth_rw|nth_rewrite)\b\s*(\d+)?\s*\[/g;
    while ((m = rwRe.exec(text)) !== null) {
      if (!usable(m.index)) continue;
      const open = m.index + m[0].length - 1;
      const close = matchClose(text, open);
      if (close === -1) continue;
      const tail = text.slice(close + 1).match(/^\s*at\s+([^\n;]*)/);
      if (!tail || !targets(tail[1].replace(/<;>.*$/, ''))) continue;
      const rules = splitTop(text.slice(open + 1, close), ',').filter(Boolean).map(r => ({
        term: r.replace(/^(←|<-)\s*/, '').trim(), rev: /^(←|<-)/.test(r)
      }));
      changes.push({ kind: 'rw', pos: m.index, rules, nth: m[2] ? parseInt(m[2], 10) : 0, text: oneLine(text.slice(m.index, close + 1) + tail[0]) });
    }
    const changeRe = /\bchange\s+([^\n]+?)\s+at\s+([^\n;]*)/g;
    while ((m = changeRe.exec(text)) !== null) {
      if (usable(m.index) && targets(m[2])) changes.push({ kind: 'change', pos: m.index, type: m[1].trim(), text: oneLine(m[0]) });
    }
    const opaqueRe = /\b(simp|simp_rw|dsimp|norm_num|push_neg|push_cast|norm_cast|field_simp|ring_nf|unfold|delta|conv|lift|zify|qify|rify|abel_nf|simp_arith|cancel_denoms|nontriviality)\b[^\n]*?\bat\s+([^\n;]*)/g;
    while ((m = opaqueRe.exec(text)) !== null) {
      if (usable(m.index) && targets(m[2])) changes.push({ kind: 'opaque', pos: m.index, text: oneLine(m[0]) });
    }
    const allRe = /\b(simp_all|subst_vars|subst)\b[^\n]*/g;
    while ((m = allRe.exec(text)) !== null) {
      if (usable(m.index)) changes.push({ kind: 'opaque', pos: m.index, text: oneLine(m[0]) });
    }
    const replaceRe = new RegExp(`\\breplace\\s+${name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*:=`, 'g');
    while ((m = replaceRe.exec(text)) !== null) {
      if (usable(m.index)) changes.push({ kind: 'opaque', pos: m.index, text: oneLine(text.slice(m.index, text.indexOf('\n', m.index) === -1 ? text.length : text.indexOf('\n', m.index))) });
    }
    return changes.sort((a, b) => a.pos - b.pos);
  }

  /**
   * Replay `changes` on `baseType`. `rw`-style rewrites and `change` are applied; replay stops
   * at a tactic it can't model. Resolves to { type, applied, stoppedAt?, failedAt?, failedRule? }.
   */
  async function replayChanges(baseType, changes, text, sigOf) {
    let type = baseType;
    const applied = [];
    for (const ch of changes) {
      if (ch.kind === 'change') { type = ch.type; applied.push(ch); continue; }
      if (ch.kind === 'opaque') return { type, applied, stoppedAt: ch };
      let tree = parseTerm(type);
      if (!tree) return { type, applied, failedAt: ch };
      for (const rule of ch.rules) {
        let eq = null;
        try { eq = await ruleEquation(rule, text, sigOf); } catch (err) { eq = null; }
        const next = eq && rewriteTerm(tree, eq.lhs, eq.rhs, eq.vars, ch.nth);
        if (!next) return { type, applied, failedAt: ch, failedRule: rule.term };
        tree = next;
      }
      type = showTerm(tree);
      applied.push(ch);
    }
    return { type, applied };
  }

  /** Tooltip fields for a local whose type was replayed: { typeSignature, docstring }. */
  function describeReplay(info, result) {
    const r = info.replay;
    const code = (c) => `\`${c.text.length > 80 ? c.text.slice(0, 77) + '…' : c.text}\``;
    const declared = `declared as \`${r.baseType}\``;
    const blocked = result.stoppedAt || result.failedAt;
    let type = result.type;
    let signature;
    if (r.projection) {
      const proj = blocked ? null : projectionChain(type, r.projection);
      signature = `${info.name} : ${proj ? proj.type : '_'}`;
      if (proj) type = proj.type;
    } else {
      signature = `${info.name} : ${type}`;
    }
    let doc;
    if (!blocked) {
      doc = `${r.lead} Type after ${result.applied.map(code).join(', ')}, replayed from the rewrite rules' statements (${declared}).`;
    } else {
      const why = result.stoppedAt
        ? `${code(result.stoppedAt)} changes it, and that can't be replayed without Lean`
        : `${code(result.failedAt)} changes it, but the rewrite couldn't be replayed${result.failedRule ? ` (rule \`${result.failedRule}\`)` : ''}`;
      signature += '  -- outdated';
      doc = `${r.lead} **Outdated:** ${why}. ` +
        (r.projection ? `Its base was \`${result.type}\` before that tactic.` : 'Shown is the type before that tactic') +
        (result.applied.length ? ` (after ${result.applied.map(code).join(', ')}).` : '.') + ` Originally ${declared}.`;
    }
    return { typeSignature: signature, docstring: doc };
  }

  /**
   * Base name and fields of a term used as a receiver: `(hasSum_map_coeff h m).mul_right (q ^ m)`
   * → { base: 'hasSum_map_coeff', path: ['mul_right'] }. Null when the base isn't a name.
   */
  function termChain(text) {
    let n = parseTerm(text);
    const path = [];
    for (let guard = 0; n && guard < 30; guard++) {
      n = tCore(n);
      if (n.k === 'app') { n = n.f; continue; }
      if (n.k === 'proj') { path.unshift(n.f); n = n.e; continue; }
      break;
    }
    return n && n.k === 'id' ? { base: n.v, path } : null;
  }

  // --- Hovering inside a term: the smallest term containing the position, with its type ---
  //
  // Lean's hover on the space in `f x`, on a bracket or an operator shows the innermost term
  // there with its type (`f x : β`). Here the term is parsed from the source line (joined with
  // the lines it continues) and its type inferred from local types and constants' signatures.

  /** Apply anonymous projections `[1, 2, …]` to a type; null if a step isn't known. */
  function projectionChain(type, indices) {
    let t = type;
    for (const n of indices) {
      const p = projectionType(t, n);
      if (!p) return null;
      t = p.type;
    }
    return { type: t };
  }

  // --- Where the hovered line lives: repo, commit, path, line (for file-scope lookup) ---

  let revisionCache = { key: null, head: null, base: null };

  /**
   * Head/base commit of the PR on this page, from GitHub's embedded JSON (null where the page
   * does not say; the background then asks GitHub). Only what is said of this PR counts: after
   * moving from one pull request to another inside GitHub, the page can still hold the data of
   * the one shown before, and a page can name other pull requests too.
   */
  function pageRevision() {
    const key = location.pathname.split('/').slice(0, 5).join('/');
    if (revisionCache.key === key) return revisionCache;
    const m = location.pathname.match(/^\/([^/]+)\/([^/]+)\/pull\/(\d+)/);
    const pr = m ? { owner: m[1], repo: m[2], number: Number(m[3]) } : null;
    let head = null;
    let base = null;
    for (const sc of pr ? document.querySelectorAll('script[type="application/json"], script[type="application/ld+json"]') : []) {
      const said = revisionIn(sc.textContent || '', pr);
      head = head || said.head;
      base = base || said.base;
      if (head && base) break;
    }
    revisionCache = { key, head, base };
    return revisionCache;
  }

  const COMMIT_KEYS = { head: ['headOid', 'headSha', 'headRefOid'], base: ['baseOid', 'baseSha', 'baseRefOid'] };
  const commitAt = (obj, side) => {
    for (const k of COMMIT_KEYS[side]) if (typeof obj[k] === 'string' && /^[0-9a-f]{40}$/.test(obj[k])) return obj[k];
    return null;
  };

  /**
   * The head and base commits that a JSON text gives the pull request `pr` (`{owner, repo,
   * number}`), each null when it gives none. An object with a commit is about the pull request
   * whose `number` it has, or else the nearest object around it has; with no number anywhere
   * around it, about this one only if the text names this pull request's page.
   */
  function revisionIn(text, pr) {
    const out = { head: null, base: null };
    if (!/"(?:head|base)(?:Oid|Sha|RefOid)"/.test(text)) return out;
    let data;
    try { data = JSON.parse(text); } catch (err) { return out; }
    // (`/o/r/pull/46` is not named by `/o/r/pull/460`.)
    const page = `/${pr.owner}/${pr.repo}/pull/${pr.number}`.toLowerCase();
    const lower = text.toLowerCase();
    let at = lower.indexOf(page);
    while (at >= 0 && /[0-9]/.test(lower[at + page.length] || '')) at = lower.indexOf(page, at + 1);
    const namesPage = at >= 0;
    const walk = (node, number, depth) => {
      if (!node || typeof node !== 'object' || depth > 64 || (out.head && out.base)) return;
      if (Array.isArray(node)) { node.forEach((item) => walk(item, number, depth + 1)); return; }
      const own = Number.isInteger(node.number) ? node.number
        : typeof node.number === 'string' && /^\d+$/.test(node.number) ? Number(node.number) : number;
      if (own === pr.number || (own === null && namesPage)) {
        out.head = out.head || commitAt(node, 'head');
        out.base = out.base || commitAt(node, 'base');
      }
      for (const value of Object.values(node)) walk(value, own, depth + 1);
    };
    walk(data, null, 0);
    return out;
  }

  function filePathFor(el) {
    const holder = el.closest('[data-file-path], [data-tagsearch-path], [data-path]');
    if (holder) {
      return holder.getAttribute('data-file-path') || holder.getAttribute('data-tagsearch-path') || holder.getAttribute('data-path');
    }
    const region = el.closest('[aria-labelledby]');
    const heading = region && document.getElementById(region.getAttribute('aria-labelledby'));
    const text = heading && heading.textContent.replace(/[\u200e\u200f]/g, '').trim();
    return text && /\.lean$/.test(text) ? text : null;
  }

  function lineFor(el) {
    const cell = el.closest('td, [role="gridcell"]');
    if (cell && cell.hasAttribute('data-line-number')) {
      return {
        line: parseInt(cell.getAttribute('data-line-number'), 10),
        side: cell.getAttribute('data-diff-side') === 'left' ? 'left' : 'right'
      };
    }
    // Classic view: line numbers live in sibling cells before the code cell.
    const row = el.closest('tr');
    if (!row || !cell) return null;
    const before = [];
    for (const c of row.children) {
      if (c === cell) break;
      if (c.hasAttribute('data-line-number')) before.push(c);
    }
    if (before.length === 0) return null;
    const deleted = rowIsDeletion(row, cell);
    const numCell = deleted ? before[0] : before[before.length - 1];
    return { line: parseInt(numCell.getAttribute('data-line-number'), 10), side: deleted ? 'left' : 'right' };
  }

  /** { owner, repo, pr, sha, side, path, line } for the hovered node on a PR page, or null. */
  function fileRefFromDom(node) {
    const el = node && (node.nodeType === 1 ? node : node.parentElement);
    if (!el || !el.closest) return null;
    const m = location.pathname.match(/^\/([^/]+)\/([^/]+)\/pull\/(\d+)/);
    if (!m) return null;
    const pos = lineFor(el);
    const path = filePathFor(el);
    if (!pos || !pos.line || !path) return null;
    const rev = pageRevision();
    return {
      owner: m[1], repo: m[2], pr: m[3],
      sha: pos.side === 'left' ? rev.base : rev.head,
      side: pos.side, path, line: pos.line
    };
  }

  const scope = (typeof window !== 'undefined' ? window : self);
  scope.LeanTerms.hooks.localType = localType;
  // `self` lets the service worker importScripts() this file for `variable` lookups.
  scope.VersoBinderContext = {
    findBinderType, findUntypedBinder, localVariableInfo, localType, inferLocalType, formatInferred,
    parsePattern, destructure, peelGoal, elementTypeOf, replaceWord, conclusionOf, codomainOf, splitApp,
    structureBeingBuilt, namedArgFunction, namedArgInfo, projectionType, projectionInfo, laterChanges,
    parseTerm, showTerm, matchTerm, rewriteTerm, peelSignature, ruleEquation, hypothesisChanges,
    replayChanges, describeReplay, inferPending, applicationTypeFrom, applyArgs, residualSignature,
    displayType, leanSignature, annotateText, freeNamesInText, declaredTypeBefore, receiverResultType,
    termChain, parenReceiver, applicationHead, typeHead, inferReceiverNamespace, declarationContext,
    contextFromDom, fileRefFromDom, pageRevision, versoAbove,
    // For term_hover.js.
    internal: {
      DECL_START, LINE_SELECTORS, ROW_SEL, domLineEls, lineFor, headerEnd, inferPending, localType, localVariableInfo,
      nearbyRowLines, projectionType, replayChanges
    }
  };
})();
