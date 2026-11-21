/**
 * Lean 4 Tokenizer and Identifier Extractor for GitHub.
 * Accurately extracts qualified identifiers, tactics, and Lean terms under the mouse cursor.
 * Handles single-span tokens, multi-span dotted tokens, and GitHub's new PR React diff view.
 */

(function () {
  // Letters, digits, Greek, letter-like symbols (ℝ, ℂ), and subscripts (Lean allows ₀-₉, ₐ-ₜ,
  // ᵢ-ᵪ); superscripts like ⁻¹ are notation, not identifier characters.
  const LEAN_IDENT_CHAR = /[a-zA-Z0-9_'!?\u0370-\u03FF\u1F00-\u1FFF\u2080-\u209C\u1D62-\u1D6A\u2100-\u214F]/;
  const LEAN_KEYWORDS = new Set([
    "def", "theorem", "lemma", "axiom", "inductive", "structure", "class",
    "instance", "example", "variable", "open", "import", "export", "universe",
    "where", "with", "by", "have", "let", "suffices", "show", "from",
    "if", "then", "else", "match", "return", "do", "for", "in",
    "private", "protected", "noncomputable", "scoped", "partial", "mut",
    "abbrev", "opaque", "macro", "syntax", "elab", "notation", "infix", "infixl", "infixr",
    "fun", "at", "only", "using", "generalizing", "says", "calc", "public", "section", "namespace",
    "end", "omit", "include", "deriving", "extends", "Type", "Sort", "Prop", "Π", "Σ", "λ",
    "alias", "attribute", "set_option", "local", "unif_hint", "initialize", "mutual", "termination_by", "decreasing_by",
    "nonrec", "unsafe", "macro_rules", "deriving", "to"
  ]);

  // Notations written with characters an identifier can't contain, looked up as one token
  // (Mathlib's scoped notations for constants, longest first: `ℝ≥0∞` before `ℝ≥0`).
  const SYMBOL_NOTATIONS = ["ℕ∪{∞}", "log⁺", "ℝ≥0∞", "d⁄dX", "ℝ≥0", "𝕔𝔻", "𝓕⁻", "∂L", "∂R", "𝒅ₕ", "D∃", "𝒟ᵒ", "𝓝ˢ", "Ω^", "∇", "𝐞", "𝔻", "𝓕", "𝟭", "𝒮", "∡", "∠", "𝑳", "𝑹", "𝒅", "𝕋", "𝒟", "𝓞", "𝓟", "𝔠", "∞", "𝓝", "𝓤"];

  // The elements that hold one line of code, in GitHub's diff and file views.
  const LINE_CONTAINERS = '.blob-code-inner, .react-code-text, [data-code-text], td.blob-code, [data-tag="diff-line"], pre, code';

  class LeanTokenizer {
    /**
     * Check if a character is part of a Lean identifier.
     */
    static isIdentChar(ch) {
      if (!ch) return false;
      return LEAN_IDENT_CHAR.test(ch);
    }

    /**
     * Extracts token from a full line string around a given character offset.
     * Accurately stitches together identifiers across dot separators (e.g., Foo.bar.baz).
     */
    static extractTokenFromLine(lineText, offset) {
      if (!lineText || offset < 0 || offset > lineText.length) return null;
      // Notation spelled with characters names can't hold (`d⁄dX`): one token.
      for (const nt of SYMBOL_NOTATIONS) {
        for (let at = lineText.indexOf(nt); at !== -1 && at <= offset; at = lineText.indexOf(nt, at + 1)) {
          if (offset < at + nt.length) {
            return { token: nt, subToken: nt, fullChain: nt, chainUpToCursor: nt, isKeyword: false, start: at, end: at + nt.length, subStart: at, subEnd: at + nt.length };
          }
        }
      }

      let idx = offset;
      if (idx >= lineText.length || (!this.isIdentChar(lineText[idx]) && lineText[idx] !== '.')) {
        if (idx > 0 && (this.isIdentChar(lineText[idx - 1]) || lineText[idx - 1] === '.')) {
          idx = idx - 1;
        } else {
          return null;
        }
      }

      // Scan backwards across identifier chars and valid dots
      let start = idx;
      while (start > 0) {
        const prev = lineText[start - 1];
        if (this.isIdentChar(prev)) {
          start--;
        } else if (prev === '.' && start > 1 && this.isIdentChar(lineText[start - 2])) {
          start--;
        } else {
          break;
        }
      }

      // Scan forwards across identifier chars and valid dots
      let end = idx;
      while (end < lineText.length) {
        const curr = lineText[end];
        if (this.isIdentChar(curr)) {
          end++;
        } else if (curr === '.' && end + 1 < lineText.length && this.isIdentChar(lineText[end + 1])) {
          end++;
        } else {
          break;
        }
      }

      let rawToken = lineText.substring(start, end).replace(/^\.+|\.+$/g, '');
      // Numbers, placeholders `_`, and holes / metavariables `?_`, `?x` aren't names.
      if (!rawToken || /^\d+$/.test(rawToken) || /^_+$/.test(rawToken) || /^[?!]/.test(rawToken)) return null;
      // `foo%` is an elaborator (`fast_instance%`), not a constant.
      if (lineText[end] === '%') return null;
      // The `'` of `∑'` / `∏'`, and suffixes of notation like `(a; g)_N`, aren't names.
      if (rawToken === "'" || (rawToken.startsWith('_') && lineText[start - 1] === ')')) return null;
      // `simp +contextual`, `simp -zeta`: tactic options, not names.
      if ((lineText[start - 1] === '+' || lineText[start - 1] === '-') && /\s/.test(lineText[start - 2] || '') &&
          /\b(simp|simp_all|simpa|dsimp|norm_num|field_simp|grind|aesop|omega|decide|positivity)\b[^\n]*$/.test(lineText.slice(0, start))) return null;

      // Decoration glued to an arrow (`→ₛₗ[σ]`, `≃+*`, `↪o`, `→L[𝕜]`) is part of a bundled-map
      // notation: report the whole operator so it can be mapped to its type.
      const before = lineText[start - 1];
      if (before === '→' || before === '≃' || before === '↪') {
        // Read the whole operator up to whitespace (`→ₙ*`, `→+*o`), normalising `[…]` / `⁅…⁆`.
        let op = before;
        for (let j = start; j < lineText.length && !/\s/.test(lineText[j]) && lineText[j] !== '('; j++) {
          const c = lineText[j];
          if (c === '[' || c === '⁅') {
            const close = lineText.indexOf(c === '[' ? ']' : '⁆', j);
            if (close === -1) break;
            op += c === '[' ? '[_]' : '⁅_⁆';
            j = close;
          } else {
            op += c;
          }
        }
        return {
          token: op, subToken: op, fullChain: op, chainUpToCursor: op, isKeyword: false, arrowNotation: true,
          start: start, end: end, subStart: start, subEnd: end
        };
      }
      if (/^[\u2080-\u209C\u1D62-\u1D6A]/.test(rawToken)) return null; // identifiers never start with a subscript

      // `_root_.Foo.bar` names `Foo.bar`; `_root_` itself isn't a declaration.
      if (rawToken.startsWith('_root_.')) {
        if (idx < start + 6) return null;
        start += 7;
        rawToken = rawToken.slice(7);
      } else if (rawToken === '_root_') {
        return null;
      }

      // On the `.` of `hy.2` / `h.trans`, the field after it is meant (Lean's `.2` hover).
      let onDot = false;
      if (lineText[idx] === '.' && idx + 1 < end && this.isIdentChar(lineText[idx + 1]) && idx > start) {
        idx += 1;
        onDot = true;
      }

      // Extract local sub-token around idx
      let subStart = idx;
      while (subStart > start && this.isIdentChar(lineText[subStart - 1])) subStart--;
      let subEnd = idx;
      while (subEnd < end && this.isIdentChar(lineText[subEnd])) subEnd++;
      let subToken = lineText.substring(subStart, subEnd).replace(/^\.+|\.+$/g, '');
      if (!subToken) {
        const parts = rawToken.split('.');
        subToken = parts[parts.length - 1];
      }

      // Determine the expression up to the hovered sub-token (like Lean LSP in VS Code)
      // e.g. in "ZeroAtFilter.neg":
      // - cursor on "ZeroAtFilter" -> target is "ZeroAtFilter"
      // - cursor on "neg" -> target is "ZeroAtFilter.neg"
      let tokenUpToCursor = lineText.substring(start, subEnd).replace(/^\.+|\.+$/g, '');
      const chainUpToCursor = tokenUpToCursor;

      // If tokenUpToCursor starts with a local variable or hypothesis caller (e.g. hl.sortedLE.pairwise or h.ZeroAtFilter),
      // strip the leading hypothesis/receiver to resolve the type or lemma
      const chainParts = tokenUpToCursor.split('.');
      if (chainParts.length > 1) {
        const first = chainParts[0];
        const second = chainParts[1];
        // A lowercase first segment is a local receiver (`hl.nodup`, `this.le`); an
        // uppercase one is a namespace (`Set.uIcc_of_le`, `Nat.succ`) and must stay.
        if (/^[a-z_\u03b1-\u03c9]/.test(first) && second !== undefined) {
          chainParts.shift();
          tokenUpToCursor = chainParts.join('.');
        }
      }

      return {
        token: tokenUpToCursor,
        subToken: subToken,
        fullChain: rawToken,
        chainUpToCursor: chainUpToCursor,
        isKeyword: LEAN_KEYWORDS.has(tokenUpToCursor) || LEAN_KEYWORDS.has(subToken),
        start: start,
        end: end,
        // The measured range includes the hovered `.` of a field.
        subStart: onDot ? subStart - 1 : subStart,
        subEnd: subEnd
      };
    }

    /**
     * Resolves the Lean token under the mouse event coordinates.
     */
    static resolveTokenFromEvent(event) {
      let range = null;
      let textNode = null;
      let offset = 0;

      if (document.caretRangeFromPoint) {
        range = document.caretRangeFromPoint(event.clientX, event.clientY);
        if (range) {
          textNode = range.startContainer;
          offset = range.startOffset;
        }
      } else if (document.caretPositionFromPoint) {
        const pos = document.caretPositionFromPoint(event.clientX, event.clientY);
        if (pos) {
          textNode = pos.offsetNode;
          offset = pos.offset;
        }
      }

      if (!textNode) {
        const target = event.target;
        if (target && target.childNodes.length === 1 && target.firstChild.nodeType === Node.TEXT_NODE) {
          textNode = target.firstChild;
          offset = 0;
        } else {
          return null;
        }
      }

      // 1. Try resolving using full code line container (handles multi-span dotted tokens)
      const lineContainer = event.target.closest(LINE_CONTAINERS) || textNode.parentElement;

      if (lineContainer && range) {
        try {
          const preRange = document.createRange();
          preRange.selectNodeContents(lineContainer);
          preRange.setEnd(range.startContainer, range.startOffset);
          const lineOffset = preRange.toString().length;
          const fullLineText = lineContainer.textContent || '';

          const lineRes = this.extractTokenFromLine(fullLineText, lineOffset);
          // Measure the hovered identifier itself (not the caret or the whole line),
          // and ignore points that aren't over it, e.g. blank space after a line's end.
          const tokenRange = lineRes && this.rangeForOffsets(lineContainer, lineRes.subStart, lineRes.subEnd);
          if (lineRes && tokenRange && this.pointInRange(tokenRange, event.clientX, event.clientY)) {
            // The code the hover is about: a qualified constant as a whole (`Set.uIcc_of_le`),
            // otherwise the hovered segment (`pairwise` of `hl.sortedLE.pairwise`).
            const shadeStart = /^[A-Z]/.test(lineRes.fullChain || '') ? lineRes.start : lineRes.subStart;
            const shade = (shadeStart < lineRes.subStart && this.rangeForOffsets(lineContainer, shadeStart, lineRes.subEnd)) || tokenRange;
            return {
              shade: [shade],
              token: lineRes.token,
              subToken: lineRes.subToken,
              chainUpToCursor: lineRes.chainUpToCursor,
              fullChain: lineRes.fullChain,
              isKeyword: lineRes.isKeyword,
              tacticPosition: this.isTacticPosition(fullLineText.slice(0, lineRes.start)),
              linePrefix: fullLineText.slice(this.markerLength(lineContainer), lineRes.start),
              tokenText: fullLineText.slice(lineRes.start, lineRes.end),
              lineSuffix: fullLineText.slice(lineRes.end),
              // Where the hovered text and the pointer are in the line of code (after any diff
              // marker), to look up what Lean itself recorded there.
              column: lineRes.subStart - this.markerLength(lineContainer),
              columnEnd: lineRes.subEnd - this.markerLength(lineContainer),
              caret: lineOffset - this.markerLength(lineContainer),
              // Where the dotted name the hovered field belongs to starts (`h` of `h.mp`).
              chainColumn: lineRes.start - this.markerLength(lineContainer),
              boundingRect: tokenRange.getBoundingClientRect(),
              textNode: textNode
            };
          }
          // Not over a name: the term there (a space, bracket, operator or numeral), as Lean's
          // hover on the space in `f x` shows `f x : β`.
          return this.termAt(lineContainer, fullLineText, lineOffset, event.clientX, event.clientY, textNode);
        } catch (err) {
          // Fall through to single text node extractor
        }
      }

      // 2. Fallback to single textNode extractor
      return this.extractTokenAt(textNode, offset, event.clientX, event.clientY);
    }

    /**
     * Where a click is in a line of code: `{ container, offset, textNode }`, with `offset`
     * counted in the text of the line's container (a diff marker included, as `markerLength`
     * says); or null when the point is not in a line of code. A point past the end of a line
     * is the end of that line.
     */
    static caretFromEvent(event) {
      let node = null;
      let offset = 0;
      if (document.caretRangeFromPoint) {
        const range = document.caretRangeFromPoint(event.clientX, event.clientY);
        if (range) { node = range.startContainer; offset = range.startOffset; }
      } else if (document.caretPositionFromPoint) {
        const pos = document.caretPositionFromPoint(event.clientX, event.clientY);
        if (pos) { node = pos.offsetNode; offset = pos.offset; }
      }
      if (!node) return null;
      const el = node.nodeType === Node.ELEMENT_NODE ? node : node.parentElement;
      const container = (el && el.closest && el.closest(LINE_CONTAINERS)) ||
        (event.target && event.target.closest && event.target.closest(LINE_CONTAINERS));
      if (!container || !container.contains(node)) return null;
      const before = document.createRange();
      before.selectNodeContents(container);
      before.setEnd(node, offset);
      return { container, offset: before.toString().length, textNode: node };
    }

    /**
     * The term under the pointer when it isn't over a name: { kind: 'term', token (a key for
     * this term), termText, termNode, termSource, termParent, boundingRect, … } or null.
     */
    static termAt(container, lineText, caret, x, y, textNode) {
      const bc = window.VersoBinderContext;
      if (!bc || !bc.termAtOffset) return null;
      const marker = this.markerLength(container);
      // The character under the pointer (the caret sits at its nearer edge).
      let ch = -1;
      for (const i of [caret, caret - 1]) {
        if (i < marker || i >= lineText.length) continue;
        const r = this.rangeForOffsets(container, i, i + 1);
        if (r && this.pointInRange(r, x, y, 0.5)) { ch = i; break; }
      }
      if (ch === -1) return null;
      const c = lineText[ch];
      if (this.isIdentChar(c) && !/[0-9]/.test(c)) return null; // part of a name or `_`
      if (/[0-9]/.test(c) && this.isIdentChar(lineText[ch - 1] || '') && !/[0-9.]/.test(lineText[ch - 1])) return null; // `h2`
      const code = lineText.slice(marker);
      const at = ch - marker;
      const prefix = code.slice(0, at);
      if (/(^|[^-])--(?!-)/.test(prefix.replace(/`[^`]*`/g, '')) || /^\s*(--|\/-)/.test(code)) return null; // a comment
      const stmt = (bc.statementAround && bc.statementAround(textNode, code)) || { text: code, lineStart: 0 };
      const hit = bc.termAtOffset(stmt.text, stmt.lineStart + at);
      if (!hit) return null;
      // The term on each line it spans (shaded); its part on this line anchors the tooltip.
      const parts = stmt.parts || [{ cell: null, start: stmt.lineStart, len: code.length }];
      const shade = [];
      let range = null;
      for (const p of parts) {
        let lo = Math.max(hit.start, p.start);
        let hi = Math.min(hit.end, p.start + p.len);
        // Not the indentation of a continuation line.
        while (lo < hi && /\s/.test(stmt.text[lo])) lo++;
        while (hi > lo && /\s/.test(stmt.text[hi - 1])) hi--;
        if (hi <= lo) continue;
        const el = p.cell ? this.codeContainer(p.cell) : container;
        const m = p.cell ? this.markerLength(el) : marker;
        const r = el && this.rangeForOffsets(el, m + lo - p.start, m + hi - p.start);
        if (!r) continue;
        shade.push(r);
        if (!p.cell) range = r;
      }
      if (!range) return null;
      const rect = range.getBoundingClientRect();
      return {
        shade,
        kind: 'term',
        token: `⟪term ${Math.round(rect.top)}:${hit.start}:${hit.end}⟫ ${hit.text}`,
        subToken: null,
        chainUpToCursor: null,
        fullChain: null,
        isKeyword: false,
        termText: hit.text,
        termNode: hit.node,
        termSource: hit.src,
        termParent: hit.parent,
        termPath: hit.path,
        termExpected: hit.expected,
        termOnParens: hit.onParens,
        linePrefix: prefix,
        lineSuffix: code.slice(at + 1),
        column: at,
        columnEnd: at + 1,
        caret: at,
        boundingRect: rect,
        textNode: textNode
      };
    }

    /** The element holding a diff cell's code line (marker included, as `markerLength` expects). */
    static codeContainer(cell) {
      return cell.querySelector('.blob-code-inner, .react-code-text, [data-code-text], code') || cell;
    }

    /** Length of a rendered `+`/`-` diff marker at the start of a line container. */
    static markerLength(container) {
      const marker = container.querySelector && container.querySelector('.diff-text-marker');
      return marker ? marker.textContent.length : 0;
    }

    /** A Range over characters [start, end) of `container`'s text, or null. */
    static rangeForOffsets(container, start, end) {
      if (end <= start) return null;
      const walker = document.createTreeWalker(container, NodeFilter.SHOW_TEXT);
      const range = document.createRange();
      let pos = 0;
      let startSet = false;
      for (let node = walker.nextNode(); node; node = walker.nextNode()) {
        const len = node.nodeValue.length;
        if (!startSet && start < pos + len) {
          range.setStart(node, start - pos);
          startSet = true;
        }
        if (startSet && end <= pos + len) {
          range.setEnd(node, end - pos);
          return range;
        }
        pos += len;
      }
      return null;
    }

    /** Is (x, y) over the rendered characters of `range` (allowing a small margin)? */
    static pointInRange(range, x, y, pad = 2) {
      for (const r of range.getClientRects()) {
        if (x >= r.left - pad && x <= r.right + pad && y >= r.top - pad && y <= r.bottom + pad) return true;
      }
      return false;
    }

    /**
     * Does the text before a word put it where a tactic goes? Start of a (diff) line,
     * after `by`, `;`, `<;>`, `·`, `=>`, `|`, or a combinator like `try`/`all_goals`.
     */
    static isTacticPosition(prefix) {
      const p = prefix.replace(/^[+\-]/, '');
      return /^\s*$/.test(p) ||
        /(\bby|;|<;>|·|=>)\s*$/.test(p) ||
        /(^\s*|\bfirst\b.*)\|\s*$/.test(p) ||  // `first | tac`, `| tac` (not `|x|`)
        /\b(try|all_goals|any_goals|repeat|first|focus|iterate\s+\d+|on_goal\s+\d+\s*=>)\s*\(?\s*$/.test(p);
    }

    /**
     * Fallback extractor within a single textNode.
     */
    static extractTokenAt(textNode, offset, x, y) {
      if (!textNode || textNode.nodeType !== Node.TEXT_NODE) return null;
      const text = textNode.nodeValue;
      if (!text || offset < 0 || offset > text.length) return null;

      const res = this.extractTokenFromLine(text, offset);
      if (!res) return null;

      try {
        const range = document.createRange();
        range.setStart(textNode, res.subStart);
        range.setEnd(textNode, res.subEnd);
        if (x !== undefined && !this.pointInRange(range, x, y)) return null;
        const rect = range.getBoundingClientRect();
        return {
          shade: [range],
          token: res.token,
          subToken: res.subToken,
          chainUpToCursor: res.chainUpToCursor,
          isKeyword: res.isKeyword,
          tacticPosition: this.isTacticPosition(text.slice(0, res.start)),
          linePrefix: text.slice(0, res.start),
          tokenText: text.slice(res.start, res.end),
          lineSuffix: text.slice(res.end),
          boundingRect: rect,
          textNode: textNode
        };
      } catch (err) {
        const rect = textNode.parentElement?.getBoundingClientRect() || null;
        return {
          token: res.token,
          subToken: res.subToken,
          chainUpToCursor: res.chainUpToCursor,
          isKeyword: res.isKeyword,
          boundingRect: rect,
          textNode: textNode
        };
      }
    }

    /**
     * Checks if a target DOM element is inside a Lean code block, PR diff, or file view.
     * Fully compatible with both GitHub's classic diffs and the new React-based /changes view.
     */
    static isInsideLeanContext(element) {
      if (!element || typeof element.closest !== 'function') return false; // the document itself

      // 1. Check for standard GitHub diff lines (classic, split, and new React /changes views)
      const inDiff = element.closest(
        '.blob-code, .blob-code-inner, tr[data-line-number], [data-tag="diff-line"], ' +
        '.react-code-text, span[data-code-text], .diff-table, .js-file-line, ' +
        '[data-component="diff-lines"], [data-component="diff-line"], [data-tag="diff-entry"], ' +
        '[data-code-marker], .diff-line, [data-line-number], td[class*="blob-code"]'
      );

      // 2. Check for code blocks in comments / markdown
      const inPre = element.closest('pre, code, .highlight-source-lean');

      // 3. Check if on GitHub PR page (/pull/...)
      const path = window.location.pathname;
      const isPR = path.includes('/pull/') && (path.includes('/changes') || path.includes('/files') || path.includes('/commits'));

      if (inDiff || inPre) return true;
      if (isPR && element.closest('[data-component="diff-file"], [data-tag="diff-entry"], .file')) {
        return true;
      }

      return false;
    }
  }

  window.LeanTokenizer = LeanTokenizer;
})();
