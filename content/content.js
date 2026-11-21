/**
 * Main content script for Lean Lens.
 * Coordinates hover detection, token resolution, PR diff scanning, and tooltip rendering.
 * Built with hysteresis and debouncing to eliminate flickering.
 */

(function () {
  let settings = {
    enabled: true,
    hoverDelay: 250,
    enablePRScanner: true,
    enableBuiltins: true,
    showOutline: true,
    showInfoview: true
  };

  /** Show or hide the outline button for the Lean files on this page. */
  function refreshOutline() {
    const panel = window.LeanOutlinePanel;
    if (!panel) return;
    if (settings.showOutline === false) {
      if (panel.root) panel.root.classList.add('lean-outline-gone');
      return;
    }
    panel.refresh();
  }

  /**
   * Show or hide the infoview's tab: there when the local helper is in use (Lean's infoview
   * needs Lean running) and the page has Lean files.
   */
  function refreshInfoview() {
    const panel = window.LeanInfoviewPanel;
    if (!panel) return;
    panel.refresh(Boolean(settings.enabled && settings.enableHelper && settings.showInfoview !== false));
  }

  let hoverTimer = null;
  let loadingTimer = null;
  let lastHoveredToken = null;
  let lastHoveredRect = null;
  // With Lean's own data, a hover depends on where the token is (its proof state), not only on
  // its text: where the hovered token is on screen, and the hover Lean's data is being read for.
  let lastHoveredSpot = null;
  let activeHover = null;
  let rescanDebounceTimer = null;

  /**
   * Load current extension settings.
   */
  function loadSettings() {
    try {
      chrome.runtime.sendMessage({ action: "GET_SETTINGS" }, (res) => {
        if (res && res.settings) {
          settings = Object.assign(settings, res.settings);
          refreshOutline();
          refreshInfoview();
        }
      });
    } catch (err) {
      // Keep defaults
    }
  }

  /**
   * Debounced scan of PR diffs to handle virtualized scrolling efficiently.
   */
  function triggerPRScan() {
    if (!settings.enablePRScanner) return;
    if (rescanDebounceTimer) clearTimeout(rescanDebounceTimer);
    rescanDebounceTimer = setTimeout(() => {
      window.LeanPRScanner.scanPage();
      indexProjectFiles();
      refreshOutline();
      refreshInfoview();
    }, 350);
  }

  // Declarations read from the PR's files at its commit (and, outside Mathlib, the project
  // files they import): GitHub collapses large diffs, and Loogle only knows Mathlib.
  let projectIndex = null; // promise while a request is running
  const indexedPaths = new Set();
  let indexedPage = null;

  function indexProjectFiles() {
    const m = location.pathname.match(/^\/([^/]+)\/([^/]+)\/pull\/(\d+)/);
    const ctx = window.VersoBinderContext;
    if (!m || !ctx || !window.LeanPRScanner) return;
    const page = `${m[1]}/${m[2]}#${m[3]}`;
    if (indexedPage !== page) { indexedPage = page; indexedPaths.clear(); }
    const paths = window.LeanPRScanner.filePaths().filter(p => !indexedPaths.has(p));
    if (!paths.length) return;
    paths.forEach(p => indexedPaths.add(p));
    const rev = ctx.pageRevision();
    const request = sendMessageP({ action: 'PROJECT_DECLARATIONS', owner: m[1], repo: m[2], pr: m[3], sha: rev.head, paths })
      .then((res) => { if (res && res.declarations) window.LeanPRScanner.addDeclarations(res.declarations); })
      .finally(() => { if (projectIndex === request) projectIndex = null; });
    projectIndex = request;
  }

  /**
   * Initialize PR diff scanning on GitHub.
   */
  function initPRScanner() {
    refreshOutline();
    refreshInfoview();
    if (!settings.enablePRScanner) return;
    window.LeanPRScanner.scanPage();
    indexProjectFiles();
    refreshOutline();
    refreshInfoview();

    // Re-scan when GitHub mounts new virtualized diff chunks
    const observer = new MutationObserver((mutations) => {
      let shouldRescan = false;
      for (const m of mutations) {
        if (m.addedNodes && m.addedNodes.length > 0) {
          for (const node of m.addedNodes) {
            if (node.nodeType === Node.ELEMENT_NODE) {
              if (node.matches?.('.file, .diff-table, [data-tag="diff-line"], [data-component="diff-file"], [data-component="diff-line"], tr') ||
                  node.querySelector?.('.file, .diff-table, [data-tag="diff-line"], [data-component="diff-line"], tr')) {
                shouldRescan = true;
                break;
              }
            }
          }
        }
        if (shouldRescan) break;
      }

      if (shouldRescan) {
        triggerPRScan();
      }
    });

    observer.observe(document.body, { childList: true, subtree: true });
  }

  /** A PR / project declaration's `binders : type` (records from older scans: strip `kind name`). */
  const declSig = (d) => (typeof d.signature === 'string' ? d.signature : d.typeSignature.replace(/^\S+\s+\S+\s*/, ''));

  /**
   * `Namespace.field` for `receiver.field` when the receiver is a local whose binder
   * type can be read from the surrounding declaration; null otherwise.
   */
  function typedFieldToken(tokenInfo, contextText) {
    const chain = tokenInfo.chainUpToCursor;
    const ctx = window.VersoBinderContext;
    if (!chain || !ctx || !contextText) return null;
    const parts = chain.split('.');
    if (parts.length !== 2 || !/^[a-z_α-ω]/.test(parts[0])) return null;
    const ns = ctx.inferReceiverNamespace(parts[0], contextText);
    return ns ? `${ns}.${parts[1]}` : null;
  }

  /**
   * Generalized field notation whose receiver needs more than a binder lookup:
   * `(f a).field` and `h.f₁.f₂.field`. Returns { token } when the namespace is known
   * here, { chain: { const, path }, field } when the worker must read constant types
   * from Loogle, or null.
   */
  function receiverFor(tokenInfo, contextText) {
    const ctx = window.VersoBinderContext;
    const fields = (tokenInfo.chainUpToCursor || '').split('.').filter(Boolean);
    if (!ctx || fields.length === 0) return null;
    const isLocal = (name) => Boolean(ctx.findBinderType(name, contextText));
    // Bound here with a written or inferred type (`intro ι _ R T` with the goal's binders).
    const boundType = (name) => ctx.findBinderType(name, contextText) || ctx.localType(name, contextText);
    const isBound = (name) => isLocal(name) || Boolean(ctx.localType(name, contextText));
    const resolveVar = (v) => {
      const vt = ctx.findBinderType(v, contextText);
      return vt ? ctx.typeHead(vt, null) : null;
    };
    // With the receiver's namespace `ns` known, `ns.f₁` is a constant whose type gives the
    // next namespace; with only a constant known, its type gives the first one.
    // `(hsides i).imp` with `def HasIntegerSide … : Prop := … ∨ …` of the PR: no
    // `HasIntegerSide.imp`, so Lean unfolds the definition and finds `Or.imp`.
    const unfolded = (ns, field) => {
      const scanner = window.LeanPRScanner;
      const def = scanner && scanner.find(ns);
      if (!def || !def.value || scanner.find(`${ns}.${field}`)) return null;
      const head = ctx.typeHead(def.value, null);
      return head && head !== ns ? { token: `${head}.${field}` } : null;
    };
    const finish = (ns, constName, rest) => {
      if (ns && rest.length === 1) {
        const out = { token: `${ns}.${rest[0]}` };
        const alt = unfolded(ns, rest[0]);
        if (alt) out.alt = alt;
        return out;
      }
      if (ns) {
        constName = `${ns}.${rest[0]}`;
        rest = rest.slice(1);
      }
      if (!constName || rest.length === 0) return null;
      return { chain: { const: constName, path: rest.slice(0, -1) }, field: rest[rest.length - 1] };
    };

    // `(expr).f₁.….field`
    let prefix = tokenInfo.linePrefix;
    if (prefix !== undefined) {
      const lastNl = contextText.lastIndexOf('\n');
      prefix = (lastNl === -1 ? '' : contextText.slice(0, lastNl + 1)) + prefix;
      const inner = ctx.parenReceiver(prefix);
      // `(e : T).field`: the ascribed type decides.
      const ascription = inner && inner.match(/^([^:]*[^:=\s])\s:\s(?!=)([\s\S]+)$/);
      if (ascription) {
        const ns = ctx.typeHead(ascription[2], resolveVar);
        if (ns) return finish(ns, null, fields);
      }
      const head = inner && ctx.applicationHead(inner);
      // `((f x).g y).h`: type the base, then each field in turn.
      const nested = inner && !head ? ctx.termChain(inner) : null;
      if (nested) {
        const segs = nested.base.split('.');
        if (isLocal(segs[0])) {
          const ns = ctx.typeHead(ctx.conclusionOf(ctx.localType(segs[0], contextText)), resolveVar);
          return ns ? finish(ns, null, [...segs.slice(1), ...nested.path, ...fields]) : null;
        }
        const prBase = window.LeanPRScanner && window.LeanPRScanner.find(nested.base);
        if (prBase && prBase.typeSignature) {
          const sig = declSig(prBase);
          const ns = ctx.typeHead(ctx.conclusionOf(sig), (v) => {
            const vt = ctx.findBinderType(v, sig);
            return vt ? ctx.typeHead(vt, null) : null;
          });
          if (ns) return finish(ns, null, [...nested.path, ...fields]);
        }
        const rest = [...nested.path, ...fields];
        return { chain: { const: nested.base, path: rest.slice(0, -1), maybeVariable: /^[a-z_]/.test(nested.base), applied: true }, field: rest[rest.length - 1] };
      }
      if (head) {
        const segs = head.split('.');
        const headType = segs.length === 1 ? boundType(head) : null;
        if (headType) {
          // `(h a b).field`: the conclusion of h's type, after its arguments.
          const ns = ctx.typeHead(ctx.conclusionOf(headType), resolveVar);
          return ns ? finish(ns, null, fields) : null;
        }
        // Bound here (`intro … T …`) with a type we can't tell: still not a constant `T`.
        if (segs.length === 1 && ctx.findUntypedBinder(head, contextText)) return null;
        // A declaration from this PR (not in Loogle yet): use its signature here. But a short
        // capitalised name not bound here (`T` in `(T i).y₀`) is likely a section `variable`,
        // unless this file declares it: the worker reads the file's variables first.
        const prDecl = window.LeanPRScanner && window.LeanPRScanner.find(head);
        if (segs.length === 1 && /^[A-Z][\w']?$/.test(head) && !ctx.findUntypedBinder(head, contextText)) {
          const here = ctx.fileRefFromDom(tokenInfo.textNode);
          if (!prDecl || !here || prDecl.filePath !== here.path) {
            return { chain: { const: head, path: fields.slice(0, -1), maybeVariable: true, applied: true }, field: fields[fields.length - 1] };
          }
        }
        if (prDecl && prDecl.typeSignature) {
          const sig = declSig(prDecl);
          const sigVar = (v) => {
            const vt = ctx.findBinderType(v, sig);
            return vt ? ctx.typeHead(vt, null) : null;
          };
          const conclusion = ctx.conclusionOf(sig);
          const ns = ctx.typeHead(conclusion, sigVar);
          if (ns) {
            const result = finish(ns, null, fields);
            // `(e r).field` where `e : A →* B`: the application coerces `e` to a function, so
            // the field may live in the codomain's namespace instead.
            const applied = ctx.splitApp(inner).slice(1).filter(a => !/^\(\s*[\w']+\s*:=/.test(a)).length > 0;
            const codomainNs = applied ? ctx.typeHead(ctx.codomainOf(conclusion), sigVar) : null;
            if (result && codomainNs && codomainNs !== ns) result.alt = finish(codomainNs, null, fields);
            return result;
          }
        }
        if (segs.length === 1 && /^[a-z_α-ω]/.test(head) && !ctx.findUntypedBinder(head, contextText) &&
            !ctx.findBinderType(head, contextText)) {
          // Maybe a file-level `variable` applied to arguments, or an unqualified constant.
          return { chain: { const: head, path: fields.slice(0, -1), maybeVariable: true, applied: true }, field: fields[fields.length - 1] };
        }
        if (segs.length === 2 && isLocal(segs[0])) {
          // `(hf.comp hg).field`: hf's namespace gives the constant `NS.comp`.
          const ns = ctx.inferReceiverNamespace(segs[0], contextText);
          return ns ? finish(null, `${ns}.${segs[1]}`, fields) : null;
        }
        return finish(null, head, fields);
      }
    }

    // `h.f₁.….field` with three or more segments: type each step in turn.
    if (fields.length >= 3 && isBound(fields[0])) {
      const ns = ctx.inferReceiverNamespace(fields[0], contextText);
      return ns ? finish(ns, null, fields.slice(1)) : null;
    }
    // `x.f₁.….field` where `x` isn't bound here: a file-level `variable` (`hT.out`) or a
    // lowercase constant (`one_div_pos.mpr`). The worker tries both.
    // Two-segment `E.foo` with a bound `E` (uppercase locals are common: `E K L : Type*`).
    if (fields.length === 2 && isBound(fields[0]) && !/^[a-z_α-ω]/.test(fields[0])) {
      const ns = ctx.inferReceiverNamespace(fields[0], contextText);
      return ns ? { token: `${ns}.${fields[1]}` } : null;
    }
    // A constant declared in the PR or project (`enormAt_X.trans_lt`): its statement's head.
    // Not for namespaces (`CNF.zero_right` is itself declared) or aliases (no written type).
    const scanner = window.LeanPRScanner;
    if (fields.length >= 2 && !isBound(fields[0]) && /^[a-z_]/.test(fields[0]) && scanner && !scanner.declarations.has(fields.join('.'))) {
      const prHead = scanner.declarations.get(fields[0]);
      if (prHead && prHead.typeSignature && prHead.kind !== 'alias') {
        const sig = declSig(prHead);
        const ns = ctx.typeHead(ctx.conclusionOf(sig), (v) => {
          const vt = ctx.findBinderType(v, sig);
          return vt ? ctx.typeHead(vt, null) : null;
        });
        if (ns) return finish(ns, null, fields.slice(1));
      }
    }
    // `Rectangle.mem_toSet.mp`: a PR constant `Rectangle.mem_toSet` (its namespace written out),
    // then fields of its type.
    if (fields.length >= 3 && /^[A-Z]/.test(fields[0]) && !isBound(fields[0]) && scanner && !scanner.declarations.has(fields.join('.'))) {
      for (let k = fields.length - 1; k >= 2; k--) {
        const prConst = scanner.find(fields.slice(0, k).join('.'));
        if (!prConst || !prConst.typeSignature || prConst.kind === 'alias') continue;
        const sig = declSig(prConst);
        const ns = ctx.typeHead(ctx.conclusionOf(sig), (v) => {
          const vt = ctx.findBinderType(v, sig);
          return vt ? ctx.typeHead(vt, null) : null;
        });
        if (ns) return finish(ns, null, fields.slice(k));
      }
    }
    // Short capitalised names (`E.algebraMap_apply`) may be `variable`s, like lowercase ones.
    if (fields.length >= 2 && (/^[a-z_α-ω]/.test(fields[0]) || /^[A-Z][\w']?$/.test(fields[0])) && !isBound(fields[0])) {
      return {
        chain: { const: fields[0], path: fields.slice(1, -1), maybeVariable: true },
        field: fields[fields.length - 1]
      };
    }
    return null;
  }

  // Notation that names a constant.
  const NOTATION_ALIASES = {
    'ℝ': 'Real', 'ℂ': 'Complex', 'ℕ': 'Nat', 'ℤ': 'Int', 'ℚ': 'Rat', 'π': 'Real.pi', "''": 'Set.image',
    // `a ≡ b [MOD n]` and friends.
    MOD: 'Nat.ModEq', ZMOD: 'Int.ModEq', PMOD: 'AddCommGroup.ModEq', SMOD: 'SModEq',
    // `Option`'s constructors, exported to the root.
    some: 'Option.some', none: 'Option.none'
  };
  Object.setPrototypeOf(NOTATION_ALIASES, null); // looked up by words from the source: no `constructor`, `toString`, … from Object

  /**
   * Surrounding declaration text, the typed token for dot notation, and (for bare
   * identifiers that aren't locals) where the line lives so the worker can read the
   * file's `namespace`/`open`s.
   */
  function lookupContext(tokenInfo) {
    const ctx = window.VersoBinderContext;
    const out = { queryToken: tokenInfo.token, fileRef: null, contextText: '', local: null, receiver: null, namedArg: null, structField: null, skip: false, alt: null };
    if (!ctx) return out;
    try {
      out.contextText = ctx.contextFromDom(tokenInfo.textNode) || '';
      // A bare name (not `x.field`) bound in this declaration is a local variable.
      const chain = tokenInfo.chainUpToCursor || tokenInfo.token;
      // Bundled-map notation (`→ₛₗ[σ]`, `≃+*`): show the structure it stands for.
      if (tokenInfo.arrowNotation) {
        out.queryToken = ctx.typeHead(`A ${chain} B`, null) || chain;
        return out;
      }
      if (!chain.includes('.')) {
        out.local = ctx.localVariableInfo(chain, out.contextText);
        if (out.local) return out;
      }
      // `h.1`, `h.2.1`: anonymous projections of a local.
      out.local = ctx.projectionInfo(chain, out.contextText);
      if (out.local) return out;
      const linePrefix = tokenInfo.linePrefix || '';
      const lineSuffix = tokenInfo.lineSuffix || '';
      // Names on an `open … in` / `open scoped …` / `namespace` line are namespaces (possibly notation-only).
      if (/^\s*(?:open|namespace)\b/.test(linePrefix)) {
        const ns = tokenInfo.fullChain || chain;
        out.local = {
          name: chain, kind: 'namespace', source: 'local_var',
          typeSignature: `namespace ${chain}`,
          docstring: `Namespace opened here${/\bscoped\b/.test(linePrefix) ? ' for its scoped notation and instances' : ''}` +
            (ns !== chain ? ` (part of \`${ns}\`)` : '') + '.'
        };
        return out;
      }
      // Option names (`set_option backward.isDefEq.respectTransparency false in`) aren't constants.
      if (/^\s*set_option\s+[\w.]*$/.test(linePrefix)) { out.skip = true; return out; }
      // `:= .ofLinearMap …`: a leading dot means the namespace of the expected type, here the
      // declaration's own type (`… ≃ₛₗ[σ] …` is `LinearEquiv`).
      if (!chain.includes('.') && /(^|[\s(])\.$/.test(linePrefix)) {
        const lastNl = out.contextText.lastIndexOf('\n');
        const before = (lastNl === -1 ? '' : out.contextText.slice(0, lastNl + 1)) + linePrefix.slice(0, -1);
        const declared = ctx.declaredTypeBefore && ctx.declaredTypeBefore(before);
        const ns = declared && ctx.typeHead(declared, null);
        if (ns) {
          out.queryToken = `${ns}.${chain}`;
          out.fileRef = ctx.fileRefFromDom(tokenInfo.textNode);
          return out;
        }
      }
      // `exact .inl h` in a proof: the goal is a proposition, so `.inl` / `.inr` are `Or`'s (a
      // `Sum` is data, built in term mode).
      if ((chain === 'inl' || chain === 'inr') && /(^|[\s(⟨,])\.$/.test(linePrefix) && /\bby\b/.test(out.contextText)) {
        out.queryToken = `Or.${chain}`;
        out.fileRef = ctx.fileRefFromDom(tokenInfo.textNode);
        return out;
      }
      // `section Foo` / `end Foo` labels and universe names (`Type u`, `Sort (max u v)`).
      if (/^\s*(?:(?:noncomputable|public|private)\s+)*(?:section|end)\s+$/.test(linePrefix) ||
          /\b(?:Type|Sort)\s*\(?(?:max\s+|imax\s+)?(?:[\w\u0370-\u03FF]+\s+)*$/.test(linePrefix) ||
          /^\s*universe\b/.test(linePrefix)) {
        out.skip = true;
        return out;
      }
      // `| ne_zero o ho IH =>`: the case of a `match` / `induction … with`.
      if (!chain.includes('.') && /^\s*\|\s*$/.test(linePrefix) && /=>/.test(lineSuffix)) {
        out.local = {
          name: chain, kind: 'variable', source: 'local_var',
          typeSignature: `| ${chain} …`,
          docstring: `Case \`${chain}\` of a \`match\` / \`induction … with\` / \`cases … with\` alternative; the names after it are bound in that case.`
        };
        return out;
      }
      // `field := …` / `toFun x := …` in a `where` / `{ }` block: a field of the structure being built.
      if (!chain.includes('.') && /^(?:(?:\s+[\w'\u0370-\u03FF\u2080-\u2089]+)|(?:\s*\([^)]*\)))*\s*:=/.test(lineSuffix) &&
          /(^\s*|[{,]\s*|\bwith\s+)$/.test(linePrefix)) {
        const ns = ctx.structureBeingBuilt(out.contextText);
        if (ns) {
          out.queryToken = `${ns}.${chain}`;
          out.structField = { ns, field: chain };
          out.fileRef = ctx.fileRefFromDom(tokenInfo.textNode);
          return out;
        }
      }
      // `foo (b := a)`: `b` is foo's parameter.
      if (!chain.includes('.') && /^\s*:=/.test(tokenInfo.lineSuffix || '')) {
        const lastNl = out.contextText.lastIndexOf('\n');
        const prefix = (lastNl === -1 ? '' : out.contextText.slice(0, lastNl + 1)) + (tokenInfo.linePrefix || '');
        const fn = ctx.namedArgFunction(prefix);
        if (fn) {
          const decl = window.LeanPRScanner && window.LeanPRScanner.find(fn);
          out.local = decl ? ctx.namedArgInfo(chain, fn, decl.typeSignature) : null;
          if (out.local) return out;
          out.namedArg = { fn, arg: chain };
        }
      }
      // `SL(2, ℤ)`, `GL(n, R)`: the matrix groups (notation in `MatrixGroups`).
      if ((chain === 'SL' || chain === 'GL') && /^\(/.test(lineSuffix)) {
        out.queryToken = chain === 'SL' ? 'Matrix.SpecialLinearGroup' : 'Matrix.GeneralLinearGroup';
        return out;
      }
      // (Unless the PR declares a name so: `def some …` of a project.)
      if (!chain.includes('.') && NOTATION_ALIASES[chain] && !(window.LeanPRScanner && window.LeanPRScanner.find(chain))) {
        out.queryToken = NOTATION_ALIASES[chain];
        out.fileRef = ctx.fileRefFromDom(tokenInfo.textNode);
        return out;
      }
      const receiver = receiverFor(tokenInfo, out.contextText);
      if (receiver && receiver.alt) out.alt = receiver.alt;
      if (receiver && receiver.token) {
        out.queryToken = receiver.token;
      } else if (receiver && receiver.chain) {
        out.receiver = receiver.chain;
        out.queryToken = receiver.field;
      } else {
        out.queryToken = typedFieldToken(tokenInfo, out.contextText) || tokenInfo.token;
      }
      // The file reference also lets the worker find `variable`s and resolve receivers' constants.
      out.fileRef = ctx.fileRefFromDom(tokenInfo.textNode);
    } catch (err) {
      // Fall back to the plain token.
    }
    return out;
  }

  /** A namespace the PR's declarations live in, as a tooltip listing a few of them; or null. */
  function projectNamespace(pr, name) {
    const members = [];
    for (const d of pr.declarations.values()) {
      if (d.name && d.name.startsWith(name + '.') && !members.includes(d.name)) members.push(d.name);
      if (members.length >= 6) break;
    }
    if (!members.length) return null;
    return {
      name, kind: 'namespace', source: 'pr_diff', typeSignature: `namespace ${name}`,
      docstring: `A namespace of this project. Some of its declarations:\n\n${members.map(m => `- \`${m}\``).join('\n')}`
    };
  }

  /** `chrome.runtime.sendMessage` as a promise (resolves to null on failure). */
  function sendMessageP(message) {
    return new Promise((resolve) => {
      try {
        chrome.runtime.sendMessage(message, (res) => resolve(chrome.runtime.lastError ? null : res));
      } catch (err) {
        resolve(null);
      }
    });
  }

  /**
   * Signature (`binders : conclusion`) of a constant used as a rewrite rule: a declaration
   * from this PR if it has exactly that name, else Loogle (via the worker), else a PR
   * declaration matched by its short name.
   */
  async function constantSignature(name, fileRef) {
    const pr = window.LeanPRScanner;
    const strip = declSig;
    const exact = pr && pr.declarations.get(name);
    if (exact && (exact.name === name || exact.name === `_root_.${name}`)) return strip(exact);
    // In its own file, a name means the file's declaration in the current namespace first
    // (`tprod` in `namespace PiTensorProduct` is `PiTensorProduct.tprod`, not the root
    // `tprod`), unless that one is `protected`, as Lean resolves names.
    if (exact && !exact.protected && !name.includes('.') && fileRef && exact.filePath === fileRef.path && exact.declaredAs === name) return strip(exact);
    const res = await sendMessageP({ action: 'CONSTANT_SIGNATURE', name, fileRef });
    if (res && res.type) return res.type;
    const loose = pr && pr.find(name);
    return loose && loose.typeSignature ? strip(loose) : null;
  }

  /**
   * Finish a local-variable tooltip that needs more work: a type inferred by the worker
   * (`obtain h | h := le_or_gt b 1`), a structure field (`e.1`), and replaying the tactics
   * that changed the hypothesis since it was bound (`rw [Set.uIcc_of_le h] at hy`).
   */
  async function refineLocal(shown, contextText, fileRef) {
    const ctx = window.VersoBinderContext;
    let info = Object.assign({}, shown);
    const result = await refineLocalType(info, contextText, fileRef, ctx);
    // A file-level variable's `Type*` as Lean names it (`ι₂ : Type u_2`).
    const prefix = result ? `${result.name} : ` : '';
    if (result && fileRef && /\b(?:Type|Sort)\*/.test(result.typeSignature || '') && result.typeSignature.startsWith(prefix)) {
      const r = await sendMessageP({ action: 'FILE_VARIABLE', name: result.name, fileRef });
      const written = result.typeSignature.slice(prefix.length).replace(/\s+/g, ' ');
      if (r && r.type && r.type.replace(/\b(Type|Sort) u_\d+\b/g, '$1*').replace(/\s+/g, ' ') === written) result.typeSignature = prefix + r.type;
    }
    // The type as Lean prints it: `f : (i : ι) → s i` for `(f : Π i, s i)`.
    if (result && ctx && ctx.annotateTextAsync && result.typeSignature && result.typeSignature.startsWith(`${result.name} : `)) {
      const variableOf = fileRef ? async (n) => { const r = await sendMessageP({ action: 'FILE_VARIABLE', name: n, fileRef }); return r && r.type; } : null;
      const typeOfName = async (n) => ctx.localType(n, contextText) || (variableOf ? await variableOf(n) : null);
      try {
        const t = await ctx.annotateTextAsync(result.typeSignature.slice(result.name.length + 3), typeOfName);
        if (t) result.typeSignature = `${result.name} : ${t}`;
      } catch (err) { /* keep the written type */ }
    }
    return result;
  }

  async function refineLocalType(info, contextText, fileRef, ctx) {
    if (info.inferNeeded && ctx) {
      // Instantiate the term's head (a PR declaration or a Loogle constant) with its arguments.
      const variableOf = fileRef
        ? async (name) => { const r = await sendMessageP({ action: 'FILE_VARIABLE', name, fileRef }); return r && r.type; }
        : null;
      const res = await ctx.inferPending(info.inferNeeded, contextText, (name) => constantSignature(name, fileRef), variableOf);
      if (res && res.typeSignature && res.use) {
        info.typeSignature = res.typeSignature;
        info.docstring = info.docstring.replace(/; its type isn't written[\s\S]*$/, '') + `; type inferred from its use as an argument of \`${res.from}\`.`;
      } else if (res && res.typeSignature) {
        info.typeSignature = res.typeSignature;
        info.docstring = `Local variable from \`${info.inferNeeded.term.length > 80 ? info.inferNeeded.term.slice(0, 77) + '…' : info.inferNeeded.term}\`; ` +
          `type inferred from the statement of \`${res.from}\`` + (res.note ? ` (${res.note})` : '') +
          (res.unresolved && res.unresolved.length ? `; \`${res.unresolved.join('`, `')}\` couldn't be determined from the arguments` : '') + '.';
        if (info.replay) {
          info.replay = Object.assign({}, info.replay, { baseType: res.typeSignature.slice(info.name.length + 3), lead: info.docstring });
        }
      }
    }
    if (info.structureNeeded) {
      const res = await sendMessageP(Object.assign({ action: 'STRUCTURE_FIELD' }, info.structureNeeded));
      if (res && res.field) {
        info.typeSignature = `${info.name} : ${res.field.type}`;
        info.docstring = `Field \`${res.field.name}\` of \`${res.structure}\`.\n\n` + info.docstring;
      }
    }
    if (info.replay && info.replay.baseType && ctx) {
      const result = await ctx.replayChanges(info.replay.baseType, info.replay.changes, contextText,
        (name) => constantSignature(name, fileRef));
      info = Object.assign(info, ctx.describeReplay(info, result));
    }
    return info;
  }

  /**
   * Is the hovered word comment / docstring prose? GitHub wraps comments in `.pl-c`.
   * Code in backticks inside a docstring still counts as code.
   */
  function isInProse(tokenInfo) {
    const node = tokenInfo.textNode;
    const el = node && (node.nodeType === 1 ? node : node.parentElement);
    const inComment = Boolean(el && el.closest && el.closest('.pl-c')) ||
      /(^|[^-])--(?!-)/.test((tokenInfo.linePrefix || '').replace(/`[^`]*`/g, ''));
    if (!inComment) return false;
    const ticks = ((tokenInfo.linePrefix || '').match(/`/g) || []).length;
    return ticks % 2 === 0;
  }

  /** Inside an attribute list `@[simp, deprecated (since := …)]`? */
  /** Is an `@[` attribute still open at the end of `prefix`? */
  function attributeOpen(prefix) {
    const open = prefix.lastIndexOf('@[');
    if (open === -1) return false;
    let depth = 0;
    for (let k = open + 1; k < prefix.length; k++) {
      if (prefix[k] === '[') depth++;
      else if (prefix[k] === ']' && --depth === 0) return false;
    }
    return depth > 0;
  }
  // Inside an attribute, also one written over several lines (`@[blueprint` then its options):
  // read from the statement the line belongs to (`tokenInfo.statementPrefix` when given).
  function isInAttribute(tokenInfo) {
    if (attributeOpen(tokenInfo.linePrefix || '')) return true;
    let prefix = tokenInfo.statementPrefix;
    if (prefix === undefined) {
      const ctx = window.VersoBinderContext;
      if (!ctx || !ctx.statementAround || !tokenInfo.textNode || !/^\s/.test(tokenInfo.linePrefix || '')) return false;
      let st = null;
      try { st = ctx.statementAround(tokenInfo.textNode, (tokenInfo.linePrefix || '') + (tokenInfo.tokenText || tokenInfo.token || '') + (tokenInfo.lineSuffix || '')); } catch (err) { st = null; }
      prefix = st && st.text ? st.text.slice(0, (st.lineStart || 0) + (tokenInfo.linePrefix || '').length) : '';
    }
    return attributeOpen(prefix || '');
  }
  // Inside a string literal (`"thm:inf-primes"`): GitHub marks strings `.pl-s`; else an odd
  // number of quotes before the word on its line.
  function isInString(tokenInfo) {
    const node = tokenInfo.textNode;
    const el = node && (node.nodeType === 1 ? node : node.parentElement);
    if (el && el.closest && el.closest('.pl-s, .pl-pds')) return true;
    return (((tokenInfo.linePrefix || '').replace(/\\./g, '').match(/"/g) || []).length) % 2 === 1;
  }

  // --- Verso documents ---
  // After `#doc (Manual) "Title" =>` (a blueprint chapter) a file is prose to its end: its words
  // aren't Lean names. Hovers stay on in ```lean blocks and on the names of `(lean := "A, B")`.
  const versoRegionCache = new Map(); // file at a revision → regions | null | Promise
  function versoRegionsFor(fileRef) {
    const key = `${fileRef.owner}/${fileRef.repo}@${fileRef.sha || fileRef.side}:${fileRef.path}`;
    if (!versoRegionCache.has(key)) {
      if (versoRegionCache.size > 200) versoRegionCache.delete(versoRegionCache.keys().next().value);
      versoRegionCache.set(key, sendMessageP({ action: 'VERSO_REGIONS', fileRef }).then((r) => {
        versoRegionCache.set(key, r || null);
        return r || null;
      }));
    }
    return versoRegionCache.get(key);
  }
  /** In a `(lean := "A, B")` string: declaration names. */
  function inLeanNames(tokenInfo) {
    return /\(lean\s*:=\s*"[^"]*$/.test(tokenInfo.linePrefix || '');
  }
  /**
   * Where the hovered word is in a Verso document: 'prose' (no hover), 'name' (in
   * `(lean := "…")`), null (Lean code), or a promise of one while the file is being read.
   */
  function versoState(tokenInfo) {
    const ctx = window.VersoBinderContext;
    if (!ctx || !tokenInfo.textNode) return null;
    const of = (where) => (where === 'prose' ? (inLeanNames(tokenInfo) ? 'name' : 'prose') : null);
    const fileRef = ctx.fileRefFromDom(tokenInfo.textNode);
    if (!fileRef) {
      // Not a PR file (a file view): a `#doc` line in view decides. (On a PR page the file's
      // regions are read once instead of scanning the page's lines on every mouse move.)
      let seen = null;
      try { seen = ctx.versoAbove ? ctx.versoAbove(tokenInfo.textNode) : null; } catch (err) { seen = null; }
      return seen ? of(seen) : null;
    }
    if (!/\.lean$/.test(fileRef.path)) return null;
    const classify = (r) => {
      if (!r || !r.docLine || fileRef.line < r.docLine) return null; // (the `#doc` line too is no code)
      return of((r.fences || []).some(([a, b]) => fileRef.line > a && fileRef.line < b) ? 'code' : 'prose');
    };
    const regions = versoRegionsFor(fileRef);
    return regions && typeof regions.then === 'function' ? regions.then(classify) : classify(regions);
  }
  const isPromise = (v) => Boolean(v) && typeof v.then === 'function';

  /**
   * The type of the term around a gap, like Lean's hover on the space in `f x` (`f x : β`).
   * Shown only when the type can be worked out from the source and constants' signatures.
   */
  async function triggerTermLookup(tokenInfo) {
    const ctx = window.VersoBinderContext;
    const { token, boundingRect, shade } = tokenInfo;
    if (!ctx || !ctx.termTypeOf) return;
    if (loadingTimer) clearTimeout(loadingTimer);
    loadingTimer = setTimeout(() => {
      if (lastHoveredToken === token) window.VersoTooltipView.showLoading(tokenInfo.termText, boundingRect, shade);
    }, 180);
    // Lean shows the notation's docstring under the type (`a + b` computes the sum …).
    const docName = ctx.notationDocName ? ctx.notationDocName({ node: tokenInfo.termNode, onParens: tokenInfo.termOnParens }) : null;
    const docRequest = docName ? sendMessageP({ action: 'NOTATION_DOC', name: docName }) : Promise.resolve(null);
    let type = null;
    const coerced = new Map(); // applications Lean prints as `(f x) y` (a coerced bundled map)
    const binders = new Map(); // binders whose types were worked out (`(i : ι) → …`)
    try {
      const contextText = ctx.contextFromDom(tokenInfo.textNode) || '';
      const fileRef = ctx.fileRefFromDom(tokenInfo.textNode);
      const variableOf = fileRef
        ? async (name) => { const r = await sendMessageP({ action: 'FILE_VARIABLE', name, fileRef }); return r && r.type; }
        : null;
      type = await ctx.termTypeOf(tokenInfo.termNode, tokenInfo.termSource, contextText,
        (name) => constantSignature(name, fileRef), { parent: tokenInfo.termParent, path: tokenInfo.termPath, expected: tokenInfo.termExpected, variableOf, coerced, binders,
          instances: fileRef ? async () => { const r = await sendMessageP({ action: 'FILE_INSTANCES', fileRef }); return r && r.instances; } : null });
    } catch (err) {
      type = null;
    }
    if (loadingTimer) { clearTimeout(loadingTimer); loadingTimer = null; }
    if (lastHoveredToken !== token) return;
    if (!type) { presentNothing(tokenInfo); return; }
    let shown = tokenInfo.termText;
    try { shown = ctx.termDisplay(tokenInfo.termNode, ctx.contextFromDom(tokenInfo.textNode) || '', coerced, binders) || shown; } catch (err) { /* source text */ }
    const docRes = await docRequest;
    if (lastHoveredToken !== token) return;
    const clip = (t, n) => (t.length > n ? t.slice(0, n - 1) + '…' : t);
    present(tokenInfo, {
      name: shown, kind: 'term', source: 'term',
      typeSignature: `${clip(shown, 300)} : ${clip(type, 600)}`,
      docstring: (docRes && docRes.doc) || ''
    });
  }

  // ------------------------------------------------------------------------------------------
  // Lean's own data, from the local helper (helper/lean-lens-helper.mjs). Where Lean recorded a
  // hover for the token, that is what is shown. The proof state and Lean's messages at the
  // pointer are added to whichever hover is shown.

  /** Whether `tokenInfo` is still the hover in progress (not just a token with the same text). */
  const isCurrent = (tokenInfo) => lastHoveredToken === tokenInfo.token && activeHover === tokenInfo;

  /**
   * Whether Lean's hover for the token is the one to show. On an operator or a bracket Lean's
   * data has documentation only, and the estimated hover (the term there, with its type) says more.
   */
  const usesExactToken = (tokenInfo, exact) => Boolean(exact && exact.state === 'ready' && exact.token) &&
    !(tokenInfo.kind === 'term' && exact.token.kind === 'syntax');

  /** Show a hover for `tokenInfo`, with what Lean's run adds to it. */
  function present(tokenInfo, data) {
    window.VersoTooltipView.show(data, tokenInfo.boundingRect, tokenInfo.shade, tokenInfo.extras || null);
  }

  /** Nothing is known about the token itself: the proof state alone, if Lean recorded one. */
  function presentNothing(tokenInfo) {
    const extras = tokenInfo.extras;
    if (extras && (extras.goals || (extras.messages && extras.messages.length))) {
      window.VersoTooltipView.show(null, tokenInfo.boundingRect, tokenInfo.shade, extras);
    } else {
      window.VersoTooltipView.hide(false);
    }
  }

  /** What Lean recorded where the pointer is: the helper's answer (with the file it is about), or null. */
  function exactLookup(tokenInfo) {
    const ctx = window.VersoBinderContext;
    const fileRef = ctx && ctx.fileRefFromDom ? ctx.fileRefFromDom(tokenInfo.textNode) : null;
    if (!settings.enableHelper || !fileRef || typeof tokenInfo.column !== 'number') return Promise.resolve(null);
    return sendMessageP({
      action: 'EXACT_HOVER', fileRef, column: tokenInfo.column, columnEnd: tokenInfo.columnEnd, caret: tokenInfo.caret,
      // The dotted name up to the hovered field, so `mp` in `X.mp` can show what it says there.
      chain: tokenInfo.chainUpToCursor || undefined, chainColumn: tokenInfo.chainColumn
    })
      .then((res) => (res && res.state && res.state !== 'off' ? Object.assign(res, { fileRef }) : null));
  }

  /** What the tooltip adds from Lean's run: goals and messages when it has run, else its state. */
  function exactExtras(tokenInfo, exact) {
    if (exact.state === 'ready') {
      const goals = exact.goals;
      const stepper = goals && goals.steps > 1 && exact.fileRef ? { go: (delta) => stepBy(tokenInfo, exact, delta) } : null;
      return { lean: exact.lean, goals, messages: exact.messages, helper: { state: 'ready' }, stepper };
    }
    return {
      lean: null, goals: null, messages: [],
      helper: {
        state: exact.state, phase: exact.phase, message: exact.message, done: exact.done, total: exact.total,
        error: exact.error, repo: exact.repo,
        run: () => runLean(tokenInfo, exact)
      }
    };
  }

  /**
   * Step through the proof the hovered tactic is in (the tooltip's ◀ ▶, or ← → while pinned):
   * the goals at the previous or next tactic, with that tactic shaded in the code when it is on
   * the page. The proof's steps are read from Lean's data once per hover.
   */
  function stepBy(tokenInfo, exact, delta) {
    const goals = exact.goals;
    if (!tokenInfo.proofSteps) {
      tokenInfo.proofSteps = sendMessageP({ action: 'EXACT_STEPS', fileRef: exact.fileRef, index: goals.index })
        .then((res) => (res && Array.isArray(res.steps) ? res.steps : []));
      tokenInfo.stepAt = goals.step;
    }
    tokenInfo.proofSteps.then((steps) => {
      if (!steps.length || !window.VersoTooltipView.isVisible()) return;
      const at = Math.max(0, Math.min(steps.length - 1, tokenInfo.stepAt + delta));
      if (at === tokenInfo.stepAt && tokenInfo.stepShown) return;
      tokenInfo.stepAt = at;
      tokenInfo.stepShown = true;
      const step = steps[at];
      const view = window.VersoTooltipView;
      const extras = Object.assign({}, tokenInfo.extras, {
        goals: Object.assign({}, step, { step: at, steps: steps.length }),
        messages: step.messages || []
      });
      tokenInfo.extras = extras;
      const shade = regionRanges(tokenInfo.textNode, step.range);
      const side = view.goalsSide;
      const pinned = view.isPinned;
      // The card is now about the tactic stepped to, not the token first hovered. Pinned, it
      // stays where it is, and the page brings that tactic into view beside it.
      view.show(null, shade.length ? shade[0].getBoundingClientRect() : tokenInfo.boundingRect, shade.length ? shade : tokenInfo.shade, extras,
        { inPlace: pinned });
      view.goalsSide = side;
      if (pinned && !view.isPinned) view.togglePin();
      view.renderExtras(extras);
      if (shade.length) revealBeside(shade, view.container);
    });
  }

  /**
   * Scroll the code a step is about (`ranges`) into view where the card (`cardEl`) does not
   * cover it, as `scrollBeside` says.
   */
  function revealBeside(ranges, cardEl) {
    const boxes = ranges.map((r) => r.getBoundingClientRect()).filter((b) => b.width || b.height);
    if (!boxes.length) return;
    const box = {
      top: Math.min(...boxes.map((b) => b.top)), bottom: Math.max(...boxes.map((b) => b.bottom)),
      left: Math.min(...boxes.map((b) => b.left)), right: Math.max(...boxes.map((b) => b.right))
    };
    const card = cardEl && cardEl.getBoundingClientRect ? cardEl.getBoundingClientRect() : null;
    const delta = scrollBeside(box, card, window.innerHeight, coveredTop((box.left + box.right) / 2));
    if (!delta) return;
    // The page, or whatever scrolls the code inside it. At once: GitHub scrolls its pages
    // smoothly, and the next step (a key held down) would measure the code mid-scroll.
    let scroller = ranges[0].startContainer.parentElement;
    while (scroller && !(scroller.scrollHeight > scroller.clientHeight + 1 && /auto|scroll/.test(getComputedStyle(scroller).overflowY))) {
      scroller = scroller.parentElement;
    }
    (scroller || document.scrollingElement || document.documentElement).scrollBy({ top: delta, behavior: 'instant' });
  }

  /**
   * How far to scroll (down positive) so that `box` (the code a step is about) shows on the
   * screen and not under the card: 0 when it does already; else it goes to the middle of the
   * room above or below the card, whichever needs less scrolling (the middle of the screen if it
   * fits in neither). `topInset` is what sticky bars cover at the top of the screen.
   */
  function scrollBeside(box, card, height, topInset = 0) {
    const rooms = card && box.left < card.right && box.right > card.left
      ? [[topInset, card.top], [card.bottom, height]]
      : [[topInset, height]];
    if (rooms.some(([a, b]) => box.top >= a && box.bottom <= b)) return 0;
    const middle = (box.top + box.bottom) / 2;
    let best = null;
    for (const [a, b] of rooms) {
      if (b - a < box.bottom - box.top + 48) continue;
      const delta = middle - (a + b) / 2;
      if (best === null || Math.abs(delta) < Math.abs(best)) best = delta;
    }
    return Math.round(best !== null ? best : middle - (topInset + height) / 2);
  }

  /** How far down the window GitHub's sticky bars (a pull request's header, a file's) reach at `x`. */
  function coveredTop(x) {
    let y = 0;
    for (let k = 0; k < 4 && document.elementsFromPoint; k++) {
      const bar = document.elementsFromPoint(x, y + 1).find((el) => {
        if (el.closest && el.closest('#verso-hover-root, .lean-outline')) return false;
        if (!/sticky|fixed/.test(getComputedStyle(el).position)) return false;
        const r = el.getBoundingClientRect();
        return r.top <= y + 1 && r.bottom > y + 1 && r.height < 200;
      });
      if (!bar) break;
      y = bar.getBoundingClientRect().bottom;
    }
    return y;
  }

  /**
   * Ranges over a region of the hovered file (`[line, column, end line, end column]`) on the
   * lines the page shows, one per line, without indentation.
   */
  function regionRanges(textNode, region) {
    const ctx = window.VersoBinderContext;
    const tk = window.LeanTokenizer;
    const internal = ctx && ctx.internal;
    const d = internal && internal.domLineEls ? internal.domLineEls(textNode) : null;
    if (!d || !region || !internal.lineFor) return [];
    const here = internal.lineFor(d.els[d.idx]);
    const byLine = new Map();
    for (const el of d.els) {
      const pos = internal.lineFor(el);
      if (pos && (!here || pos.side === here.side)) byLine.set(pos.line, el);
    }
    const out = [];
    for (let line = region[0]; line <= region[2]; line++) {
      const el = byLine.get(line);
      if (!el) continue;
      const container = tk.codeContainer(el);
      const marker = tk.markerLength(container);
      const text = (container.textContent || '').slice(marker);
      let from = line === region[0] ? region[1] : 0;
      let to = line === region[2] ? region[3] : text.length;
      while (from < to && /\s/.test(text[from])) from++;
      while (to > from && /\s/.test(text[to - 1])) to--;
      const range = to > from ? tk.rangeForOffsets(container, marker + from, marker + to) : null;
      if (range) out.push(range);
    }
    return out;
  }

  /** Lean's hover for a token, as a tooltip card. */
  function exactCard(exact) {
    const t = exact.token;
    const card = { name: t.display || t.name, kind: t.kind, typeSignature: t.typeSignature, docstring: t.docstring, source: 'lean', lean: exact.lean };
    if (t.kind !== 'const') return card;
    // A declaration of this pull request or project: say which kind, and where it is.
    const pr = settings.enablePRScanner && window.LeanPRScanner ? window.LeanPRScanner.declarations.get(t.name) : null;
    if (pr) {
      if (pr.kind) card.kind = pr.kind;
      if (pr.element) {
        card.element = pr.element;
        card.lineNumber = pr.lineNumber;
      } else if (pr.repo && pr.sha && pr.filePath) {
        card.sourceUrl = `https://github.com/${pr.repo}/blob/${pr.sha}/${pr.filePath}#L${pr.lineNumber}`;
        card.sourceLabel = 'View source →';
      }
    } else if (!t.definedHere) {
      card.sourceUrl = `https://leanprover-community.github.io/mathlib4_docs/find/?pattern=${encodeURIComponent(t.name)}#doc`;
    }
    return card;
  }

  /**
   * Run Lean on this pull request's Lean files (only ever from a click on the tooltip's button):
   * the hovered file, and on the pull request's own side the other files it changes.
   */
  function runLean(tokenInfo, exact) {
    const fileRef = exact.fileRef;
    if (!fileRef) return;
    const paths = new Set([fileRef.path]);
    if (fileRef.side !== 'left' && window.LeanPRScanner) window.LeanPRScanner.filePaths().forEach((path) => paths.add(path));
    sendMessageP({
      action: 'HELPER_RUN', owner: fileRef.owner, repo: fileRef.repo, pr: fileRef.pr, sha: exact.sha,
      paths: [...paths], allow: exact.state === 'not_allowed'
    }).then((res) => {
      if (!isCurrent(tokenInfo)) return;
      const started = Object.assign({ state: 'error', error: 'The helper did not answer' }, res || {}, { fileRef, sha: exact.sha });
      if (started.state === 'done' || started.state === 'idle') started.state = 'pending';
      tokenInfo.extras = exactExtras(tokenInfo, started);
      window.VersoTooltipView.setExtras(tokenInfo.extras);
      if (started.state === 'pending') watchHelper(tokenInfo);
    });
  }

  /** While Lean runs and the hover stays open: show its progress, then its answer. */
  function watchHelper(tokenInfo) {
    const tick = () => {
      if (!isCurrent(tokenInfo) || !window.VersoTooltipView.isVisible()) return;
      exactLookup(tokenInfo).then((exact) => {
        if (!isCurrent(tokenInfo) || !exact) return;
        tokenInfo.extras = exactExtras(tokenInfo, exact);
        if (exact.state === 'ready') {
          tokenInfo.exact = exact;
          if (usesExactToken(tokenInfo, exact)) present(tokenInfo, exactCard(exact));
          else triggerHoverLookup(tokenInfo);
          return;
        }
        window.VersoTooltipView.setExtras(tokenInfo.extras);
        if (exact.state === 'pending') setTimeout(tick, 1500);
      });
    };
    setTimeout(tick, 1500);
  }

  // The keywords that start a declaration: hovering one shows what is in force there.
  const DECL_KEYWORDS = new Set(['theorem', 'lemma', 'def', 'abbrev', 'instance', 'opaque', 'example', 'structure',
    'class', 'inductive', 'axiom', 'irreducible_def']);

  /** Whether the hovered token is the keyword a declaration starts with (`theorem` in `@[simp] theorem foo`). */
  function isDeclKeyword(tokenInfo) {
    return Boolean(tokenInfo && tokenInfo.kind !== 'term' && DECL_KEYWORDS.has(tokenInfo.token) &&
      /^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|public|noncomputable|scoped|partial|nonrec|unsafe|meta)\s+)*$/.test(
        (tokenInfo.linePrefix || '').replace(/^\s*(?:open|omit|include|set_option)\b.*?\sin\s+/, '')));
  }

  /**
   * `#where` at a declaration: its namespaces and the `open`, `variable`, `include` and `omit`
   * commands in force there, read from the file; on a pull request's own side, hints where a
   * declaration it adds might belong.
   */
  function showWhere(tokenInfo) {
    const ctx = window.VersoBinderContext;
    const fileRef = ctx && ctx.fileRefFromDom ? ctx.fileRefFromDom(tokenInfo.textNode) : null;
    if (!fileRef) return false;
    const rev = ctx.pageRevision();
    fileRef.baseSha = rev.base;
    activeHover = tokenInfo;
    sendMessageP({ action: 'DECL_WHERE', fileRef }).then((res) => {
      if (!isCurrent(tokenInfo) || !res) return;
      present(tokenInfo, whereCard(res, fileRef));
    });
    return true;
  }

  /** A `DECL_WHERE` answer as a tooltip card. */
  function whereCard(res, fileRef) {
    const decl = res.decl;
    const notes = [];
    if (res.hints && res.hints.length) {
      notes.push(`**Placement**\n\n${res.hints.map((h) => `- ${h.text}`).join('\n')}`);
    }
    const similar = (res.similar || []).filter((s) => !(res.hints || []).some((h) => h.line === s.line));
    if (similar.length) {
      notes.push(`Similar in this file: ${similar.map((s) => `\`${s.name}\` (line ${s.line})`).join(', ')}.`);
    }
    if (!res.where) notes.unshift('Nothing opened and no variables here: the top level of the file.');
    return {
      name: decl ? decl.fullName || decl.name || decl.kind : 'Context',
      kind: 'where',
      typeSignature: res.where || '',
      docstring: notes.join('\n\n'),
      source: 'outline',
      bare: !res.where,
      filePath: fileRef.path,
      lineNumber: decl ? decl.line : fileRef.line,
      isNew: res.isNew
    };
  }

  /**
   * Resolve and display hover definition.
   */
  function triggerHoverLookup(tokenInfo) {
    // The keyword starting a declaration: what is in force there (`#where`).
    if (isDeclKeyword(tokenInfo) && showWhere(tokenInfo)) return;
    // A Verso document's prose (known once the file has been read): no hover.
    if (isPromise(tokenInfo.verso)) {
      tokenInfo.verso.then((state) => {
        tokenInfo.verso = state;
        if (state === 'prose' || (state !== 'name' && isInString(tokenInfo))) return;
        if (lastHoveredToken === tokenInfo.token) triggerHoverLookup(tokenInfo);
      });
      return;
    }
    // Lean's own answer first, when the local helper is in use.
    if (settings.enableHelper && tokenInfo.exact === undefined) {
      tokenInfo.exact = null;
      activeHover = tokenInfo;
      exactLookup(tokenInfo).then((exact) => {
        if (!isCurrent(tokenInfo)) return;
        tokenInfo.exact = exact;
        tokenInfo.extras = exact ? exactExtras(tokenInfo, exact) : null;
        if (usesExactToken(tokenInfo, exact)) {
          present(tokenInfo, exactCard(exact));
          return;
        }
        triggerHoverLookup(tokenInfo);
        if (exact && exact.state === 'pending') watchHelper(tokenInfo);
      });
      return;
    }
    // A keyword gets here only for Lean's own data: its docs (shown above) or the proof state.
    if (tokenInfo.isKeyword) { presentNothing(tokenInfo); return; }
    if (tokenInfo.kind === 'term') { triggerTermLookup(tokenInfo); return; }
    const { token, subToken, boundingRect, shade } = tokenInfo;
    // A name in `(lean := "…")` is a declaration's full name, read as written.
    const lookup = tokenInfo.verso === 'name'
      ? { queryToken: tokenInfo.fullChain || tokenInfo.token, fileRef: null, contextText: '', local: null, receiver: null, namedArg: null, structField: null, skip: false, alt: null }
      : lookupContext(tokenInfo);
    if (lookup.skip) {
      if (tokenInfo.extras) presentNothing(tokenInfo);
      return;
    }

    // 0. Local variables shadow everything else: show their type.
    if (lookup.local) {
      present(tokenInfo, lookup.local);
      // (A written type with `Π i, …`, `∀ i, …` or `⨂[R] i, …` is printed with its binders' types.)
      const needsMore = lookup.local.inferNeeded || lookup.local.structureNeeded || lookup.local.replay ||
        /[∀Π⨂⨁]|\b(?:fun|λ)\b|\b(?:Type|Sort)\*/.test(lookup.local.typeSignature || '');
      if (needsMore) {
        const fileRef = window.VersoBinderContext && window.VersoBinderContext.fileRefFromDom(tokenInfo.textNode);
        refineLocal(lookup.local, lookup.contextText, fileRef).then((info) => {
          if (lastHoveredToken === token && info) present(tokenInfo, info);
        }).catch(() => { /* keep the provisional tooltip */ });
      }
      return;
    }

    // 1. Check if defined in current PR diff
    if (settings.enablePRScanner && window.LeanPRScanner) {
      // The typed name first (`SortedGT.sort_toFinset`), then the hovered word itself.
      const pr = window.LeanPRScanner;
      const prDecl = pr.find(lookup.queryToken) ||
        (lookup.queryToken === token || !lookup.queryToken.includes('.') ? pr.find(token) || (subToken ? pr.find(subToken) : null) : null);
      if (prDecl) {
        present(tokenInfo, prDecl);
        return;
      }
      // A namespace of the project (`IntegerRectangle` in `_root_.IntegerRectangle.IsTiling.normalized`).
      const ns = /^[A-Z][\w'.]*$/.test(lookup.queryToken) && !projectIndex ? projectNamespace(pr, lookup.queryToken) : null;
      if (ns) {
        present(tokenInfo, ns);
        return;
      }
      // The PR's files are still being read: try again once they are.
      if (projectIndex) {
        projectIndex.then(() => { if (lastHoveredToken === token) triggerHoverLookup(tokenInfo); });
        return;
      }
    }

    // 2. Check Built-ins (tactics, core types)
    if (settings.enableBuiltins && window.VersoBuiltins) {
      const builtin = window.VersoBuiltins.get(token) || (subToken ? window.VersoBuiltins.get(subToken) : null);
      if (builtin) {
        present(tokenInfo, builtin);
        return;
      }
    }

    // Single-letter identifiers are local variables, not global Mathlib definitions.
    // Without a file reference (to look for `variable` declarations) there is nothing to show.
    if (lookup.queryToken.length <= 1 && !lookup.fileRef) {
      if (tokenInfo.extras) presentNothing(tokenInfo);
      return;
    }

    // Dot notation on a local (`hl.nodup` with `hl : l.SortedLT`): resolve the field
    // in the namespace of the receiver's type, as Lean does (`List.SortedLT.nodup`).
    const { queryToken, fileRef, contextText, receiver, namedArg, structField } = lookup;

    // 3. Query background worker (Loogle)
    // To prevent flicker, do NOT show loading immediately.
    // If the lookup takes longer than 180ms, only then show a subtle loading spinner.
    if (loadingTimer) clearTimeout(loadingTimer);
    loadingTimer = setTimeout(() => {
      if (lastHoveredToken === token) {
        window.VersoTooltipView.showLoading(token, boundingRect, shade);
      }
    }, 180);

    try {
      chrome.runtime.sendMessage(
        {
          action: "LOOKUP_TOKEN", token: queryToken, subToken: subToken,
          fileRef: fileRef, contextText: contextText.slice(-4000),
          fullChain: tokenInfo.fullChain, alt: lookup.alt,
          tacticPosition: Boolean(tokenInfo.tacticPosition) && !receiver,
          receiver: receiver, namedArg: namedArg, structField: structField
        },
        (res) => {
          if (loadingTimer) {
            clearTimeout(loadingTimer);
            loadingTimer = null;
          }

          // Verify cursor hasn't moved away to another token while fetching
          if (lastHoveredToken !== token) return;

          if (res && res.success && res.data) {
            present(tokenInfo, res.data);
          } else {
            // Not found; quietly hide tooltip without flashing
            presentNothing(tokenInfo);
          }
        }
      );
    } catch (err) {
      if (loadingTimer) clearTimeout(loadingTimer);
      presentNothing(tokenInfo);
    }
  }

  /**
   * Handle mouse movements on GitHub code and diffs.
   * Uses hysteresis to prevent micro-jitter blinking.
   */
  function handleMouseMove(e) {
    if (!settings.enabled) return;

    // Ignore if tooltip is pinned
    if (window.VersoTooltipView.isPinned) return;

    // 1. Check if mouse is hovering over the tooltip itself
    const root = document.getElementById('verso-hover-root');
    if (root && root.contains(e.target)) {
      window.VersoTooltipView.clearHideTimer();
      // Don't let a token crossed on the way here replace the tooltip being read.
      if (hoverTimer) {
        clearTimeout(hoverTimer);
        hoverTimer = null;
        lastHoveredToken = null;
        lastHoveredRect = null;
      }
      return;
    }

    // 2. Hysteresis: if tooltip is visible, check if mouse is still inside the active token's area
    // (a name's; a term's area holds names with their own hovers). Narrow sideways, so the gap
    // next to a name (`f x`) can be hovered.
    if (window.VersoTooltipView.isVisible() && lastHoveredRect) {
      const padX = 3;
      const padY = 8;
      const inX = e.clientX >= (lastHoveredRect.left - padX) && e.clientX <= (lastHoveredRect.right + padX);
      const inY = e.clientY >= (lastHoveredRect.top - padY) && e.clientY <= (lastHoveredRect.bottom + padY);

      if (inX && inY) {
        // Mouse is still within the boundary of the active token; keep it stable!
        window.VersoTooltipView.clearHideTimer();
        return;
      }
    }

    // 3. Check if target is inside a Lean code block or diff
    if (!window.LeanTokenizer.isInsideLeanContext(e.target)) {
      if (hoverTimer) {
        clearTimeout(hoverTimer);
        hoverTimer = null;
      }
      if (loadingTimer) {
        clearTimeout(loadingTimer);
        loadingTimer = null;
      }
      lastHoveredToken = null;
      lastHoveredRect = null;
      window.VersoTooltipView.scheduleHide(180);
      return;
    }

    // 4. Extract Lean token at cursor
    let tokenInfo = window.LeanTokenizer.resolveTokenFromEvent(e);
    if (tokenInfo) {
      // (A word in a string is hovered only as a name in a Verso `(lean := "…")`.)
      const verso = versoState(tokenInfo);
      const names = (verso === 'name' || isPromise(verso)) && tokenInfo.kind !== 'term' && inLeanNames(tokenInfo);
      if (verso === 'prose' || isInProse(tokenInfo) || (isInString(tokenInfo) && !names) || isInAttribute(tokenInfo)) tokenInfo = null;
      else tokenInfo.verso = verso;
    }
    // (A keyword has a hover only from Lean's own data: its docs, and the proof state there.)
    if (!tokenInfo || !tokenInfo.token || (tokenInfo.isKeyword && !settings.enableHelper && !isDeclKeyword(tokenInfo))) {
      if (hoverTimer) {
        clearTimeout(hoverTimer);
        hoverTimer = null;
      }
      if (loadingTimer) {
        clearTimeout(loadingTimer);
        loadingTimer = null;
      }
      lastHoveredToken = null;
      lastHoveredRect = null;
      window.VersoTooltipView.scheduleHide(180);
      return;
    }

    // If still hovering the exact same token, keep tooltip active. (With Lean's own data, the
    // same text elsewhere is another hover: its proof state differs.)
    const rect = tokenInfo.boundingRect;
    const spot = settings.enableHelper && rect ? `${Math.round(rect.left)}:${Math.round(rect.top)}` : null;
    if (lastHoveredToken === tokenInfo.token && lastHoveredSpot === spot) {
      window.VersoTooltipView.clearHideTimer();
      return;
    }

    // New token hovered: clear pending timers
    if (hoverTimer) {
      clearTimeout(hoverTimer);
      hoverTimer = null;
    }
    if (loadingTimer) {
      clearTimeout(loadingTimer);
      loadingTimer = null;
    }

    lastHoveredToken = tokenInfo.token;
    lastHoveredSpot = spot;
    lastHoveredRect = tokenInfo.kind === 'term' ? null : tokenInfo.boundingRect;

    // Debounce hover before showing definition
    hoverTimer = setTimeout(() => {
      triggerHoverLookup(tokenInfo);
    }, settings.hoverDelay || 250);
  }

  /**
   * The pointer went into the infoview's panel, where hovers are shown while it is open (the
   * panel keeps its own mouse moves from `handleMouseMove`). A token crossed on the way there,
   * or one still being looked up, does not replace the hover being read.
   */
  function leaveForPanel(e) {
    const view = window.VersoTooltipView;
    if (!view.dock || !e.target || !e.target.closest || !e.target.closest('.lean-infoview')) return;
    if (hoverTimer) {
      clearTimeout(hoverTimer);
      hoverTimer = null;
    }
    if (loadingTimer) {
      clearTimeout(loadingTimer);
      loadingTimer = null;
    }
    lastHoveredToken = null;
    lastHoveredRect = null;
    lastHoveredSpot = null;
    activeHover = null;
    // (Takes away a lookup's loading bar; the hover shown stays.)
    view.hide(false);
  }

  /**
   * Bind event listeners.
   */
  function initListeners() {
    document.addEventListener('mousemove', handleMouseMove, { passive: true });
    document.addEventListener('mouseover', leaveForPanel, { passive: true });

    // Handle GitHub SPA soft navigations (Turbo / PJAX)
    const handleNavigation = () => {
      window.VersoTooltipView.hide(true);
      setTimeout(refreshOutline, 500);
      setTimeout(refreshInfoview, 500);
      setTimeout(() => {
        initPRScanner();
      }, 500);
    };

    document.addEventListener('turbo:render', handleNavigation);
    document.addEventListener('turbo:load', handleNavigation);
    document.addEventListener('pjax:end', handleNavigation);
    window.addEventListener('popstate', handleNavigation);
  }

  /**
   * Handle messages from Popup or Background
   */
  chrome.runtime.onMessage.addListener((request, sender, sendResponse) => {
    if (request.action === "GET_PAGE_INFO") {
      const isLean = window.LeanTokenizer.isInsideLeanContext(document.body) ||
                     Boolean(document.querySelector('.file-header[data-path$=".lean"], a[title$=".lean"]'));
      sendResponse({
        isLeanDetected: isLean,
        prDefinitionsCount: window.LeanPRScanner.declarations.size,
        declarations: Array.from(window.LeanPRScanner.declarations.values()).slice(0, 20)
      });
      return true;
    }

    if (request.action === "SETTINGS_UPDATED") {
      loadSettings();
      sendResponse({ success: true });
      return true;
    }
  });

  // Exposed for the test suite.
  window.VersoContentInternals = { receiverFor, lookupContext, isInProse, isInAttribute, isInString, refineLocal, triggerTermLookup, versoState, inLeanNames,
    triggerHoverLookup, exactCard, exactExtras, regionRanges, scrollBeside, isDeclKeyword, whereCard, leaveForPanel, setSettings: (values) => Object.assign(settings, values), hovering: (token) => { lastHoveredToken = token; } };

  // Startup
  loadSettings();
  initListeners();
  setTimeout(initPRScanner, 500);
})();
