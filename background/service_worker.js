/**
 * Background service worker for Lean Lens.
 * Coordinates definition queries across the local Lean helper, Loogle, and caches.
 */

// Shared binder parsing (also used by the content script).
if (typeof importScripts === 'function') {
  try { importScripts('../content/lean_terms.js', '../content/binder_context.js', '../content/pr_scanner.js', '../content/lean_outline.js'); } catch (err) { /* lookups still work without them */ }
  // Reading what the local helper's real Lean run produced.
  try { importScripts('exact_data.js'); } catch (err) { /* approximate hovers still work */ }
}

const SETTINGS_KEY = "lean_lens_settings";
const LEGACY_SETTINGS_KEY = "verso_settings";

const DEFAULT_SETTINGS = {
  enabled: true,
  hoverDelay: 250,
  enablePRScanner: true,
  enableBuiltins: true,
  enableLoogle: true,
  // The local helper (helper/lean-lens-helper.mjs) that runs real Lean on this machine.
  enableHelper: false,
  helperUrl: "http://127.0.0.1:5326",
  helperToken: "",
  // The outline button beside a Lean file (declarations, `open`, `variable`, placement hints).
  showOutline: true,
  theme: "auto"
};

// In-memory cache for speed during active review session
const memoryCache = new Map();
let queryStats = { totalQueries: 0, cacheHits: 0, loogleHits: 0, leanHits: 0 };

/**
 * Get stored settings merged with defaults.
 */
async function getSettings() {
  return new Promise((resolve) => {
    chrome.storage.local.get([SETTINGS_KEY, LEGACY_SETTINGS_KEY], (res) => {
      let saved = res[SETTINGS_KEY];
      // One-time migration from the extension's former name ("Verso").
      if (!saved && res[LEGACY_SETTINGS_KEY]) {
        saved = res[LEGACY_SETTINGS_KEY];
        chrome.storage.local.set({ [SETTINGS_KEY]: saved }, () => chrome.storage.local.remove(LEGACY_SETTINGS_KEY));
      }
      resolve(Object.assign({}, DEFAULT_SETTINGS, saved || {}));
    });
  });
}

/**
 * Determine declaration kind from signature or name.
 */
function inferKind(name, type, doc) {
  if (!name) return "def";
  const lowerName = name.toLowerCase();
  const lowerType = (type || "").toLowerCase();

  if (lowerName.includes("tactic") || lowerType.includes("tacticm")) return "tactic";
  if (lowerType.startsWith("class ") || lowerType.includes(" : class")) return "class";
  if (lowerType.startsWith("structure ")) return "structure";
  if (lowerType.startsWith("inductive ")) return "inductive";
  if (lowerType.includes(" : prop") || lowerType.includes("→ prop") || lowerName.endsWith("_iff") || lowerName.startsWith("theorem_")) {
    return "theorem";
  }
  return "def";
}

/**
 * Construct Mathlib4 docs deep-link URL.
 */
function getMathlibDocsUrl(moduleName, declName) {
  if (!moduleName || !declName) {
    return "https://leanprover-community.github.io/mathlib4_docs/";
  }
  const modPath = moduleName.replace(/\./g, "/");
  return `https://leanprover-community.github.io/mathlib4_docs/${modPath}.html#${encodeURIComponent(declName)}`;
}

/**
 * Query Loogle API raw endpoint.
 */
// Raw Loogle responses for this worker's lifetime: hovers and scope checks repeat queries.
const rawQueryCache = new Map();

async function queryLoogleRaw(queryStr) {
  if (rawQueryCache.has(queryStr)) return rawQueryCache.get(queryStr);
  const result = await queryLoogleRawUncached(queryStr);
  if (result !== undefined) {
    if (rawQueryCache.size > 1000) rawQueryCache.delete(rawQueryCache.keys().next().value);
    rawQueryCache.set(queryStr, result);
  }
  return result;
}

/** Returns hits, null for "no such name / no hits", or undefined on a network failure (not cached). */
async function queryLoogleRawUncached(queryStr) {
  try {
    const loogleUrl = `https://loogle.lean-lang.org/json?q=${encodeURIComponent(queryStr)}`;
    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), 3500);

    const response = await fetch(loogleUrl, {
      method: "GET",
      signal: controller.signal,
      headers: { "Accept": "application/json" }
    });
    clearTimeout(timeout);

    if (!response.ok) return undefined;
    const data = await response.json();
    if (data && Array.isArray(data.hits) && data.hits.length > 0) {
      return data.hits;
    }
    return null;
  } catch (err) {
    return undefined; // network error / timeout: let callers move on, don't cache
  }
}

const CACHE_VERSION = "v4";

/**
 * True if `name` ends with the dotted segments of `token`.
 * Qualifier segments compare case-insensitively, because dot notation writes the
 * receiver namespace in lowerCamelCase (`hl.sortedLE.pairwise` → `List.SortedLE.pairwise`).
 * The last segment must match exactly.
 */
function nameMatchesToken(name, token) {
  const nameSegs = name.split('.');
  const tokenSegs = token.split('.');
  if (tokenSegs.length > nameSegs.length) return false;
  const offset = nameSegs.length - tokenSegs.length;
  for (let i = 0; i < tokenSegs.length; i++) {
    const a = nameSegs[offset + i];
    const b = tokenSegs[i];
    const isLast = i === tokenSegs.length - 1;
    if (isLast ? a !== b : a.toLowerCase() !== b.toLowerCase()) return false;
  }
  return true;
}

/**
 * Choose the Loogle hit for a hovered token.
 * Returns { hit } for a confident match, { candidates } when the text alone can't decide
 * (we don't know the receiver's type), or null when nothing in `hits` fits.
 * Never falls back to an arbitrary hit: a wrong lemma is worse than no answer.
 */
function selectLoogleHit(hits, token, shortName) {
  if (!Array.isArray(hits) || hits.length === 0 || !token) return null;
  const last = shortName || token.split('.').pop();

  if (token.includes('.')) {
    const matches = hits.filter(h => h.name && nameMatchesToken(h.name, token));
    if (matches.length > 0) {
      const exact = matches.find(h => h.name === token);
      if (exact) return { hit: exact };
      if (matches.length === 1) return { hit: matches[0] };
      // Several namespaces end the same way (e.g. `Nonempty.mono` in Set and Finset):
      // an exact-case suffix can still single one out, otherwise we can't tell.
      const exactCase = matches.filter(h => h.name.endsWith('.' + token));
      if (exactCase.length === 1) return { hit: exactCase[0] };
      return { candidates: matches };
    }
    // Qualifier didn't match anything: we can only list what the last segment might be.
    const candidates = hits.filter(h => h.name && nameMatchesToken(h.name, last));
    return candidates.length > 0 ? { candidates } : null;
  }

  // Bare token: exact root declaration wins, then a unique suffix match.
  const exact = hits.find(h => h.name === token);
  if (exact) return { hit: exact };
  const matches = hits.filter(h => h.name && nameMatchesToken(h.name, token));
  if (matches.length === 1) return { hit: matches[0] };
  if (matches.length > 1) return { candidates: matches };
  return null;
}

const MAX_CANDIDATES_SHOWN = 8;

function buildAmbiguousResult(token, candidates) {
  const label = token.split('.').pop();
  const shown = candidates.slice(0, MAX_CANDIDATES_SHOWN);
  const more = candidates.length - shown.length;
  const lines = shown.map(h => `- \`${h.name}\``);
  if (more > 0) lines.push(`- …and ${more} more`);
  return {
    name: label,
    kind: "ambiguous",
    typeSignature: `-- ${candidates.length} possible declaration${candidates.length === 1 ? "" : "s"} named ${label}`,
    docstring:
      `Couldn't tell which \`${label}\` this is from the text alone: it depends on the type of the receiver, which only Lean knows. Possible matches:\n\n` +
      lines.join('\n'),
    module: "",
    source: "loogle",
    ambiguous: true,
    sourceUrl: `https://leanprover-community.github.io/mathlib4_docs/find/?pattern=${encodeURIComponent(label)}#doc`
  };
}

function hitToResult(hit) {
  const kind = inferKind(hit.name, hit.type, hit.doc);
  const moduleName = hit.module || "";
  const bc = self.VersoBinderContext;
  return {
    name: hit.name,
    kind: kind,
    // As Lean's hover prints it: `mul_pos.{u_1} {α : Type u_1} … : 0 < a * b`.
    typeSignature: hit.type ? (bc && bc.leanSignature ? bc.leanSignature(hit.name, hit.type) : `${hit.name} : ${hit.type}`) : `${kind} ${hit.name}`,
    docstring: hit.doc || "",
    module: moduleName,
    source: "loogle",
    sourceUrl: getMathlibDocsUrl(moduleName, hit.name)
  };
}

/**
 * Smart Loogle Query with automatic namespace resolution and substring search.
 * Resolves opened namespaces (e.g. ZeroAtFilter -> Filter.ZeroAtFilter) and dot notation.
 */
async function queryLoogle(token, subToken) {
  if (!token) return null;
  const shortName = subToken || (token.includes('.') ? token.split('.').pop() : token);

  // 1. Exact token, 2. substring search for the token, 3. substring search for the last segment.
  const candidateQueries = Array.from(new Set([token, `"${token}"`, `"${shortName}"`]));

  let ambiguous = null;
  for (const q of candidateQueries) {
    const hits = await queryLoogleRaw(q);
    const picked = selectLoogleHit(hits, token, shortName);
    if (!picked) continue;
    if (picked.hit) return hitToResult(picked.hit);
    if (!ambiguous) ambiguous = picked.candidates;
  }

  return ambiguous ? buildAmbiguousResult(token, ambiguous) : null;
}

// ---------------------------------------------------------------------------
// Tactic docs: Mathlib's tactic reference page, parsed once and cached.
// ---------------------------------------------------------------------------

const TACTIC_DOCS_URL = "https://leanprover-community.github.io/mathlib4_docs/tactics.html";
const TACTIC_CACHE_KEY = "tactic_docs_v1";
const TACTIC_CACHE_MS = 1000 * 60 * 60 * 24 * 7;
let tacticDocsPromise = null;

function decodeEntities(s) {
  return s
    .replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&quot;/g, '"')
    .replace(/&#39;|&#x27;/g, "'").replace(/&nbsp;/g, ' ')
    .replace(/&#(\d+);/g, (_, n) => String.fromCodePoint(+n))
    .replace(/&#x([0-9a-f]+);/gi, (_, n) => String.fromCodePoint(parseInt(n, 16)))
    .replace(/&amp;/g, '&');
}

/** doc-gen4 docstring HTML → the small Markdown subset the tooltip renders. */
function docHtmlToMarkdown(html) {
  const stripTags = (t) => t.replace(/<[^>]+>/g, '');
  let md = html
    .replace(/<pre[^>]*>\s*<code[^>]*>([\s\S]*?)<\/code>\s*<\/pre>/g, (_, code) => `\n\n\`\`\`lean\n${stripTags(code).trim()}\n\`\`\`\n\n`)
    .replace(/<code[^>]*>([\s\S]*?)<\/code>/g, (_, code) => '`' + stripTags(code) + '`')
    .replace(/<(strong|b)>([\s\S]*?)<\/\1>/g, '**$2**')
    .replace(/<(em|i)>([\s\S]*?)<\/\1>/g, '*$2*')
    .replace(/<li[^>]*>/g, '\n- ').replace(/<\/li>/g, '')
    .replace(/<\/?(ul|ol)[^>]*>/g, '\n')
    .replace(/<br\s*\/?>/g, '\n')
    .replace(/<\/?p[^>]*>/g, '\n\n');
  md = decodeEntities(stripTags(md));
  return md.replace(/[ \t]+\n/g, '\n').replace(/\n{3,}/g, '\n\n').trim();
}

/** Parse tactics.html into { name: { doc, module, anchor } } (first entry per name wins). */
function parseTacticDocs(html) {
  const docs = Object.create(null);
  const re = /<div id="([^"]+)"><div id="userName-[^"]*"><h2>([\s\S]*?)<\/h2>([\s\S]*?)<dl>([\s\S]*?)<\/dl>/g;
  let m;
  while ((m = re.exec(html)) !== null) {
    const name = decodeEntities(m[2].replace(/<[^>]+>/g, '')).trim();
    if (!/^[A-Za-z_][\w'!?]*$/.test(name) || docs[name]) continue; // (`docs` has no prototype: `constructor` is a tactic)
    const mod = (m[4].match(/Defined in module:<\/dt><dd><a[^>]*>([^<]+)<\/a>/) || [])[1] || '';
    docs[name] = { doc: docHtmlToMarkdown(m[3]), module: mod.trim(), anchor: decodeEntities(m[1]) };
  }
  return docs;
}

function getTacticDocs() {
  if (!tacticDocsPromise) {
    tacticDocsPromise = (async () => {
      const cached = await new Promise((res) => {
        try { chrome.storage.local.get([TACTIC_CACHE_KEY], (r) => res(r && r[TACTIC_CACHE_KEY])); } catch (err) { res(null); }
      });
      if (cached && Date.now() - cached.timestamp < TACTIC_CACHE_MS) return cached.docs;
      const html = await fetchText(TACTIC_DOCS_URL, 15000);
      if (!html) return cached ? cached.docs : {};
      const docs = parseTacticDocs(html);
      try { chrome.storage.local.set({ [TACTIC_CACHE_KEY]: { timestamp: Date.now(), docs } }); } catch (err) { /* ignore */ }
      return docs;
    })().catch(() => { tacticDocsPromise = null; return {}; });
  }
  return tacticDocsPromise;
}

// Docstrings of notations (`«term_+_»`, `Lean.Parser.Term.paren`, `BigOperators.bigsum`, …),
// shown under a term's type as Lean's hover does. Read from Loogle, kept for a week.
const NOTATION_DOC_KEY = "notation_docs_v1";
let notationDocsPromise = null; // Promise<{ [name]: { doc, timestamp } }>

async function notationDoc(name) {
  if (!name) return null;
  if (!notationDocsPromise) {
    notationDocsPromise = new Promise((res) => {
      try { chrome.storage.local.get([NOTATION_DOC_KEY], (r) => res((r && r[NOTATION_DOC_KEY]) || {})); } catch (err) { res({}); }
    });
  }
  const docs = await notationDocsPromise;
  const entry = ownEntry(docs, name);
  if (entry && Date.now() - entry.timestamp < TACTIC_CACHE_MS) return entry.doc;
  const hits = await queryLoogleRaw(name);
  if (hits === undefined) return entry ? entry.doc : null; // offline: keep what we had
  const hit = hits && hits.find(h => h.name === name);
  docs[name] = { doc: (hit && hit.doc) || '', timestamp: Date.now() };
  try { chrome.storage.local.set({ [NOTATION_DOC_KEY]: docs }); } catch (err) { /* ignore */ }
  return docs[name].doc;
}

// Heads Lean unfolds for generalized field notation when the field isn't found under them.
const UNFOLD_HEADS = { 'GE.ge': 'LE.le', 'GT.gt': 'LT.lt', 'HasSuperset.Superset': 'HasSubset.Subset', 'HasSSuperset.SSuperset': 'HasSSubset.SSubset' };
Object.setPrototypeOf(UNFOLD_HEADS, null); // looked up by words from the source: no `constructor`, `toString`, … from Object

/** `table[key]` if it's the table's own entry (tables read back from storage have Object's prototype). */
function ownEntry(table, key) {
  return table && Object.prototype.hasOwnProperty.call(table, key) ? table[key] : undefined;
}

async function lookupTactic(token) {
  if (!token || token.includes('.')) return null;
  const docs = await getTacticDocs();
  // `choose!`, `simp?`: variants documented under the tactic's name.
  const entry = docs && (ownEntry(docs, token) || ownEntry(docs, token.replace(/[!?]+$/, '')));
  if (!entry) return null;
  return {
    name: token,
    kind: 'tactic',
    typeSignature: `tactic ${token}`,
    docstring: entry.doc,
    module: entry.module,
    source: 'loogle',
    sourceUrl: `${TACTIC_DOCS_URL}#${encodeURIComponent(entry.anchor)}`
  };
}

// ---------------------------------------------------------------------------
// File scope: which namespaces a bare identifier can resolve in at a given line.
// ---------------------------------------------------------------------------

const SCOPE_DECL = /^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|public|noncomputable|scoped|partial|nonrec|unsafe|meta)\s+)*(theorem|lemma|def|abbrev|instance|opaque|example|structure|class|inductive)\b\s*([^\s(:{\[⦃]*)/;

/** Remove `--` line comments and (nested) `/- … -/` block comments, carrying depth across lines. */
function stripLeanComments(line, state) {
  let out = '';
  for (let i = 0; i < line.length; i++) {
    if (line.startsWith('/-', i)) { state.depth++; i++; continue; }
    if (state.depth > 0) {
      if (line.startsWith('-/', i)) { state.depth--; i++; }
      continue;
    }
    if (line.startsWith('--', i)) break;
    out += line[i];
  }
  return out;
}

/** Parse the body of an `open` command into [{ ns, only }] (scoped/renaming opens give no names). */
function parseOpen(body) {
  const result = [];
  const re = /([^\s()]+)(?:\s*\(([^)]*)\))?/g;
  let m;
  while ((m = re.exec(body)) !== null) {
    const word = m[1];
    // `open scoped X`: only X's notations and instances, no names (kept for `notationScopeAt`).
    if (word === 'scoped') return parseOpen(body.slice(re.lastIndex)).map(o => Object.assign(o, { scoped: true }));
    if (word === 'hiding' || word === 'renaming' || word === '→' || word === 'in') break;
    result.push({ ns: word, only: m[2] ? m[2].trim().split(/\s+/) : null });
  }
  return result;
}

function prefixesOf(ns) {
  const segs = ns.split('.').filter(Boolean);
  const out = [];
  for (let k = segs.length; k > 0; k--) out.push(segs.slice(0, k).join('.'));
  return out;
}

/**
 * Namespaces in scope at 1-based `line` of a Lean file, most specific first:
 * the declaration's own namespace, the current `namespace` chain, then `open`s
 * (innermost scope and latest `open` first). Each entry: { ns, only }.
 */
function scopeAt(text, line, withScoped = false) {
  const { frames, declNs, declOpenIn } = walkScope(text, line);
  const ordered = [];
  const seen = new Set();
  const add = (ns, only = null, origin = 'open', scoped = false) => {
    if (scoped && !withScoped) return;
    const key = ns + '|' + (only ? only.join(',') : '');
    if (seen.has(key)) return;
    seen.add(key);
    ordered.push({ ns, only, origin });
  };
  if (declNs) prefixesOf(declNs).forEach(ns => add(ns, null, 'namespace'));
  const cur = frames.filter(f => f.kind === 'namespace').map(f => f.name).join('.');
  if (cur) prefixesOf(cur).forEach(ns => add(ns, null, 'namespace'));
  // Later `open` commands first; names within one command keep source order.
  declOpenIn.forEach(o => add(o.ns, o.only, 'open', o.scoped));
  for (let f = frames.length - 1; f >= 0; f--) {
    frames[f].opens.slice().reverse().forEach(group => group.forEach(o => add(o.ns, o.only, 'open', o.scoped)));
  }
  return ordered;
}

// Scoped notations, in force where their namespace is open (or is the current one): token →
// [[namespace, constant as written, namespace it was declared in]]. Generated from Mathlib's
// `scoped[NS] notation "t" => c` (a single constant). `I` without `open unitInterval` is a
// constant (`Complex.I` with `open Complex`).
const SCOPED_NOTATIONS = {
  "AffineSpace": [["Affine", "AddTorsor", ""]],
  "D": [["Derivative", "normalizedDerivOfComplex", "Derivative"]],
  "D∃": [["Dioph", "Dioph.vec_ex1_dioph", "Dioph"]],
  "I": [["unitInterval", "unitInterval", ""]],
  "L": [["LSeries.notation", "LSeries", ""]],
  "cexp": [["Complex", "Complex.exp", "Complex"]],
  "d⁄dX": [["PowerSeries", "derivative", "PowerSeries"]],
  "log⁺": [["Real", "posLog", "Real"]],
  "rexp": [["Real", "Real.exp", "Real"]],
  "Δ": [["Laplacian", "Laplacian.laplacian", "Laplacian"], ["CategoryTheory.Bicategory", "Comonad.comul", "CategoryTheory.Bicategory"], ["CategoryTheory.ComonObj", "ComonObj.comul", "CategoryTheory.ComonObj"]],
  "Ι": [["Interval", "Set.uIoc", "Set"]],
  "Λ": [["ArithmeticFunction", "ArithmeticFunction.vonMangoldt", "ArithmeticFunction.to"]],
  "Ω": [["ArithmeticFunction.Omega", "ArithmeticFunction.cardFactors", "ArithmeticFunction"], ["Topology.Homotopy", "LoopSpace", ""]],
  "Ω^": [["Topology.Homotopy", "GenLoop", ""]],
  "α_": [["CategoryTheory.Bicategory", "Bicategory.associator", "CategoryTheory.Bicategory"], ["CategoryTheory.Limits.CatCospanTransform", "CatCospanTransform.associator", "CategoryTheory.Limits.CatCospanTransform"], ["CategoryTheory.MonoidalCategory", "MonoidalCategoryStruct.associator", "CategoryTheory.MonoidalCategory"]],
  "γ": [["CategoryTheory.MonObj", "ModObj.smul", "CategoryTheory.ModObj"]],
  "δ": [["CategoryTheory.AddMonObj", "AddModObj.vadd", "CategoryTheory.AddModObj"], ["LSeries.notation", "delta", ""], ["RingTheory.LinearMap", "CoalgebraStruct.comul", ""]],
  "ε": [["DualNumber", "DualNumber.eps", ""], ["Hyperreal", "Hyperreal.epsilon", "Hyperreal"], ["CategoryTheory.Bicategory", "Comonad.counit", "CategoryTheory.Bicategory"], ["CategoryTheory.ComonObj", "ComonObj.counit", "CategoryTheory.ComonObj"], ["RingTheory.LinearMap", "CoalgebraStruct.counit", ""]],
  "ζ": [["CategoryTheory.AddMonObj", "AddMonObj.zero", "CategoryTheory.AddMonObj"], ["ArithmeticFunction.zeta", "ArithmeticFunction.zeta", "ArithmeticFunction"]],
  "η": [["CategoryTheory.MonObj", "MonObj.one", "CategoryTheory.MonObj"], ["ModularForm", "eta", "ModularForm"], ["OrderType", "OrderType.eta", "OrderType"]],
  "θ": [["Chebyshev", "Chebyshev.theta", "Chebyshev"], ["OrderType", "OrderType.theta", "OrderType"]],
  "ι": [["CategoryTheory.MonObj", "GrpObj.inv", "CategoryTheory.MonObj"]],
  "λ": [["ArithmeticFunction.carmichael", "ArithmeticFunction.carmichael", "ArithmeticFunction"]],
  "λ_": [["CategoryTheory.Bicategory", "Bicategory.leftUnitor", "CategoryTheory.Bicategory"], ["CategoryTheory.Limits.CatCospanTransform", "CatCospanTransform.leftUnitor", "CategoryTheory.Limits.CatCospanTransform"], ["CategoryTheory.MonoidalCategory", "MonoidalCategoryStruct.leftUnitor", "CategoryTheory.MonoidalCategory"]],
  "μ": [["CategoryTheory.MonObj", "MonObj.mul", "CategoryTheory.MonObj"], ["ArithmeticFunction.Moebius", "ArithmeticFunction.moebius", "ArithmeticFunction"]],
  "π": [["FundamentalGroupoid", "FundamentalGroupoid.fundamentalGroupoidFunctor", "FundamentalGroupoid"], ["Real", "Real.pi", "Real"], ["Nat.Prime", "Nat.primeCounting", "Nat"]],
  "π'": [["Nat.Prime", "Nat.primeCounting'", "Nat"]],
  "π_": [["Topology", "HomotopyGroup.Pi", ""]],
  "πₓ": [["FundamentalGroupoid", "FundamentalGroupoid.fundamentalGroupoidFunctor.obj", "FundamentalGroupoid"]],
  "πₘ": [["FundamentalGroupoid", "FundamentalGroupoid.fundamentalGroupoidFunctor.map", "FundamentalGroupoid"]],
  "ρ_": [["CategoryTheory.Bicategory", "Bicategory.rightUnitor", "CategoryTheory.Bicategory"], ["CategoryTheory.Limits.CatCospanTransform", "CatCospanTransform.rightUnitor", "CategoryTheory.Limits.CatCospanTransform"], ["CategoryTheory.MonoidalCategory", "MonoidalCategoryStruct.rightUnitor", "CategoryTheory.MonoidalCategory"]],
  "σ": [["CategoryTheory.AddMonObj", "AddMonObj.add", "CategoryTheory.AddMonObj"], ["ArithmeticFunction.sigma", "ArithmeticFunction.sigma", "ArithmeticFunction"], ["unitInterval", "unitInterval.symm", "unitInterval"]],
  "φ": [["Nat", "Nat.totient", "Nat"], ["goldenRatio", "Real.goldenRatio", "Real"]],
  "ψ": [["Chebyshev", "Chebyshev.psi", "Chebyshev"], ["goldenRatio", "Real.goldenConj", "Real"]],
  "ω": [["QuadraticAlgebra", "omega", "QuadraticAlgebra"], ["Hyperreal", "Hyperreal.omega", "Hyperreal"], ["omegaLimit", "omegaLimit", ""], ["ArithmeticFunction.omega", "ArithmeticFunction.cardDistinctFactors", "ArithmeticFunction"], ["OrderType", "OrderType.omega0", "OrderType"], ["Ordinal", "Ordinal.omega0", "Ordinal"]],
  "ℍ": [["UpperHalfPlane", "UpperHalfPlane", ""]],
  "ℑ": [["ComplexStarModule", "imaginaryPart", ""]],
  "ℕ∪{∞}": [["LightProfinite", "NatUnionInfty", "LightProfinite"]],
  "ℙ": [["LinearAlgebra.Projectivization", "Projectivization", ""], ["ProbabilityTheory", "MeasureTheory.MeasureSpace.volume", ""]],
  "ℛ": [["Coalgebra", "Coalgebra.Repr.arbitrary", ""]],
  "ℜ": [["ComplexStarModule", "realPart", ""]],
  "ℝ≥0": [["NNReal", "NNReal", "NNReal"]],
  "ℝ≥0∞": [["ENNReal", "ENNReal", ""]],
  "ℵ₀": [["Cardinal", "Cardinal.aleph0", "Cardinal"]],
  "∂L": [["CategoryTheory.Distributive", "leftDistrib", "CategoryTheory.Distributive"]],
  "∂R": [["CategoryTheory.Distributive", "rightDistrib", "CategoryTheory.Distributive"]],
  "∇": [["Gradient", "gradient", ""]],
  "∞": [["OnePoint", "OnePoint.infty", "OnePoint"]],
  "∠": [["EuclideanGeometry", "EuclideanGeometry.angle", "EuclideanGeometry"]],
  "∡": [["EuclideanGeometry", "EuclideanGeometry.oangle", "EuclideanGeometry"]],
  "𝐞": [["FourierTransform", "Real.fourierChar", "Real"]],
  "𝑳": [["LieGroup", "smoothLeftMul", ""]],
  "𝑹": [["LieGroup", "smoothRightMul", ""]],
  "𝒅": [["Manifold", "fdifferential", ""]],
  "𝒅ₕ": [["Manifold", "hfdifferential", ""]],
  "𝒟": [["Modular", "ModularGroup.fd", "ModularGroup"]],
  "𝒟ᵒ": [["Modular", "ModularGroup.fdo", "ModularGroup"]],
  "𝒮": [["CategoryTheory.HopfObj", "HopfObj.antipode", "CategoryTheory.HopfObj"]],
  "𝓕": [["FourierTransform", "fourier", "FourierTransform"], ["ZMod", "dft", "ZMod"]],
  "𝓕⁻": [["FourierTransform", "fourierInv", "FourierTransform"]],
  "𝓝": [["Topology", "nhds", ""]],
  "𝓝ˢ": [["Topology", "nhdsSet", ""]],
  "𝓞": [["NumberField", "NumberField.RingOfIntegers", "NumberField"]],
  "𝓟": [["Filter", "Filter.principal", "Filter"]],
  "𝓤": [["Uniformity", "uniformity", ""]],
  "𝔠": [["Cardinal", "Cardinal.continuum", "Cardinal"]],
  "𝔻": [["Complex.UnitDisc", "Complex.UnitDisc", "Complex"]],
  "𝕋": [["HeckeCosetModule", "HeckeRing", ""]],
  "𝕔𝔻": [["Complex.UnitDisc", "Complex.UnitClosedDisc", "Complex"]],
  "𝟭": [["CategoryTheory.BasedFunctor", "BasedFunctor.id", "CategoryTheory.BasedFunctor"]]
};
Object.setPrototypeOf(SCOPED_NOTATIONS, null);

/**
 * The notation `token` in force at `line` of `text` (the latest `open` of its namespace wins):
 * the names its constant may have, most likely first, or null.
 */
function notationTarget(token, text, line) {
  const options = SCOPED_NOTATIONS[token];
  if (!options || !text || !line) return null;
  for (const s of scopeAt(text, line, true)) {
    if (s.only) continue;
    const hit = options.find(([ns]) => ns === s.ns);
    if (!hit) continue;
    const [, constant, declaredIn] = hit;
    return declaredIn && !constant.startsWith(declaredIn + '.') ? [`${declaredIn}.${constant}`, constant] : [constant];
  }
  return null;
}

/** The constant a scoped notation stands for at `fileRef`'s line: its lookup result, or null. */
async function scopedNotation(token, fileRef) {
  if (!SCOPED_NOTATIONS[token] || !fileRef || !fileRef.line) return null;
  for (const constant of notationTarget(token, await getFileText(fileRef), fileRef.line) || []) {
    const hit = await loogleExact(constant);
    if (hit && hit.type) return hitToResult(hit);
  }
  return null;
}

/**
 * `variable` commands still in scope at 1-based `line`, as [{ text, line }], outermost first.
 */
function variablesAt(text, line) {
  const { frames } = walkScope(text, line);
  return frames.flatMap(f => f.variables);
}

/** Walk a Lean file up to `line`, tracking namespace/section frames, opens and variables (cached). */
const walkScopeCache = new Map(); // file text → Map(line → walk)
function walkScope(text, line) {
  let perText = walkScopeCache.get(text);
  if (!perText) {
    perText = new Map();
    walkScopeCache.set(text, perText);
    if (walkScopeCache.size > 4) walkScopeCache.delete(walkScopeCache.keys().next().value);
  }
  if (!perText.has(line)) perText.set(line, walkScopeUncached(text, line));
  return perText.get(line);
}

function walkScopeUncached(text, line) {
  const lines = text.split('\n');
  const frames = [{ kind: 'root', name: '', opens: [], variables: [] }];
  const state = { depth: 0 };
  let pendingOpenIn = [];
  let declOpenIn = [];
  let declNs = null;
  let openVariable = null; // `variable` command whose indented continuation lines we're reading

  const upto = Math.min(line, lines.length);
  for (let i = 0; i < upto; i++) {
    const raw = stripLeanComments(lines[i], state);
    let t = raw.trim();
    if (openVariable && t && /^\s/.test(raw)) { openVariable.text += '\n' + raw; continue; }
    openVariable = null;
    if (!t) continue;
    if (/^variable\b/.test(t)) {
      openVariable = { text: t, line: i + 1 };
      frames[frames.length - 1].variables.push(openVariable);
      continue;
    }
    let m;
    const openIn = t.match(/^open\s+(.*?)\s+in\b\s*(.*)$/);
    if (openIn) {
      pendingOpenIn = parseOpen(openIn[1]);
      t = openIn[2].trim();
      if (!t) continue;
    }
    if ((m = t.match(/^namespace\s+(\S+)/))) {
      frames.push({ kind: 'namespace', name: m[1], opens: [], variables: [] });
    } else if (/^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|public|private)\s+)*section\b/.test(t)) {
      frames.push({ kind: 'section', name: '', opens: [], variables: [] });
    } else if (/^end\b/.test(t)) {
      if (frames.length > 1) frames.pop();
    } else if ((m = t.match(/^open\s+(.*)$/))) {
      frames[frames.length - 1].opens.push(parseOpen(m[1]));
    } else if ((m = t.match(SCOPE_DECL))) {
      const cur = frames.filter(f => f.kind === 'namespace').map(f => f.name).join('.');
      let name = m[2] || '';
      let abs = false;
      if (name.startsWith('_root_.')) { name = name.slice(7); abs = true; }
      const parent = name.includes('.') ? name.slice(0, name.lastIndexOf('.')) : '';
      declNs = parent ? (abs || !cur ? parent : `${cur}.${parent}`) : null;
      if (m[1] === 'structure' || m[1] === 'class' || m[1] === 'inductive') {
        declNs = abs || !cur ? name : `${cur}.${name}`;
      }
      declOpenIn = pendingOpenIn;
      pendingOpenIn = [];
    }
  }
  return { frames, declNs, declOpenIn };
}

/** A `variable`-declared name at `fileRef.line`, as tooltip data, or null. */
async function lookupFileVariable(token, fileRef) {
  const bc = self.VersoBinderContext;
  if (!bc || !fileRef || !fileRef.line) return null;
  const text = await getFileText(fileRef);
  if (!text) return null;
  // As Lean elaborates it there: the latest `variable` of that name, `Type*` named `Type u_8`.
  const scanner = self.LeanPRScanner;
  const scoped = scanner && scanner.variablesAt ? scanner.variablesAt(text, fileRef.line) : [];
  const scopedType = (n) => { for (let j = scoped.length - 1; j >= 0; j--) if (scoped[j].name === n) return scoped[j].type; return null; };
  for (let k = scoped.length - 1; k >= 0; k--) {
    if (scoped[k].name !== token) continue;
    if (!scoped[k].type) return null; // the declaration's own untyped binder (`{ι}`) shadows it
    const shown = bc.annotateText ? bc.annotateText(scoped[k].type, scopedType) : scoped[k].type;
    const declaredAt = variablesAt(text, fileRef.line).filter(v => bc.findBinderType(token, v.text)).map(v => v.line).pop();
    return {
      name: token, kind: 'variable', source: 'local_var', declaredAt, rawType: scoped[k].type,
      typeSignature: `${token} : ${shown}`,
      docstring: declaredAt ? `Declared with \`variable\` at line ${declaredAt} of this file.` : 'Declared with `variable` in this file.'
    };
  }
  const vars = variablesAt(text, fileRef.line);
  // Later `variable` commands shadow earlier ones.
  for (let k = vars.length - 1; k >= 0; k--) {
    const type = bc.findBinderType(token, vars[k].text);
    if (type) {
      return {
        name: token, kind: 'variable', source: 'local_var', declaredAt: vars[k].line, rawType: type,
        typeSignature: `${token} : ${type}`,
        docstring: `Declared with \`variable\` at line ${vars[k].line} of this file.`
      };
    }
  }
  return null;
}

const fileTextCache = new Map(); // key → Promise<string|null>
const prRevisionCache = new Map(); // owner/repo#pr → Promise<{head, base}|null>

async function fetchText(url, ms = 5000, init = {}) {
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), ms);
  try {
    const res = await fetch(url, Object.assign({ signal: controller.signal }, init));
    return res.ok ? await res.text() : null;
  } catch (err) {
    return null;
  } finally {
    clearTimeout(timer);
  }
}

/**
 * The path of a GitHub URL made from parts a page names (owner, repository, commit, the file's
 * path), or null when a part would not stay one part. Each is encoded, so a `/`, `?` or `#`
 * in it stays inside it; and none may be empty, `.` or `..`, which the URL would resolve, so
 * that `/owner/repo/blob/..%2F..%2Fsettings/x.lean` cannot make the worker fetch some other
 * page of github.com with the user's session.
 */
function githubPath(...parts) {
  const segments = parts.map(part => String(part == null ? '' : part));
  if (segments.some(s => s === '' || s === '.' || s === '..')) return null;
  return segments.map(encodeURIComponent).join('/');
}

function getPrRevision(owner, repo, pr) {
  const key = `${owner}/${repo}#${pr}`;
  const at = /^\d+$/.test(String(pr)) ? githubPath(owner, repo) : null;
  if (!at) return Promise.resolve(null);
  if (!prRevisionCache.has(key)) {
    prRevisionCache.set(key, fetchText(`https://api.github.com/repos/${at}/pulls/${pr}`).then(t => {
      if (!t) return null;
      const j = JSON.parse(t);
      return { head: j.head && j.head.sha, base: j.base && j.base.sha };
    }).catch(() => null));
  }
  return prRevisionCache.get(key);
}

async function getFileText(fileRef) {
  let sha = fileRef.sha;
  if (!sha && fileRef.pr) {
    const rev = await getPrRevision(fileRef.owner, fileRef.repo, fileRef.pr);
    sha = rev && (fileRef.side === 'left' ? rev.base : rev.head);
  }
  if (!sha || !fileRef.path) return null;
  const repoPath = githubPath(fileRef.owner, fileRef.repo);
  const filePath = githubPath(sha, ...String(fileRef.path).split('/'));
  if (!repoPath || !filePath) return null;
  const key = `${fileRef.owner}/${fileRef.repo}@${sha}:${fileRef.path}`;
  if (!fileTextCache.has(key)) {
    if (fileTextCache.size > 300) fileTextCache.delete(fileTextCache.keys().next().value);
    fileTextCache.set(key, fetchText(`https://raw.githubusercontent.com/${repoPath}/${filePath}`)
      // Private repositories: github.com's raw endpoint with the user's GitHub session.
      .then(t => t !== null ? t : fetchText(`https://github.com/${repoPath}/raw/${filePath}`, 8000, { credentials: 'include' })));
  }
  return fileTextCache.get(key);
}

/** Modules a Lean file imports (`import A.B`, `public import A.B`, `import all A`). */
function importsOf(text) {
  const out = [];
  const re = /^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.'«»]+)/gm;
  let m;
  while ((m = re.exec(text)) !== null) out.push(m[1]);
  return out;
}

/**
 * Declarations in a PR's Lean files, read from the files at the PR's commit rather than the
 * page (GitHub collapses large diffs). Outside Mathlib, also the project files they import,
 * following imports within the repository (Loogle only knows Mathlib).
 */
// Packages a project imports that aren't in its repository (their files aren't fetched).
const EXTERNAL_ROOTS = new Set(['Mathlib', 'Batteries', 'Std', 'Lean', 'Init', 'Lake', 'Aesop', 'Qq', 'ProofWidgets',
  'Plausible', 'LeanSearchClient', 'ImportGraph', 'Verso', 'VersoManual', 'VersoBlog', 'VersoBlueprint', 'SubVerso',
  'MD4Lean', 'Cli', 'Duper', 'Auto', 'LeanCopilot', 'Canonical', 'Hammer', 'Archive', 'Counterexamples']);

// The declarations last read from a PR's files (per revision), for receivers of the
// project's own types (`(T i).y₀` with `variable {T : ι → Rectangle}`: `Rectangle.y₀`).
const projectIndexCache = new Map(); // `owner/repo@sha` → declarations

/** A declaration of the project named `name` (or `….name`), at `fileRef`'s revision; or null. */
function projectDeclaration(name, fileRef) {
  const list = fileRef && projectIndexCache.get(`${fileRef.owner}/${fileRef.repo}@${fileRef.sha}`);
  if (!list) return null;
  return list.find(d => d.name === name) || list.find(d => d.name.endsWith('.' + name)) || null;
}

async function projectDeclarations({ owner, repo, pr, sha, paths }) {
  const scanner = self.LeanPRScanner;
  if (!scanner || !paths || !paths.length) return [];
  if (!sha && pr) {
    const rev = await getPrRevision(owner, repo, pr);
    sha = rev && rev.head;
  }
  if (!sha) return [];
  const isMathlib = /^leanprover-community\/mathlib4?$/i.test(`${owner}/${repo}`);
  const roots = new Set(paths.map(p => p.split('/')[0].replace(/\.lean$/, '')));
  const changed = new Set(paths);
  const queue = paths.filter(p => p.endsWith('.lean'));
  const seen = new Set();
  const decls = [];
  const limit = isMathlib ? queue.length : 120;
  while (queue.length && seen.size < limit) {
    const batch = [];
    while (queue.length && batch.length < 8 && seen.size + batch.length < limit) {
      const p = queue.shift();
      if (!seen.has(p) && !batch.includes(p)) batch.push(p);
    }
    batch.forEach(p => seen.add(p));
    const texts = await Promise.all(batch.map(p => getFileText({ owner, repo, sha, path: p })));
    batch.forEach((p, k) => {
      const text = texts[k];
      if (!text) return;
      for (const d of scanner.scanSource(text, p)) {
        decls.push(Object.assign(d, { inPR: changed.has(p), repo: `${owner}/${repo}`, sha }));
      }
      if (isMathlib) return;
      // The repository's own modules: also those outside the PR's folders (a blueprint chapter
      // `DifferentProofsBlueprint/…` imports `DifferentProofs.…`).
      for (const mod of importsOf(text)) {
        const root = mod.split('.')[0];
        if (!roots.has(root) && EXTERNAL_ROOTS.has(root)) continue;
        const fp = mod.replace(/\./g, '/') + '.lean';
        if (!seen.has(fp) && !queue.includes(fp)) queue.push(fp);
      }
    });
  }
  const key = `${owner}/${repo}@${sha}`;
  projectIndexCache.delete(key);
  projectIndexCache.set(key, decls);
  if (projectIndexCache.size > 4) projectIndexCache.delete(projectIndexCache.keys().next().value);
  return decls;
}

/** Does `name` exist? Returns the Loogle hit for it, or null. */
async function loogleExact(name) {
  const hits = await queryLoogleRaw(name);
  if (!hits) return null;
  let hit = hits.find(h => h.name === name);
  if (!hit) {
    const more = await queryLoogleRaw(`"${name}"`);
    hit = more && more.find(h => h.name === name);
  }
  return hit || { name, type: '', doc: '', module: '' };
}

/**
 * A root name that is really an `export`ed class field (`mul_zero` → `MulZeroClass.mul_zero`,
 * `star` → `Star.star`, `algebraMap` → `Algebra.algebraMap`). Loogle doesn't know the short name.
 * A class-field projection has a `[self : Class …]` binder.
 */
async function exportedClassField(token) {
  if (!/^[a-z][\w'!?]*$/.test(token)) return null;
  const isField = (h) => {
    const ns = h.name.slice(0, h.name.length - token.length - 1);
    return ns && h.type && h.type.includes(`[self : ${ns}`) && !h.name.startsWith('Lean.');
  };
  const guess = await loogleExact(`${token[0].toUpperCase()}${token.slice(1)}.${token}`);
  if (guess && isField(guess)) return guess;
  const hits = await queryLoogleRaw(`"${token}"`);
  return (hits || []).find(h => h.name.endsWith('.' + token) && isField(h)) || null;
}

/**
 * Resolve a bare identifier using the namespaces open at its line, as Lean would.
 * `contextText` (the enclosing declaration) breaks ties between several real candidates.
 */
async function resolveInScope(token, scope, contextText) {
  const candidates = [];
  const origin = new Map();
  for (const { ns, only, origin: o } of scope) {
    if (only && !only.includes(token)) continue;
    const name = `${ns}.${token}`;
    if (!origin.has(name)) origin.set(name, o);
    candidates.push(name);
  }
  candidates.push(token);
  const unique = Array.from(new Set(candidates)).slice(0, 12);
  const found = (await Promise.all(unique.map(loogleExact))).filter(h => h && h.type);
  if (!token.includes('.') && !found.some(h => h.name === token)) {
    // The root name may be an exported class field; treat it as the root candidate.
    const exported = await exportedClassField(token);
    if (exported) {
      const result = hitToResult(exported);
      result.docstring = `*\`${token}\` is exported from \`${exported.name}\`.*\n\n${result.docstring}`;
      return result;
    }
  }
  if (found.length === 0) return null;
  if (found.length === 1) return hitToResult(found[0]);
  const withNote = (hit, why) => {
    const result = hitToResult(hit);
    const others = found.filter(h => h !== hit).map(h => `\`${h.name}\``).join(', ');
    result.docstring = `*Also in scope here: ${others}. ${why}*\n\n${result.docstring}`;
    return result;
  };

  // A root name wins: Mathlib marks clashing namespaced names `protected`, and those
  // aren't reachable by `open` or by being inside the namespace.
  const root = found.find(h => h.name === token);
  if (root) return withNote(root, 'Picked the root declaration (namespaced ones with the same name are usually `protected`).');

  // The declaration's / current namespace beats `open`ed ones in practice
  // (Lean would try all and keep the one that typechecks).
  const own = found.filter(h => origin.get(h.name) === 'namespace');
  if (own.length >= 1 && own.length < found.length) {
    return withNote(own[0], 'Picked the one in the current namespace.');
  }

  // Several real candidates (Lean would pick by type). Prefer one whose namespace
  // is mentioned in the declaration, and say what else was in scope.
  const ctx = contextText || '';
  const mentioned = found.filter(h => {
    const ns = h.name.slice(0, h.name.length - token.length - 1);
    return ns && new RegExp(`(^|[^\\w.])${ns.replace(/\./g, '\\.')}(?![\\w])`).test(ctx);
  });
  if (mentioned.length === 1) return withNote(mentioned[0], 'Picked by the types used in this declaration.');
  return buildAmbiguousResult(token, found);
}

async function lookupInFileScope(token, fileRef, contextText, allowDotted = false) {
  if (!fileRef || !fileRef.line || (token.includes('.') && !allowDotted)) return null;
  const text = await getFileText(fileRef);
  if (!text) return null;
  // An empty scope still checks the root name (`mul_zero` in a file with no `open`).
  return resolveInScope(token, scopeAt(text, fileRef.line), contextText);
}

/**
 * Handle Token Lookup.
 */
/** Top-level binder groups of a Loogle signature (before ` : conclusion`): [{ names, type }]. */
function signatureBinders(sig) {
  const groups = [];
  const pairs = { '(': ')', '{': '}', '[': ']', '⦃': '⦄' };
  let i = 0;
  while (i < sig.length) {
    while (i < sig.length && /\s/.test(sig[i])) i++; // groups may be separated by newlines
    const open = sig[i];
    if (!pairs[open]) break;
    let depth = 0, j = i;
    for (; j < sig.length; j++) {
      if ('({[⦃⟨'.includes(sig[j])) depth++;
      else if (')}]⦄⟩'.includes(sig[j])) { depth--; if (depth === 0) break; }
    }
    const group = sig.slice(i + 1, j);
    const colon = group.indexOf(' : ');
    // A default value (`(left_inv : LeftInverse invFun toFun := by …)`) isn't part of the type.
    const dflt = colon === -1 ? -1 : group.indexOf(' := ', colon);
    const type = group.slice(colon + 3, dflt === -1 ? group.length : dflt).replace(/\s+/g, ' ').trim();
    if (colon !== -1) groups.push({ names: group.slice(0, colon).trim().split(/\s+/), type, explicit: open === '(' });
    else groups.push({ names: [], type: group.trim(), explicit: false }); // anonymous instance `[Fact p]`
    i = j + 1;
  }
  return groups;
}

function replaceWord(text, name, value) {
  // Not inside a longer name or a field access `x.name`; after a range `a..name` it counts.
  const esc = name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  return text.replace(new RegExp(`(?<![\\w'\\u2080-\\u209C])(?<!(?:^|[^.])\\.)${esc}(?![\\w'\\u2080-\\u209C])`, 'g'), () => value);
}

/**
 * Type produced by applying constant `constName` to a receiver of type `receiverType`
 * (when given): the signature's conclusion, with the parameters of the receiver's binder
 * substituted from the receiver's type. `Fact.out` on `Fact (0 < T)` → `(0 < T)`.
 */
async function resultType(constName, receiverType) {
  const bc = self.VersoBinderContext;
  const hit = await loogleExact(constName);
  if (!bc || !hit || !hit.type) return null;
  let conclusion = bc.conclusionOf(hit.type);
  if (!conclusion) return null;
  if (receiverType && bc.receiverResultType) {
    // Match the receiver against its parameter as terms (handles `a ↔ b`, `a ≤ b`, …).
    const viaTerms = bc.receiverResultType(hit.type, receiverType);
    if (viaTerms) return { type: viaTerms, sig: hit.type };
  }
  const binders = signatureBinders(hit.type);
  if (receiverType) {
    const recvHead = bc.typeHead(receiverType, null);
    const strip = (x) => {
      x = x.trim();
      while (x.startsWith('(') && x.endsWith(')')) x = x.slice(1, -1).trim();
      return x;
    };
    const recvArgs = bc.splitApp(strip(receiverType)).slice(1);
    const binder = binders.find(b => bc.typeHead(b.type, null) === recvHead);
    if (binder) {
      const params = bc.splitApp(strip(binder.type)).slice(1);
      // Simultaneous substitution via placeholders (parameters may name each other's arguments).
      const subst = [];
      params.forEach((p, k) => {
        if (recvArgs[k] === undefined || !/^[\w'Ͱ-Ͽ₀-₉]+$/.test(p)) return;
        const arg = recvArgs[k];
        subst.push([p, /\s/.test(arg) && !/^\(.*\)$/.test(arg) ? `(${arg})` : arg]);
      });
      subst.forEach(([p], k) => { conclusion = replaceWord(conclusion, p, `\u0000${k}\u0000`); });
      subst.forEach(([, v], k) => { conclusion = conclusion.split(`\u0000${k}\u0000`).join(v); });
    }
  }
  // Dot notation in the conclusion (`l.SortedLE`) is typed via the signature's own binders.
  return { type: conclusion, sig: hit.type };
}

function namespaceOfType(type, sig) {
  const bc = self.VersoBinderContext;
  if (!bc || !type) return null;
  const resolveVar = (v) => {
    const vt = sig ? bc.findBinderType(v, sig) : null;
    return vt ? bc.typeHead(vt, null) : null;
  };
  return bc.typeHead(type, resolveVar);
}

/** Namespace of the type a constant produces (no receiver to substitute from). */
async function resultNamespace(constName) {
  const r = await resultType(constName, null);
  return r ? namespaceOfType(r.type, r.sig) : null;
}

/**
 * Full name of a possibly-unqualified constant at `fileRef` (via the file's
 * namespaces/opens), or the name itself.
 */
async function qualifyConstant(name, fileRef) {
  if (name.includes('.') || !fileRef) return name;
  const direct = await loogleExact(name);
  if (direct && direct.type) return name;
  const scoped = await lookupInFileScope(name, fileRef, '');
  return scoped && !scoped.ambiguous ? scoped.name : name;
}

// Anonymous projections `.1` / `.2` of common types, by name.
const NUMERIC_FIELDS = {
  'Iff': ['mp', 'mpr'], 'And': ['left', 'right'], 'Prod': ['fst', 'snd'], 'PProd': ['fst', 'snd'],
  'Sigma': ['fst', 'snd'], 'PSigma': ['fst', 'snd'], 'Subtype': ['val', 'property']
};
Object.setPrototypeOf(NUMERIC_FIELDS, null);

/** Name of field number `n` of structure `ns` (from the table, or `ns.mk`'s explicit binders). */
/** Fields of structure `ns` in order, from `ns.mk`'s explicit parameters: [{ name, type }]. */
async function structureFields(ns) {
  const hit = await loogleExact(`${ns}.mk`);
  if (!hit || !hit.type) return null;
  return signatureBinders(hit.type).filter(b => b.explicit).flatMap(b => b.names.map(name => ({ name, type: b.type })));
}

async function numericFieldName(ns, n) {
  if (NUMERIC_FIELDS[ns]) return NUMERIC_FIELDS[ns][n - 1] || null;
  const fields = await structureFields(ns);
  return (fields && fields[n - 1] && fields[n - 1].name) || null;
}

/**
 * The field reached by anonymous projections `.index.rest…` of a value of structure type
 * `type` (`e.1` with `e : α ≃ β` is `Equiv.toFun : α → β`): { name, type, structure } or null.
 */
async function structureField(type, index, rest) {
  const bc = self.VersoBinderContext;
  if (!bc) return null;
  let head = bc.typeHead(type, null);
  let current = null;
  for (const n of [index, ...(rest || [])]) {
    if (!head) return null;
    const fields = await structureFields(head);
    const field = fields && fields[n - 1];
    if (!field) return null;
    current = { name: field.name, type: field.type, structure: head };
    head = bc.typeHead(field.type, null);
  }
  return current;
}

/**
 * A field's hover in its place: `Nat.even_add_one.mp` shows `Even (n + 1) → ¬Even n` rather than
 * `Iff.mp`'s general `a → b`, which stays below it. `head` is the receiver chain's first name with
 * its type (a variable) or its signature (a constant); `fields` the constants after it.
 */
function fieldResultInPlace(result, hit, head, fields) {
  const terms = self.LeanTerms;
  const bc = self.VersoBinderContext;
  if (!terms || !terms.fieldChainInPlace || !bc || !bc.leanSignature || !head) return result;
  const printed = (h) => bc.leanSignature(h.name, h.type);
  let placed = null;
  try {
    placed = terms.fieldChainInPlace(head, fields.map((f) => ({ text: f.text, name: f.hit.name, signature: printed(f.hit) })));
  } catch (err) {
    placed = null;
  }
  if (!placed) return result;
  return Object.assign({}, result, {
    name: placed.term,
    typeSignature: placed.signature,
    docstring: `Worked out from \`${head.name}\` and \`${hit.name}\`:\n\n\`\`\`lean\n${result.typeSignature}\n\`\`\`${result.docstring ? `\n\n${result.docstring}` : ''}`
  });
}

/** `const.path₁.….field`, typing each step from Loogle signatures. */
async function resolveReceiverChain(receiver, field, fileRef) {
  if (!receiver || !receiver.const || !field) return null;
  // Track the receiver's full type, so later steps can substitute from it.
  let current = null; // { type, sig }
  // The chain's first name as Lean would show it, to say what the field is in its place.
  let head = null;
  const steps = [];
  const bc0 = self.VersoBinderContext;
  if (receiver.maybeVariable) {
    // A file-level `variable` first (`hT.out` with `variable [hT : Fact (0 < T)]`).
    const v = fileRef ? await lookupFileVariable(receiver.const, fileRef) : null;
    const bc = self.VersoBinderContext;
    current = v
      ? { type: receiver.applied && bc ? bc.conclusionOf(v.rawType) : v.rawType, sig: null }
      : await resultType(await qualifyConstant(receiver.const, fileRef), null);
    if (v && !receiver.applied) head = { name: receiver.const, type: v.rawType };
  } else {
    const name = await qualifyConstant(receiver.const, fileRef);
    current = await resultType(name, null);
    if (current && current.sig && !receiver.applied && bc0 && bc0.leanSignature) head = { name, signature: bc0.leanSignature(name, current.sig) };
  }
  const named = async (ns, f) => (/^\d+$/.test(f) ? await numericFieldName(ns, parseInt(f, 10)) : f);
  for (const step of receiver.path || []) {
    const ns = current && namespaceOfType(current.type, current.sig);
    const name = ns && await named(ns, step);
    if (!name) return null;
    const stepHit = head ? await loogleExact(`${ns}.${name}`) : null;
    if (stepHit && stepHit.type) steps.push({ text: step, hit: stepHit }); else head = null;
    current = await resultType(`${ns}.${name}`, current.type);
  }
  const ns = current && namespaceOfType(current.type, current.sig);
  const name = ns && await named(ns, field);
  if (!name) return null;
  const hit = await loogleExact(`${ns}.${name}`);
  if (hit && hit.type) return fieldResultInPlace(hitToResult(hit), hit, head, [...steps, { text: field, hit }]);
  // The project's own type (`Rectangle.y₀`, a field of a structure of the PR).
  const own = projectDeclaration(`${ns}.${name}`, fileRef);
  return own ? Object.assign({}, own) : null;
}

/** `Foo` in `Foo.bar` when `Foo` is only a namespace: a short tooltip listing a few members. */
async function lookupNamespace(token, fullChain) {
  if (!/^[A-Z][\w'.]*$/.test(token)) return null;
  const hits = await queryLoogleRaw(`"${token}."`);
  const members = (hits || []).filter(h => h.name.startsWith(token + '.'));
  // The rest of the hovered name (`Order.lt_one_iff`) proves the namespace exists.
  let nsName = token;
  if (fullChain && fullChain.startsWith(token + '.') && !members.some(h => h.name === fullChain)) {
    const named = await loogleExact(fullChain);
    if (named && named.type) {
      members.unshift(named);
    } else {
      // Opened namespace: `AdjoinSimple.gen` is `IntermediateField.AdjoinSimple.gen`.
      const sub = await queryLoogleRaw(`"${fullChain}"`);
      const full = (sub || []).find(h => h.name.endsWith('.' + fullChain));
      if (full) {
        nsName = full.name.slice(0, full.name.length - fullChain.length + token.length);
        members.unshift(full);
      }
    }
  }
  if (members.length === 0) return null;
  const sample = members.slice(0, 6).map(h => `- \`${h.name}\``).join('\n');
  return {
    name: nsName, kind: 'namespace', source: 'loogle',
    typeSignature: `namespace ${nsName}`,
    docstring: `A namespace, not a declaration. Some of its members:\n\n${sample}`,
    sourceUrl: `https://leanprover-community.github.io/mathlib4_docs/find/?pattern=${encodeURIComponent(token)}#doc`
  };
}

/**
 * Conclusion of constant application `term` (`le_or_gt b 1`), with its explicit and named
 * arguments substituted: `b ≤ 1 ∨ 1 < b`.
 */
async function applicationType(term, fileRef) {
  const bc = self.VersoBinderContext;
  const head = bc && bc.applicationHead(term);
  if (!head) return null;
  const hit = await loogleExact(await qualifyConstant(head, fileRef));
  if (!hit || !hit.type) return null;
  let conclusion = bc.conclusionOf(hit.type);
  if (!conclusion) return null;
  const explicitNames = signatureBinders(hit.type).filter(b => b.explicit).flatMap(b => b.names);
  const named = Object.create(null);
  const positional = [];
  for (const a of bc.splitApp(term).slice(1)) {
    const nm = a.match(/^\(\s*([\w'\u0370-\u03FF\u2080-\u209C]+)\s*:=\s*([\s\S]+)\)$/);
    if (nm) named[nm[1]] = nm[2].trim();
    else positional.push(a);
  }
  const wrap = (a) => (/\s/.test(a) && !/^[(⟨]/.test(a) ? `(${a})` : a);
  // Simultaneous substitution (`a ↦ b, b ↦ 1` must not turn `a` into `1`): placeholders first.
  const subst = [];
  explicitNames.forEach((n, k) => {
    if (positional[k] !== undefined && positional[k] !== '_') subst.push([n, wrap(positional[k])]);
  });
  for (const [n, v] of Object.entries(named)) subst.push([n, wrap(v)]);
  subst.forEach(([n], k) => { conclusion = replaceWord(conclusion, n, `\u0000${k}\u0000`); });
  subst.forEach(([, v], k) => { conclusion = conclusion.split(`\u0000${k}\u0000`).join(v); });
  // More arguments than explicit binders: the conclusion is a function; apply it.
  for (let extra = positional.length - explicitNames.length; extra > 0; extra--) {
    const cut = conclusion.indexOf(' → ');
    if (cut === -1) break;
    conclusion = conclusion.slice(cut + 3);
  }
  return { type: conclusion, name: hit.name };
}

/** Types for `obtain PAT := TERM` / `rcases TERM with PAT` when TERM is a constant application. */
async function inferPattern(request) {
  const bc = self.VersoBinderContext;
  if (!bc || !request || !request.term || !request.pattern) return null;
  const app = await applicationType(request.term, request.fileRef);
  if (!app) return null;
  const out = new Map();
  bc.destructure(bc.parsePattern(request.pattern), app.type, out);
  const types = (out.get(request.name) || []).filter(t => t.type);
  if (!types.length) return null;
  const f = bc.formatInferred(request.name, { types, caseIdx: request.caseIdx || 0 });
  return { typeSignature: f.typeSignature, note: f.note, from: app.name, conclusion: app.type };
}

/** `fn (arg := …)`: the type of fn's parameter `arg`, from its signature. */
async function lookupNamedArg(namedArg, fileRef) {
  const bc = self.VersoBinderContext;
  if (!bc || !namedArg || !namedArg.fn) return null;
  const hit = await loogleExact(await qualifyConstant(namedArg.fn, fileRef));
  const info = hit && hit.type ? bc.namedArgInfo(namedArg.arg, hit.name, hit.type) : null;
  return info || {
    name: namedArg.arg, kind: 'variable', source: 'local_var',
    typeSignature: `(${namedArg.arg} := …)`,
    docstring: `Named argument \`${namedArg.arg}\` of \`${namedArg.fn}\` (its type isn't in the visible signature, e.g. it comes from a \`variable\`).`
  };
}

async function handleLookupToken(token, subToken, fileRef, contextText, tacticPosition, receiver, namedArg, structField, fullChain) {
  queryStats.totalQueries++;

  // `field := …` in a structure instance: `Struct.field`, else say what it is.
  if (structField) {
    const hit = await loogleExact(token);
    if (hit && hit.type) return hitToResult(hit);
    return {
      name: structField.field, kind: 'variable', source: 'local_var',
      typeSignature: `${structField.field} := …`,
      docstring: `Field \`${structField.field}\` of the \`${structField.ns}\` being built here (possibly inherited from a parent structure).`
    };
  }

  if (namedArg) {
    const arg = await lookupNamedArg(namedArg, fileRef);
    if (arg) return arg;
  }

  // `adjoin.finiteDimensional` with `open IntermediateField` is the namespaced lemma
  // `IntermediateField.adjoin.finiteDimensional`, not dot notation: check that first.
  if (receiver && receiver.maybeVariable && !receiver.applied && fileRef) {
    const dotted = [receiver.const, ...(receiver.path || []), token].join('.');
    const named = await lookupInFileScope(dotted, fileRef, contextText, true);
    if (named && !named.ambiguous && named.typeSignature && !(named.kind === 'def' && named.source !== 'loogle')) return named;
  }

  // `(f a).field` / `h.f₁.f₂.field`: Lean resolves `field` in the receiver's type.
  if (receiver) {
    const resolved = await resolveReceiverChain(receiver, token, fileRef);
    if (resolved) return resolved;
  }

  // In tactic position (`by fun_prop`, `· positivity`, `<;> simp`), a bare word is a tactic.
  if (tacticPosition && token && !token.includes('.')) {
    const tactic = await lookupTactic(token);
    if (tactic) return tactic;
  }

  // Bare identifiers depend on the file's `variable`s, `namespace`s and `open`s,
  // so they bypass the token cache.
  if (fileRef && token && !token.includes('.')) {
    const variable = await lookupFileVariable(token, fileRef);
    if (variable) return variable;
    const notation = await scopedNotation(token, fileRef);
    if (notation) return notation;
    // One-letter lowercase names are locals; uppercase ones can be constants (`X`, `C`, `I`).
    if (token.length <= 1 && !/^[A-Z]$/.test(token)) return null;
    const settings = await getSettings();
    if (settings.enableLoogle) {
      const scoped = await lookupInFileScope(token, fileRef, contextText);
      if (scoped) {
        queryStats.loogleHits++;
        return scoped;
      }
    }
  }

  // 1. Check in-memory cache
  if (memoryCache.has(token)) {
    queryStats.cacheHits++;
    return memoryCache.get(token);
  }

  // 2. Check storage cache
  const cacheKey = `cache_${CACHE_VERSION}_${token}`;
  const cached = await new Promise((res) => {
    chrome.storage.local.get([cacheKey], (result) => res(result[cacheKey]));
  });
  if (cached && Date.now() - cached.timestamp < 1000 * 60 * 60 * 24 * 7) {
    queryStats.cacheHits++;
    memoryCache.set(token, cached.data);
    return cached.data;
  }

  const settings = await getSettings();

  // 3. Try Loogle API (with smart namespace and substring resolution)
  if (settings.enableLoogle) {
    let loogleResult = await queryLoogle(token, subToken);
    if (!loogleResult || loogleResult.ambiguous) {
      // Tactics aren't declarations, so Loogle can't find them.
      loogleResult = (await lookupTactic(token)) || loogleResult;
    }
    if ((!loogleResult || loogleResult.ambiguous) && token.includes('.')) {
      // `h.trans` with `h : a ≥ b`: without `GE.ge.trans`, Lean unfolds `≥` to `≤` (`LE.le.trans`).
      const unfolded = Object.entries(UNFOLD_HEADS).find(([from]) => token.startsWith(from + '.'));
      if (unfolded) {
        const hit = await loogleExact(unfolded[1] + token.slice(unfolded[0].length));
        if (hit && hit.type) loogleResult = hitToResult(hit);
      }
    }
    if ((!loogleResult || loogleResult.ambiguous) && token.includes('.') && fileRef) {
      // `Tendsto.sub` from a type head written unqualified (`open Filter`): qualify it in scope.
      const [first, ...rest] = token.split('.');
      const qualified = await qualifyConstant(first, fileRef);
      if (qualified !== first) {
        const hit = await loogleExact(`${qualified}.${rest.join('.')}`);
        if (hit && hit.type) loogleResult = hitToResult(hit);
      }
    }
    if ((!loogleResult || loogleResult.ambiguous) && token.includes('.')) {
      // `MultilinearMap.ext_iff.mp`, `Finset.univ.erase`: a constant followed by fields.
      const segs = token.split('.');
      for (let k = segs.length - 1; k >= 1 && (!loogleResult || loogleResult.ambiguous); k--) {
        const head = segs.slice(0, k).join('.');
        const exists = await loogleExact(head);
        if (!exists || !exists.type) continue;
        const viaFields = await resolveReceiverChain({ const: head, path: segs.slice(k, -1) }, segs[segs.length - 1], fileRef);
        if (viaFields) loogleResult = viaFields;
      }
    }
    // A namespace segment (`ENNReal.Tendsto` in `ENNReal.Tendsto.const_mul`) rather than a lemma.
    if ((!loogleResult || (loogleResult.ambiguous && fullChain && fullChain.startsWith(token + '.')))) {
      loogleResult = (await lookupNamespace(token, fullChain)) || loogleResult;
    }
    if (loogleResult) {
      queryStats.loogleHits++;
      // Ambiguous results may come from a transient failure of the more specific
      // queries, so keep them out of the persistent cache.
      if (!loogleResult.ambiguous) {
        memoryCache.set(token, loogleResult);
        chrome.storage.local.set({
          [cacheKey]: { timestamp: Date.now(), data: loogleResult }
        });
      }
      return loogleResult;
    }
  }

  return null;
}

// ---------------------------------------------------------------------------------------------
// The local helper: real Lean, run on this machine (helper/lean-lens-helper.mjs).

/**
 * One request to the helper. Resolves to its JSON answer, or to `{state}` when there is none:
 * 'off' (not set up), 'offline' (not running), 'unauthorized' (wrong token), 'not_allowed'
 * (the repository is not allowed yet), 'error'.
 */
async function helperRequest(path, { body, settings, timeout = 6000 } = {}) {
  const s = settings || await getSettings();
  if (!s.enableHelper || !s.helperUrl || !s.helperToken) return { state: 'off' };
  let timer = null;
  try {
    const controller = new AbortController();
    timer = setTimeout(() => controller.abort(), timeout);
    const res = await fetch(new URL(path, s.helperUrl).toString(), {
      method: body ? 'POST' : 'GET',
      headers: Object.assign({ 'X-Lean-Lens-Token': s.helperToken }, body ? { 'Content-Type': 'application/json' } : {}),
      body: body ? JSON.stringify(body) : undefined,
      signal: controller.signal
    });
    if (res.status === 401) return { state: 'unauthorized' };
    const json = await res.json().catch(() => null);
    if (res.status === 403) return { state: 'not_allowed', repo: json && json.repo };
    if (!res.ok || !json) return { state: 'error', error: (json && json.error) || `The helper answered ${res.status}` };
    return json;
  } catch (err) {
    return { state: 'offline' };
  } finally {
    if (timer) clearTimeout(timer);
  }
}

// What the helper said about a file: its data once Lean has run, else a short-lived state.
const exactCache = new Map(); // owner/repo@sha:path → { until, value: Promise<{state, data?, …}> }
const EXACT_FILES_KEPT = 40;

async function commitOf(fileRef) {
  if (fileRef.sha) return fileRef.sha;
  if (!fileRef.pr) return null;
  const rev = await getPrRevision(fileRef.owner, fileRef.repo, fileRef.pr);
  return rev && (fileRef.side === 'left' ? rev.base : rev.head);
}

function exactFile(repo, sha, path) {
  const key = `${repo}@${sha}:${path}`;
  const cached = exactCache.get(key);
  if (cached && (cached.until === Infinity || cached.until > Date.now())) return cached.value;
  const entry = { until: Date.now() + 1000, value: null };
  entry.value = helperRequest('/file', { body: { repo, sha, path }, timeout: 15000 }).then((res) => {
    if (res.state === 'ready' && res.data && self.LeanLensExact && res.data.version === self.LeanLensExact.FORMAT_VERSION) {
      entry.until = Infinity; // a commit's file never changes
      return res;
    }
    if (res.state === 'ready') return { state: 'error', error: 'The helper and the extension are different versions' };
    // Not there yet: ask again soon, but not on every mouse move. A stopped helper is asked rarely.
    entry.until = Date.now() + (res.state === 'offline' || res.state === 'off' ? 8000 : 1000);
    return res;
  });
  if (exactCache.size >= EXACT_FILES_KEPT) exactCache.delete(exactCache.keys().next().value);
  exactCache.set(key, entry);
  return entry.value;
}

/** What Lean recorded at `request.column` of the file line `request.fileRef` names. */
async function exactHover(request) {
  const fileRef = request.fileRef;
  if (!fileRef || !fileRef.path || !fileRef.line || !self.LeanLensExact) return { state: 'off' };
  const settings = await getSettings();
  if (!settings.enableHelper || !settings.helperToken) return { state: 'off' };
  const sha = await commitOf(fileRef);
  if (!sha) return { state: 'off' };
  const repo = `${fileRef.owner}/${fileRef.repo}`;
  const file = await exactFile(repo, sha, fileRef.path);
  if (file.state !== 'ready') return Object.assign({}, file, { repo, sha, data: undefined });
  queryStats.leanHits++;
  return Object.assign({ state: 'ready', repo, sha },
    self.LeanLensExact.describe(file.data, fileRef.line, request.column, request.columnEnd, request.caret, request.chain, request.chainColumn));
}

// ---------------------------------------------------------------------------------------------
// A file's outline, what is in force at a declaration (`#where`), and where it might belong.

const outlineCache = new Map(); // file text (+ base text) → { entries, hints, added }

/**
 * The outline of the file `fileRef` names, at the commit the page shows. On a pull request's
 * own side, the declarations it adds (`added`, their lines) and placement hints for those;
 * elsewhere, hints for none (`hints` then only lists similar declarations on request).
 */
async function fileOutline(fileRef) {
  const outline = self.LeanOutline;
  if (!outline || !fileRef || !fileRef.path) return null;
  const text = await getFileText(Object.assign({}, fileRef, { line: undefined }));
  if (text === null || text === undefined) return null;
  const onPrSide = Boolean(fileRef.pr) && fileRef.side !== 'left';
  const base = onPrSide ? await getFileText(Object.assign({}, fileRef, { side: 'left', sha: fileRef.baseSha || undefined })) : undefined;
  const key = `${fileRef.owner}/${fileRef.repo}:${fileRef.path}\u0000${text}\u0000${onPrSide ? base : ''}`;
  if (outlineCache.has(key)) return outlineCache.get(key);
  const entries = outline.outline(text);
  let added = null;
  let hints = [];
  if (onPrSide) {
    // A file the pull request creates has no base: all of it is new.
    const lines = outline.addedLines(base === null ? null : base, text);
    added = entries.filter((e) => e.kind === 'decl' && lines.has(e.line)).map((e) => e.line);
    hints = outline.placementHints(text, new Set(added), entries).filter((h) => h.hints.length);
  }
  const result = {
    text, entries, added, hints, sha: await commitOf(fileRef),
    slim: entries.map((e) => ({
      kind: e.kind, line: e.line, endLine: e.endLine, depth: e.depth, text: e.text.split('\n')[0].slice(0, 160),
      name: e.name || '', fullName: e.fullName || '', declKind: e.declKind || '', prefixes: e.prefixes || []
    }))
  };
  if (outlineCache.size > 12) outlineCache.delete(outlineCache.keys().next().value);
  outlineCache.set(key, result);
  return result;
}

/** What is in force at `fileRef.line` (`#where`), the declaration there, and where it might belong. */
async function declWhere(fileRef) {
  const outline = self.LeanOutline;
  const file = await fileOutline(fileRef);
  if (!file || !fileRef.line) return null;
  const ctx = outline.contextAt(file.text, fileRef.line, file.entries);
  const decl = ctx.decl;
  const placed = decl && decl.name ? outline.placementHints(file.text, new Set([decl.line]), file.entries)[0] : null;
  const isNew = Boolean(decl && file.added && file.added.includes(decl.line));
  return {
    where: outline.whereText(ctx),
    namespace: ctx.namespace,
    decl: decl ? { kind: decl.declKind, name: decl.name, fullName: decl.fullName, line: decl.line, endLine: decl.endLine } : null,
    isNew,
    similar: placed ? placed.similar : [],
    // Hints about placement only for what the pull request adds (the rest was there before).
    hints: placed && (isNew || !file.added) && fileRef.pr ? placed.hints : []
  };
}

/** Every step of the proof the recorded tactic `request.index` of a file is in (the stepper). */
async function exactSteps(request) {
  const fileRef = request.fileRef;
  if (!fileRef || !fileRef.path || !self.LeanLensExact || typeof request.index !== 'number') return { steps: [] };
  const sha = await commitOf(fileRef);
  if (!sha) return { steps: [] };
  const file = await exactFile(`${fileRef.owner}/${fileRef.repo}`, sha, fileRef.path);
  if (file.state !== 'ready') return { steps: [] };
  const exact = self.LeanLensExact;
  return {
    steps: exact.stepsOfProof(file.data, request.index)
      .map((step) => Object.assign(step, { messages: exact.messagesAt(file.data, step.range[0], step.range[1]) }))
  };
}

/** Start Lean on files of a commit. The page only sends this after a click. */
async function helperRun(request) {
  const sha = request.sha || await commitOf(request);
  if (!sha) return { state: 'error', error: 'This page does not say which commit it shows' };
  const repo = `${request.owner}/${request.repo}`;
  if (request.allow) {
    const allowed = await helperRequest('/allow', { body: { repo } });
    if (!allowed.ok) return allowed;
  }
  const res = await helperRequest('/run', { body: { repo, sha, pr: request.pr ? Number(request.pr) : undefined, paths: request.paths } });
  // Forget "not there yet" answers, so the next hover asks again.
  for (const [key, entry] of exactCache) if (entry.until !== Infinity) exactCache.delete(key);
  return Object.assign({ repo, sha }, res);
}

/**
 * Message Dispatcher
 */
/**
 * A lookup with an alternative reading (`alt`: e.g. the codomain of a coerced bundled map):
 * use the alternative when the primary one finds nothing definite.
 */
async function handleLookupWithAlt(request) {
  const run = (token, receiver) => handleLookupToken(token, request.subToken, request.fileRef, request.contextText,
    request.tacticPosition, receiver, request.namedArg, request.structField, request.fullChain);
  const primary = await run(request.token, request.receiver);
  const alt = request.alt;
  if (alt && (!primary || primary.ambiguous || primary.kind === 'namespace')) {
    const second = alt.token ? await run(alt.token, null) : await run(alt.field, alt.chain);
    if (second && !second.ambiguous) return second;
  }
  return primary;
}

// Message handlers: each returns the response (or a promise of it).
const MESSAGE_HANDLERS = {
  LOOKUP_TOKEN: async (request) => {
    const result = await handleLookupWithAlt(request);
    return { success: Boolean(result), data: result };
  },
  PROJECT_DECLARATIONS: async (request) => ({ declarations: await projectDeclarations(request) }),
  // Statement of a rewrite rule's constant, for replaying `rw … at h` in the page.
  CONSTANT_SIGNATURE: async (request) => {
    const hit = await loogleExact(await qualifyConstant(request.name, request.fileRef));
    return hit && hit.type ? { name: hit.name, type: hit.type } : null;
  },
  INFER_PATTERN: (request) => inferPattern(request),
  NOTATION_DOC: async (request) => ({ doc: await notationDoc(request.name) }),
  // A file-level `variable` (`[hT : Fact (0 < T)]`) for typing terms around a hovered gap.
  FILE_VARIABLE: async (request) => {
    const v = await lookupFileVariable(request.name, request.fileRef);
    return v ? { type: v.rawType } : null;
  },
  // The instance arguments the file's `variable`s have at a line (for out-params Lean finds by
  // instance search: `[RingHomInvPair σ₁₂ σ₂₁]` gives `(f i).symm : t i ≃ₛₗ[σ₂₁] s i`).
  FILE_INSTANCES: async (request) => {
    const text = request.fileRef && request.fileRef.line ? await getFileText(request.fileRef) : null;
    const scanner = self.LeanPRScanner;
    if (!text || !scanner || !scanner.variablesAt) return { instances: [] };
    return { instances: scanner.variablesAt(text, request.fileRef.line).filter(v => v.bi === '[' && v.type).map(v => v.type) };
  },
  // Where a Verso document (`#doc … =>`) starts in a file, and its ```lean blocks.
  VERSO_REGIONS: async (request) => {
    const text = request.fileRef ? await getFileText(request.fileRef) : null;
    return text && self.LeanPRScanner && self.LeanPRScanner.versoRegions ? self.LeanPRScanner.versoRegions(text) : null;
  },
  STRUCTURE_FIELD: async (request) => {
    const f = await structureField(request.type, request.index, request.rest);
    return f ? { field: { name: f.name, type: f.type }, structure: f.structure } : null;
  },
  GET_SETTINGS: async () => ({ success: true, settings: await getSettings(), stats: queryStats }),
  SET_SETTINGS: (request) => new Promise((resolve) => {
    chrome.storage.local.set({ [SETTINGS_KEY]: request.settings }, () => resolve({ success: true }));
  }),
  CLEAR_CACHE: () => new Promise((resolve) => {
    memoryCache.clear();
    rawQueryCache.clear();
    fileTextCache.clear();
    exactCache.clear();
    tacticDocsPromise = null;
    notationDocsPromise = null;
    // Remove cached lookups only; keep the user's settings.
    chrome.storage.local.get(null, (all) => {
      const keys = Object.keys(all || {}).filter(k => k.startsWith('cache_') || k === TACTIC_CACHE_KEY || k === NOTATION_DOC_KEY);
      chrome.storage.local.remove(keys, () => resolve({ success: true }));
    });
  }),
  // What Lean itself recorded at a position of a file (from the local helper), if it has run.
  EXACT_HOVER: (request) => exactHover(request),
  // Ask the helper to run Lean on files of a commit (only ever after a click in the page).
  HELPER_RUN: (request) => helperRun(request),
  // A file's outline (with the scope commands), the declarations a PR adds, and hints for those.
  FILE_OUTLINE: async (request) => {
    const file = await fileOutline(request.fileRef);
    return file ? { entries: file.slim, added: file.added, hints: file.hints, sha: file.sha } : null;
  },
  // `#where` at a declaration: its namespaces, `open`s, `variable`s, `include`s and `omit`s.
  DECL_WHERE: (request) => declWhere(request.fileRef),
  // The proof a hovered tactic is in, step by step, for stepping through it in the tooltip.
  EXACT_STEPS: (request) => exactSteps(request),
  HELPER_ALLOW: async (request) => {
    const res = await helperRequest('/allow', { body: { repo: request.repo } });
    exactCache.clear();
    return res;
  },
  TEST_HELPER: async (request) => {
    const res = await helperRequest('/status', { settings: { enableHelper: true, helperUrl: request.url, helperToken: request.token }, timeout: 2500 });
    return { success: Boolean(res && res.ok), state: res && res.state, details: res };
  }
};

// What the page gets when a handler fails, so it never waits forever.
const MESSAGE_FALLBACKS = { LOOKUP_TOKEN: { success: false, data: null }, PROJECT_DECLARATIONS: { declarations: [] } };

chrome.runtime.onMessage.addListener((request, sender, sendResponse) => {
  const handler = request && Object.prototype.hasOwnProperty.call(MESSAGE_HANDLERS, request.action) && MESSAGE_HANDLERS[request.action];
  if (!handler) return false;
  Promise.resolve()
    .then(() => handler(request)) // also catches errors thrown synchronously
    .then(sendResponse, (err) => {
      console.warn('[Lean Lens] message handler failed:', request.action, err);
      sendResponse(Object.prototype.hasOwnProperty.call(MESSAGE_FALLBACKS, request.action) ? MESSAGE_FALLBACKS[request.action] : null);
    });
  return true; // respond asynchronously
});
