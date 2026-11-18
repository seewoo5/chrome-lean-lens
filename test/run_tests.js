/**
 * Automated test suite for the Lean Lens Chrome extension.
 * Tests tokenizer, PR diff scanner, builtins database, and HTML rendering.
 */

const assert = require('assert');
const fs = require('fs');
const path = require('path');
const vm = require('vm');

console.log("=== Running Lean Lens Test Suite ===\n");

// Setup minimal DOM simulation in VM context
const context = {
  console: console,
  addEventListener: () => {},
  document: {},
  Node: { TEXT_NODE: 3, ELEMENT_NODE: 1 },
  setTimeout: setTimeout,
  clearTimeout: clearTimeout,
  Date: Date
};
context.window = context;
context.self = context; // the service worker reaches shared scripts through `self`

function loadScript(relPath) {
  const fullPath = path.join(__dirname, '..', relPath);
  const code = fs.readFileSync(fullPath, 'utf8');
  vm.runInNewContext(code, context);
}

// 1. Test Builtins Database
console.log("1. Testing Builtins Database...");
loadScript('content/builtins_db.js');
const builtins = context.VersoBuiltins;
assert(builtins, "VersoBuiltins should be defined");

// Test tactics
const simp = builtins.get("simp");
assert(simp && simp.kind === "tactic", "simp should be recognized as tactic");
assert(simp.docstring.includes("simplifier"), "simp docstring should be detailed");

const rw = builtins.get("rw");
assert(rw && rw.kind === "tactic", "rw should be recognized as tactic");

const omega = builtins.get("omega");
assert(omega && omega.kind === "tactic", "omega should be recognized as tactic");

// Test types
const nat = builtins.get("Nat");
assert(nat && nat.kind === "inductive", "Nat should be recognized as inductive type");

const finsetSum = builtins.get("Finset.sum");
assert(finsetSum && finsetSum.name === "Finset.sum", "Finset.sum should be found");

// Builtins should NOT contain arbitrary Mathlib domain definitions (they should be resolved dynamically)
assert(!builtins.get("ZeroAtFilter"), "ZeroAtFilter should NOT be hardcoded into builtins");
assert(!builtins.get("BoundedAtFilter"), "BoundedAtFilter should NOT be hardcoded into builtins");

console.log("   ✓ Builtins DB verified: contains only core tactics and prelude primitives.\n");

// 2. Test Tokenizer Logic
console.log("2. Testing Lean Tokenizer...");
loadScript('content/lean_tokenizer.js');
const tokenizer = context.LeanTokenizer;
assert(tokenizer, "LeanTokenizer should be defined");

function mockTextNode(text) {
  return {
    nodeType: 3,
    nodeValue: text
  };
}

// Extract simple token
const res1 = tokenizer.extractTokenAt(mockTextNode("lemma continuous_extend_dense (hd : Dense s)"), 8);
assert(res1 && res1.token === "continuous_extend_dense", `Expected continuous_extend_dense, got ${res1?.token}`);

// Extract dotted token
const res2 = tokenizer.extractTokenAt(mockTextNode("  Finset.sum s (fun i => f i)"), 4);
assert(res2 && res2.token === "Finset", `Expected Finset, got ${res2?.token}`);
assert(res2.subToken === "Finset", `Expected subToken Finset, got ${res2.subToken}`);

const res3 = tokenizer.extractTokenAt(mockTextNode("  Finset.sum s (fun i => f i)"), 11);
assert(res3 && res3.token === "Finset.sum", `Expected Finset.sum, got ${res3?.token}`);
assert(res3.subToken === "sum", `Expected subToken sum, got ${res3.subToken}`);

// Reject pure number
const resNum = tokenizer.extractTokenAt(mockTextNode("  have h : 12345 = 12345 := rfl"), 13);
assert(resNum === null, "Pure numbers should return null");

// Token with prime
const resPrime = tokenizer.extractTokenAt(mockTextNode("  have h' : x' = y' := rfl"), 9);
assert(resPrime && resPrime.token === "h'", `Expected h', got ${resPrime?.token}`);

// Extract token from full line across dots
const lineSnippet = "  lemma foo (h : FunctionsBoundedAtImInfty.easy_lemma f)";
// Index 25 is on "FunctionsBoundedAtImInfty"
const tokenNamespace = tokenizer.extractTokenFromLine(lineSnippet, 25);
assert(tokenNamespace && tokenNamespace.token === "FunctionsBoundedAtImInfty",
  `Expected FunctionsBoundedAtImInfty, got ${tokenNamespace?.token}`);

// Index 45 is on "easy_lemma"
const tokenLemma = tokenizer.extractTokenFromLine(lineSnippet, 45);
assert(tokenLemma && tokenLemma.token === "FunctionsBoundedAtImInfty.easy_lemma",
  `Expected FunctionsBoundedAtImInfty.easy_lemma, got ${tokenLemma?.token}`);

// Test fine-grained token extraction on dot chains (ZeroAtFilter.neg)
const dotLine = "  exact ZeroAtFilter.neg h";
// Hovering over "ZeroAtFilter" (index 12)
const hoverBase = tokenizer.extractTokenFromLine(dotLine, 12);
assert(hoverBase && hoverBase.token === "ZeroAtFilter", `Expected ZeroAtFilter, got ${hoverBase?.token}`);
assert(hoverBase.subToken === "ZeroAtFilter", `Expected subToken ZeroAtFilter, got ${hoverBase?.subToken}`);

// Hovering over "neg" (index 22)
const hoverLemma = tokenizer.extractTokenFromLine(dotLine, 22);
assert(hoverLemma && hoverLemma.token === "ZeroAtFilter.neg", `Expected ZeroAtFilter.neg, got ${hoverLemma?.token}`);
assert(hoverLemma.subToken === "neg", `Expected subToken neg, got ${hoverLemma?.subToken}`);

console.log("   ✓ Tokenizer verified: extracts simple, dotted, and fine-grained chain tokens.\n");

// 3. Test PR Scanner Logic
console.log("3. Testing PR Scanner Regex & Declaration Parser...");
loadScript('content/pr_scanner.js');
const prScanner = context.LeanPRScanner;
assert(prScanner, "LeanPRScanner should be defined");

// Mock container with rows
const mockRows = [
  { textContent: "+/-- Extension lemma for continuous maps on dense subspaces. -/", classList: { contains: () => false }, getAttribute: () => null },
  { textContent: "+lemma continuous_extend_dense (hd : Dense s) (hf : Continuous f) : Continuous (Dense.extend hd f) := by", classList: { contains: () => false }, getAttribute: () => "123" },
  { textContent: "+  intro x", classList: { contains: () => false }, getAttribute: () => "124" },
  { textContent: "+/-- Lift a dense subspace homomorphism. -/", classList: { contains: () => false }, getAttribute: () => null },
  { textContent: "+def DenseSubspace.lift (s : Finset Nat) : Real :=", classList: { contains: () => false }, getAttribute: () => "46" }
];

const mockContainer = {
  querySelectorAll: (selector) => mockRows
};

prScanner.scanDiffLines(mockContainer, "Mathlib/Topology/Maps.lean");

const foundLemma = prScanner.find("continuous_extend_dense");
assert(foundLemma, "PR scanner should find continuous_extend_dense");
assert(foundLemma.kind === "lemma", `Expected kind lemma, got ${foundLemma.kind}`);
assert(foundLemma.docstring.includes("Extension lemma"), `Docstring mismatch: ${foundLemma.docstring}`);
assert(foundLemma.lineNumber === 123, `Line number mismatch: ${foundLemma.lineNumber}`);

const foundDef = prScanner.find("DenseSubspace.lift");
assert(foundDef, "PR scanner should find DenseSubspace.lift");
assert(foundDef.kind === "def", `Expected kind def, got ${foundDef.kind}`);
assert(foundDef.docstring.includes("Lift a dense subspace"), `Docstring mismatch: ${foundDef.docstring}`);

console.log("   ✓ PR Scanner verified: successfully parses PR declarations, kinds, and docstrings.\n");

// 4. Test Lean Syntax Highlighter
console.log("4. Testing Lean Syntax Highlighter (highlightLean)...");
// Create mock DOM elements for tooltip_view
context.document.getElementById = () => null;
context.document.createElement = () => ({
  addEventListener: () => {},
  querySelector: () => ({ addEventListener: () => {} }),
  querySelectorAll: () => []
});
context.document.body = { appendChild: () => {} };

loadScript('content/goal_diff.js');
loadScript('content/tooltip_view.js');
const tooltipView = context.VersoTooltipView;
assert(tooltipView, "VersoTooltipView should be defined");

// Test the exact snippet from user's report
const testSig = "def Continuous [TopologicalSpace α] [TopologicalSpace β] (f : α → β) : Prop";
const highlighted = tooltipView.highlightLean(testSig);

console.log("   Highlighted output:", highlighted);
assert(!highlighted.startsWith('="v-kw">'), `Bug detected! Starts with plain text ="v-kw">: ${highlighted}`);
assert(!highlighted.includes('<span class<span'), `Bug detected! Nested broken span tags found: ${highlighted}`);
assert(highlighted.includes('<span class="v-kw">def</span>'), "def should be wrapped in valid v-kw span");
assert(highlighted.includes('<span class="v-inst">[TopologicalSpace α]</span>'), "Instance argument should be wrapped in v-inst span");
assert(highlighted.includes('<span class="v-sym">:</span>'), "Colon should be wrapped in v-sym span");
assert(highlighted.includes('<span class="v-sym">→</span>'), "Arrow should be wrapped in v-sym span");

// An attribute is not an instance argument.
const attributed = tooltipView.highlightLean('@[expose] public section\n@[simp] theorem t [Group G] : True');
assert(attributed.includes('<span class="v-attr">@[expose]</span>') && attributed.includes('<span class="v-attr">@[simp]</span>'), attributed);
assert(attributed.includes('<span class="v-inst">[Group G]</span>'), attributed);

console.log("   ✓ Syntax Highlighter verified: perfectly renders Lean keywords, binders, and symbols.\n");

// 5. Test Loogle Dynamic Hit Selection
console.log("5. Testing Dynamic Loogle Hit Resolution...");
const mockLoogleHits = [
  { name: "Filter.ZeroAtFilter.neg", type: "lemma ...", module: "Mathlib.Order.Filter.ZeroAndBoundedAtFilter" },
  { name: "Filter.ZeroAtFilter", type: "def Filter.ZeroAtFilter ...", module: "Mathlib.Order.Filter.ZeroAndBoundedAtFilter" },
  { name: "Filter.ZeroAtFilter.add", type: "lemma ...", module: "Mathlib.Order.Filter.ZeroAndBoundedAtFilter" },
  { name: "Filter.BoundedAtFilter", type: "def Filter.BoundedAtFilter ...", module: "Mathlib.Order.Filter.ZeroAndBoundedAtFilter" }
];

// Load the real selection logic from the service worker (stubbing the chrome API).
// A working in-memory chrome.storage and a captured message listener (exercised in section 17).
const fakeStorage = {};
const workerListeners = [];
context.chrome = {
  runtime: { onMessage: { addListener: (fn) => workerListeners.push(fn) } },
  storage: { local: {
    get: (keys, cb) => {
      const out = {};
      const wanted = keys === null ? Object.keys(fakeStorage) : [].concat(keys);
      wanted.forEach(k => { if (k in fakeStorage) out[k] = fakeStorage[k]; });
      if (cb) cb(out);
    },
    set: (obj, cb) => { Object.assign(fakeStorage, obj); if (cb) cb(); },
    remove: (keys, cb) => { [].concat(keys).forEach(k => delete fakeStorage[k]); if (cb) cb(); },
    clear: (cb) => { Object.keys(fakeStorage).forEach(k => delete fakeStorage[k]); if (cb) cb(); }
  } }
};
loadScript('background/service_worker.js');
const selectLoogleHit = context.selectLoogleHit;
assert(typeof selectLoogleHit === "function", "selectLoogleHit should be defined by service_worker.js");

const resolvedZero = selectLoogleHit(mockLoogleHits, "ZeroAtFilter", "ZeroAtFilter").hit;
assert(resolvedZero.name === "Filter.ZeroAtFilter", `Expected Filter.ZeroAtFilter, got ${resolvedZero?.name}`);

const resolvedNeg = selectLoogleHit(mockLoogleHits, "ZeroAtFilter.neg", "neg").hit;
assert(resolvedNeg.name === "Filter.ZeroAtFilter.neg", `Expected Filter.ZeroAtFilter.neg, got ${resolvedNeg?.name}`);

const resolvedBounded = selectLoogleHit(mockLoogleHits, "BoundedAtFilter", "BoundedAtFilter").hit;
assert(resolvedBounded.name === "Filter.BoundedAtFilter", `Expected Filter.BoundedAtFilter, got ${resolvedBounded?.name}`);

// Regression: mathlib4#45928, `hl.sortedLE.pairwise` must not resolve to List.Perm.pairwise.
const pairwiseHits = [
  { name: "List.Pairwise" },
  { name: "List.Perm.pairwise" },
  { name: "Array.Perm.pairwise" },
  { name: "List.IsChain.pairwise" },
  { name: "List.SortedLE.pairwise" },
  { name: "List.SortedGE.pairwise" }
];
const sortedLE = selectLoogleHit(pairwiseHits, "sortedLE.pairwise", "pairwise");
assert(sortedLE && sortedLE.hit && sortedLE.hit.name === "List.SortedLE.pairwise",
  `Expected List.SortedLE.pairwise, got ${JSON.stringify(sortedLE)}`);

// If the qualifier matches nothing in the hit list, never pick an arbitrary `.pairwise`.
const noQualifier = selectLoogleHit(pairwiseHits.filter(h => h.name !== "List.SortedLE.pairwise"), "sortedLE.pairwise", "pairwise");
assert(noQualifier && !noQualifier.hit && noQualifier.candidates.length === 4,
  `Expected 4 ambiguous candidates, got ${JSON.stringify(noQualifier)}`);

// Bare token with several suffix matches is ambiguous, not a guess.
const barePairwise = selectLoogleHit(pairwiseHits, "pairwise", "pairwise");
assert(barePairwise && !barePairwise.hit && barePairwise.candidates.length === 5,
  `Expected bare pairwise to be ambiguous, got ${JSON.stringify(barePairwise)}`);

// Case matters for the last segment: `Pairwise` is not `pairwise`.
const pascal = selectLoogleHit(pairwiseHits, "Pairwise", "Pairwise");
assert(pascal && pascal.hit && pascal.hit.name === "List.Pairwise", `Expected List.Pairwise, got ${JSON.stringify(pascal)}`);

// No relevant hit at all → null (previously fell back to hits[0]).
assert(selectLoogleHit(mockLoogleHits, "Continuous", "Continuous") === null, "Unrelated hits should give null");

const amb = context.buildAmbiguousResult("sortedLE.pairwise", noQualifier.candidates);
assert(amb.ambiguous && amb.name === "pairwise" && amb.docstring.includes("List.Perm.pairwise"), "Ambiguous result should list candidates");

console.log("   ✓ Dynamic Resolution verified: accurately resolves unqualified and dot-notation tokens to base Mathlib definitions.\n");

// 6. Receiver type inference for dot notation
console.log("6. Testing receiver type inference (binder_context)...");
loadScript('content/lean_terms.js');
loadScript('content/binder_context.js');
loadScript('content/term_hover.js');
const bc = context.VersoBinderContext;
assert(bc, "VersoBinderContext should be defined");

const prLines = [
  "theorem _root_.List.toFinset_sort [DecidableEq α] {l : List α} (hl : l.Nodup) :",
  "  rw [← h]",
  "  exact pairwise_sort _ r",
  "",
  "theorem _root_.List.SortedLT.sort_toFinset [LinearOrder α] {l : List α} (hl : l.SortedLT) :",
  "    l.toFinset.sort (· ≤ ·) = l :=",
  "  (List.toFinset_sort _ hl.nodup).2 hl.sortedLE.pairwise"
];
const prCtx = bc.declarationContext(prLines, prLines.length - 1);
assert(!prCtx.includes("l.Nodup"), "Context must stop at the enclosing declaration");
assert.strictEqual(bc.findBinderType("hl", prCtx), "l.SortedLT");
assert.strictEqual(bc.findBinderType("l", prCtx), "List α");
assert.strictEqual(bc.inferReceiverNamespace("hl", prCtx), "List.SortedLT", "hl.nodup → List.SortedLT.nodup");
assert.strictEqual(bc.inferReceiverNamespace("l", prCtx), "List", "l.toFinset → List.toFinset");

const cases = [
  ["theorem foo (hab : a ≤ b) : a < c :=", "hab", "LE.le"],
  ["theorem foo {s : Set α} (hs : s.Nonempty) :", "hs", "Set.Nonempty"],
  ["theorem foo (hf : Continuous f) (hg : Differentiable ℝ g) :", "hg", "Differentiable"],
  ["theorem foo (h₁ h₂ : Nat.Prime p) :", "h₂", "Nat.Prime"],
  ["theorem foo (h : ∀ x, p x) :", "h", null],
  ["theorem foo (h : P ∧ Q) :", "h", "And"],
  ["theorem foo (n : ℕ) :", "n", "Nat"],
  ["example : True := by\n  have hx : x ∈ s := by simp\n  exact hx.out", "hx", "Membership.mem"],
  ["theorem foo (h : a = b) : True := by\n  have h : Continuous f := sorry\n  exact h.comp", "h", "Continuous"],
  ["theorem foo (x : α) :", "y", null],
  // Bundled-map notations (mathlib4#45917: `g.compLinearMap`)
  ["def compLinearMap (g : (Π i, M₂ i) →ₘₛₗ[σ₂₃] N₃) (f : Π i, M₁ i →ₛₗ[σ₁₂] M₂ i) :", "g", "MultilinearMap"],
  ["def compLinearMap (g : (Π i, M₂ i) →ₘₛₗ[σ₂₃] N₃) (f : Π i, M₁ i →ₛₗ[σ₁₂] M₂ i) :", "f", null],
  ["theorem foo (m : Π i, M₁ i) :", "m", null],
  ["theorem foo (f : M →ₗ[R] N) :", "f", "LinearMap"],
  ["theorem foo (e : M ≃ₗ[R] N) :", "e", "LinearEquiv"],
  ["theorem foo (f : R →+* S) :", "f", "RingHom"],
  ["theorem foo (f : G →* H) :", "f", "MonoidHom"],
  ["theorem foo (e : α ≃ β) :", "e", "Equiv"],
  ["theorem foo (f : α ↪o β) :", "f", "OrderEmbedding"],
  ["theorem foo (f : E →L[𝕜] F) :", "f", "ContinuousLinearMap"],
  ["theorem foo (f : L →ₗ⁅R⁆ L') :", "f", "LieHom"],
  ["theorem foo (f : C(X, Y)) :", "f", "ContinuousMap"],
  ["theorem foo (f : α → β) :", "f", null],
  ["theorem foo (f : M →ₗ[R] N → P) :", "f", "LinearMap"],
  ["theorem foo (f : M →ₓ[R] N) :", "f", null],
  ["theorem foo (h : a ↔ b) :", "h", "Iff"],
  ["theorem compLinearMap_injective (f : Π i, M₁ i →ₛₗ[σ₁₂] M₂ i) (hf : ∀ i, Surjective (f i)) :\n    Injective fun g : (Π i, M₂ i) →ₘₛₗ[σ₂₃] N₃ => g.compLinearMap f", "g", "MultilinearMap"],
  ["theorem foo : ∀ x y : ℕ, x.succ = y", "y", "Nat"],
  ["theorem foo (x : ℤ) : ∃ x : ℕ, x.succ = 0", "x", "Nat"]
];
for (const [text, name, expected] of cases) {
  const got = bc.inferReceiverNamespace(name, text);
  assert.strictEqual(got, expected, `${name} in ${JSON.stringify(text)}: expected ${expected}, got ${got}`);
}

// A partial namespace matching several declarations is ambiguous, not a guess.
const monoHits = [{ name: "Set.Nonempty.mono" }, { name: "Finset.Nonempty.mono" }];
const mono = selectLoogleHit(monoHits, "Nonempty.mono", "mono");
assert(mono && !mono.hit && mono.candidates.length === 2, `Expected ambiguous Nonempty.mono, got ${JSON.stringify(mono)}`);
assert.strictEqual(selectLoogleHit(monoHits, "Set.Nonempty.mono", "mono").hit.name, "Set.Nonempty.mono");

// The service-worker selector resolves the typed token exactly.
const nodupHits = [{ name: "List.Sublist.nodup" }, { name: "List.Perm.nodup" }, { name: "List.SortedLT.nodup" }];
assert.strictEqual(selectLoogleHit(nodupHits, "List.SortedLT.nodup", "nodup").hit.name, "List.SortedLT.nodup");

console.log("   ✓ Receiver inference verified: hl.nodup with (hl : l.SortedLT) resolves in List.SortedLT.\n");

// 7. File scope (namespace / section / open) for bare identifiers
console.log("7. Testing file-scope resolution (scopeAt)...");
const scopeAt = context.scopeAt;
assert(typeof scopeAt === "function", "scopeAt should be defined by service_worker.js");
const leanFile = [
  "import Mathlib.Foo",                       // 1
  "/-! # Doc",                                // 2
  "open Nope -/",                             // 3  (inside block comment)
  "open Fin Function Finset Set",             // 4
  "section Meta",                             // 5
  "open Lean Meta",                           // 6
  "end Meta",                                 // 7
  "namespace MultilinearMap",                 // 8
  "-- open Commented",                        // 9
  "section",                                  // 10
  "open Finset (sum prod)",                   // 11
  "open scoped BigOperators",                 // 12
  "theorem cons_add (m : ∀ i : Fin n, M i.succ) :", // 13
  "    f (cons (x + y) m) = 0 := by",         // 14
  "end",                                      // 15
  "open Real in",                             // 16
  "theorem _root_.List.foo_bar : True := by", // 17
  "  exact trivial",                          // 18
  "theorem Nested.baz : True := trivial",     // 19
  "end MultilinearMap",                       // 20
  "theorem top : True := trivial"             // 21
].join("\n");
const ns = (line) => JSON.parse(JSON.stringify(scopeAt(leanFile, line).map(o => o.only ? `${o.ns}(${o.only.join(" ")})` : o.ns)));
assert.deepStrictEqual(ns(14), ["MultilinearMap", "Finset(sum prod)", "Fin", "Function", "Finset", "Set"]);
assert.deepStrictEqual(ns(18), ["List", "MultilinearMap", "Real", "Fin", "Function", "Finset", "Set"]);
assert.deepStrictEqual(ns(19), ["MultilinearMap.Nested", "MultilinearMap", "Fin", "Function", "Finset", "Set"]);
assert.deepStrictEqual(ns(21), ["Fin", "Function", "Finset", "Set"]);
assert(!ns(14).includes("Nope") && !ns(14).includes("Commented") && !ns(14).includes("Lean") && !ns(14).includes("BigOperators"),
  "Comments, closed sections and `open scoped` must not contribute names");
console.log("   ✓ File scope verified: namespaces, sections, opens, `open … in`, and declaration namespaces.\n");

// 8. Local variable tooltips and `variable` declarations (mathlib4#45909)
console.log("8. Testing local variables and PR scanning in the newer diff view...");
const declText = [
  "private theorem le_mul_exp_of_forall_abs_lt {b c e C : ℝ} (hb : 0 < b)",
  "    (h : ∀ s : ℝ, |s| < b → C ≤ c * Real.exp (e * s)) : C ≤ c * Real.exp (e * b) := by",
  "  have htend : Filter.Tendsto (fun s : ℝ => c * Real.exp (e * s))",
  "      (nhdsWithin b (Set.Iio b)) (nhds (c * Real.exp (e * b))) :=",
  "    (ContinuousAt.tendsto (h := by fun_prop)).mono_left nhdsWithin_le_nhds",
  "  filter_upwards [self_mem_nhdsWithin] with s hs1 hs2",
  "  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ, ∀ z : ℂ, H z = 0 := sorry",
  "  rcases le_total (0 : ℝ) s with h' | h'",
  "  set y := b + 1 with hy",
  "  intro z hz"
].join("\n");
const lv = (n) => { const r = bc.localVariableInfo(n, declText); return r && r.typeSignature; };
assert.strictEqual(lv("hb"), "hb : 0 < b");
assert.strictEqual(lv("C"), "C : ℝ");
assert.strictEqual(lv("h"), "h : ∀ s : ℝ, |s| < b → C ≤ c * Real.exp (e * s)");
assert.strictEqual(lv("htend"), "htend : Filter.Tendsto (fun s : ℝ => c * Real.exp (e * s)) (nhdsWithin b (Set.Iio b)) (nhds (c * Real.exp (e * b)))");
assert.strictEqual(lv("hs2"), "hs2 : _");
assert.strictEqual(lv("H"), "H : ℂ → ℂ");
assert.strictEqual(lv("hH"), "hH : _");
assert.strictEqual(lv("h'"), "h' : _");
assert.strictEqual(lv("y"), "y := b + 1");
assert.strictEqual(lv("hz"), "hz : _");
assert.strictEqual(lv("Real"), null, "constants are not locals");
assert.strictEqual(lv("Filter.Tendsto"), null, "dotted names are not locals");

const varFile = [
  "open Complex Real",
  "variable {T : ℝ} [hT : Fact (0 < T)]",
  "public section",
  "variable {f : AddCircle T → ℂ}",
  "  (g : ℂ → ℂ)",
  "theorem foo : True := trivial",
  "end",
  "theorem bar : True := trivial"
].join("\n");
const vars = (line) => JSON.parse(JSON.stringify(context.variablesAt(varFile, line).map(v => v.line)));
assert.deepStrictEqual(vars(6), [2, 4], "both variable commands in scope inside the section");
assert.deepStrictEqual(vars(8), [2], "`end` closes `public section`'s variables");
assert.strictEqual(bc.findBinderType("g", context.variablesAt(varFile, 6)[1].text), "ℂ → ℂ", "indented continuation lines belong to `variable`");

// PR scanner: newer view, cells only, deleted lines skipped, multi-line signatures.
const cell = (text, opts = {}) => ({
  textContent: text,
  classList: { contains: () => false },
  getAttribute: (a) => (a === 'data-code-marker' ? (opts.deleted ? '-' : null) : null),
  closest: (sel) => (sel === '[data-line-number]' && opts.line ? { getAttribute: () => String(opts.line) } : null)
});
const reactRows = [
  cell("/-- A value dominated by `c * exp (e * s)` ... -/", { line: 60 }),
  cell("private theorem le_mul_exp_of_forall_abs_lt {b c e C : ℝ} (hb : 0 < b)", { line: 62 }),
  cell("    (h : ∀ s : ℝ, |s| < b → C ≤ c * Real.exp (e * s)) : C ≤ c * Real.exp (e * b) := by", { line: 63 }),
  cell("theorem old_name_deleted : True := trivial", { deleted: true }),
  cell("theorem norm_fourierCoeff_le_of_shift {f : AddCircle T → ℂ} {g : ℂ → ℂ} {M a : ℝ}", { line: 136 }),
  cell("    (hg : True) :", { line: 137 }),
  cell("    ‖fourierCoeff f k‖ ≤ M := by", { line: 138 })
];
prScanner.reset();
prScanner.scanDiffLines({ querySelectorAll: (sel) => (sel === '.diff-text-inner' ? reactRows : []) }, "Mathlib/Analysis/Fourier/StripDecay.lean");
const lm = prScanner.find("le_mul_exp_of_forall_abs_lt");
assert(lm && lm.lineNumber === 62, `le_mul_exp_of_forall_abs_lt should be indexed at line 62, got ${lm && lm.lineNumber}`);
assert(lm.typeSignature.includes("C ≤ c * Real.exp (e * b)"), `Signature should span lines: ${lm.typeSignature}`);
const nf = prScanner.find("norm_fourierCoeff_le_of_shift");
assert(nf && nf.typeSignature.endsWith("‖fourierCoeff f k‖ ≤ M"), `Multi-line signature: ${nf && nf.typeSignature}`);
assert(!prScanner.find("old_name_deleted"), "Deleted lines must not be indexed");

console.log("   ✓ Local variables, `variable` scope, and newer-view PR scanning verified.\n");

// 9. Tactic docs and tactic position
console.log("9. Testing tactic docs parsing and tactic position...");
const sampleTactics =
  '<div id="Mathlib.Meta.FunProp.funPropTacStx"><div id="userName-fun_prop"><h2>fun_prop</h2>' +
  '<p><p><code>fun_prop</code> solves a goal of the form <code>P f</code> &amp; more.</p>' +
  '<ul><li><code>fun_prop (disch := tac)</code> uses <code>tac</code>.</li></ul>' +
  '<pre><code class="language-lean">example : <a href="x">Continuous</a> (fun x : ℝ ↦ x) := by fun_prop\n</code></pre></p>' +
  '<dl><dt>Tags:</dt><dd></dd><dt>Defined in module:</dt><dd><a href="./M.html">Mathlib.Tactic.FunProp.Elab</a></dd></dl></div></div>' +
  '<div id="Other.fun_prop2"><div id="userName-fun_prop"><h2>fun_prop</h2><p>duplicate</p><dl></dl></div></div>' +
  '<div id="convSeq"><div id="userName-conv => _"><h2>conv =&gt; _</h2><p>not an identifier</p><dl></dl></div></div>';
const tdocs = context.parseTacticDocs(sampleTactics);
assert.deepStrictEqual(JSON.parse(JSON.stringify(Object.keys(tdocs))), ["fun_prop"], "one entry per identifier-like tactic name");
assert.strictEqual(tdocs.fun_prop.module, "Mathlib.Tactic.FunProp.Elab");
assert(tdocs.fun_prop.doc.startsWith("`fun_prop` solves a goal of the form `P f` & more."), tdocs.fun_prop.doc);
assert(tdocs.fun_prop.doc.includes("- `fun_prop (disch := tac)` uses `tac`."), "list items become Markdown bullets");
assert(tdocs.fun_prop.doc.includes("```lean\nexample : Continuous (fun x : ℝ ↦ x) := by fun_prop\n```"), "code blocks keep text, drop links");

const tp = (prefix) => tokenizer.isTacticPosition(prefix);
assert(tp("    "), "start of an indented line");
assert(tp("+    "), "start of an added diff line");
assert(tp("  have h := by "), "after `by`");
assert(tp("  · "), "after a focusing dot");
assert(tp("  constructor <;> "), "after `<;>`");
assert(tp("  try ("), "inside a combinator");
assert(tp("  (ContinuousAt.tendsto (h := by "), "nested `by`");
assert(!tp("  exact "), "argument position");
assert(!tp("  rw ["), "inside a rewrite list");
assert(!tp("  simpa using "), "after `using`");
assert(!tp("    have h2 : |"), "absolute-value bars are not tactic separators");
assert(tp("  first | "), "`first | tac`");
assert(tp("  first | simp | "), "later `first` alternatives");
console.log("   ✓ Tactic docs parsing and tactic-position detection verified.\n");

// 10. Receivers that are terms: `(f a).field`, `h.f₁.f₂.field`
console.log("10. Testing term receivers (conclusionOf / parenReceiver)...");
const concl = (t) => bc.conclusionOf(t);
assert.strictEqual(concl(" {X : Type u_1} [TopologicalSpace X] {f : X → Y} {x : X} (h : ContinuousAt f x) : Filter.Tendsto f (nhds x) (nhds (f x))"),
  "Filter.Tendsto f (nhds x) (nhds (f x))");
assert.strictEqual(concl("∀ s : ℝ, |s| < b → C ≤ c * Real.exp (e * s)"), "C ≤ c * Real.exp (e * s)");
assert.strictEqual(concl(" {l : List α} (h : l.SortedLT) : l.SortedLE"), "l.SortedLE");
assert.strictEqual(concl("(f : M →ₗ[R] N) : M →ₗ[R] N"), "M →ₗ[R] N", "bundled arrows are not premises");
assert.strictEqual(bc.typeHead(concl(" {l : List α} (h : l.SortedLT) : l.SortedLE"),
  (v) => bc.typeHead(bc.findBinderType(v, " {l : List α} (h : l.SortedLT) : l.SortedLE"), null)), "List.SortedLE");

assert.strictEqual(bc.parenReceiver("    (ContinuousAt.tendsto (h := by fun_prop))."), "ContinuousAt.tendsto (h := by fun_prop)");
assert.strictEqual(bc.parenReceiver("  exact (foo\n    (bar x))."), "foo\n    (bar x)", "receivers may span lines");
assert.strictEqual(bc.parenReceiver("  exact foo."), null);
assert.strictEqual(bc.applicationHead("ContinuousAt.tendsto (h := by fun_prop)"), "ContinuousAt.tendsto");
assert.strictEqual(bc.applicationHead("@hf.comp _ hg"), "hf.comp");
assert.strictEqual(bc.typeHead(bc.conclusionOf(bc.findBinderType("h", declText)), null), "LE.le", "(h s hs).le uses h's conclusion");
console.log("   ✓ Term receivers verified.\n");

// 11. Anonymous projections `h.1`, `h.2`
console.log("11. Testing anonymous projections...");
const proj = (t, n) => { const r = bc.projectionType(t, n); return r && r.type; };
assert.strictEqual(proj("0 ≤ y ∧ y ≤ s", 1), "0 ≤ y");
assert.strictEqual(proj("A ∧ B ∧ C", 2), "B ∧ C", "∧ is right-associative");
assert.strictEqual(proj("a ≤ b ↔ c ≤ d", 2), "c ≤ d → a ≤ b");
assert.strictEqual(proj("∃ H : ℂ → ℂ, ∀ z, H z = 0", 1), "ℂ → ℂ");
assert.strictEqual(proj("∃ H : ℂ → ℂ, ∀ z, H z = 0", 2), "∀ z, H z = 0");
assert.strictEqual(proj("α × (β × γ)", 2), "β × γ");
assert.strictEqual(proj("{x : ℝ // 0 < x}", 2), "0 < x");
assert.strictEqual(proj("y ∈ Set.uIcc (0 : ℝ) s", 1), "(0 : ℝ) ⊓ s ≤ y");
assert.strictEqual(proj("x ∈ Icc a b", 2), "x ≤ b");
assert.strictEqual(proj("x ∈ s ∩ t", 2), "x ∈ t");
assert.strictEqual(proj("Continuous f", 1), null, "unknown shapes defer to the structure lookup");

const uIccDecl = [
  "private theorem abs_le_abs_of_mem_uIcc' {s y : ℝ} (hy : y ∈ Set.uIcc (0 : ℝ) s) :",
  "    |y| ≤ |s| := by",
  "  rcases le_total (0 : ℝ) s with h | h",
  "  · rw [Set.uIcc_of_le h] at hy",
  "    rw [abs_of_nonneg h]",
  "    exact (abs_le).mpr ⟨by linarith [hy.1], hy.2⟩"
].join("\n");
// `hy` is rewritten before use: the projection is resolved by replaying the rewrite (section 14).
const p1 = bc.projectionInfo("hy.1", uIccDecl);
assert.strictEqual(p1.typeSignature, "hy.1 : _", "provisional until the rewrite is replayed");
assert(p1.replay && p1.docstring.includes("rw [Set.uIcc_of_le h] at hy"), "names the rewrite it applies");
assert(bc.localVariableInfo("hy", uIccDecl).replay, "hovering hy itself also replays the rewrite");
assert.strictEqual(bc.projectionInfo("hz.1", uIccDecl), null, "unknown bases are not projections");
assert.strictEqual(bc.projectionInfo("hy.le", uIccDecl), null, "named fields are not anonymous projections");
const needs = bc.projectionInfo("e.1", "theorem foo (e : α ≃ β) : True := by\n  exact e.1");
assert(needs.structureNeeded && needs.structureNeeded.index === 1, "structures ask the worker for `mk` fields");
assert.deepStrictEqual(JSON.parse(JSON.stringify(bc.laterChanges("h", "(h : P)\n  simp at h ⊢\n  norm_num at *\n  exact h", 0))),
  ["simp at h ⊢", "norm_num at *"]);
console.log("   ✓ Anonymous projections verified.\n");

// 12. Regressions from sweeping real PRs (hover every identifier)
console.log("12. Testing regressions found by sweeping real PRs...");
const tok = (line, word, nth = 0) => {
  let at = -1;
  for (let k = 0; k <= nth; k++) at = line.indexOf(word, at + 1);
  return tokenizer.extractTokenFromLine(line, at);
};
assert.strictEqual(tok("  · rw [Set.uIcc_of_le h] at hy", "uIcc_of_le").token, "Set.uIcc_of_le", "short namespaces are not stripped");
assert.strictEqual(tok("  exact hl.nodup", "nodup").token, "nodup", "lowercase receivers are stripped");
assert.strictEqual(tok("theorem _root_.List.SortedLT.foo :", "SortedLT").chainUpToCursor, "List.SortedLT", "`_root_.` is dropped");
assert.strictEqual(tok("theorem _root_.List.SortedLT.foo :", "_root_"), null);
assert.strictEqual(tok("  simpa [hx] using hy.smul x⁻¹", "x⁻¹").token, "x", "superscripts are notation");
assert.strictEqual(tok("  refine foo ?_", "?_"), null, "holes are not names");
assert.strictEqual(tok("  := fast_instance% FunLike", "fast_instance"), null, "elaborators are not names");
const arrowTok = tok("def f : R →ₙ* R →o R where", "ₙ");
assert(arrowTok.arrowNotation && arrowTok.token === "→ₙ*", `arrow notation is read whole: ${arrowTok.token}`);
assert.strictEqual(tok("def f : R →ₚ[S] R where", "ₚ").token, "→ₚ[_]");
assert.strictEqual(bc.typeHead("A →ₙ* B", null), "MulHom");
assert.strictEqual(bc.typeHead("R →ₚ[S] R", null), "PositiveLinearMap");

// Binders
assert.strictEqual(bc.findBinderType("z", "(hg : DifferentiableOn ℂ g {z : ℂ | |z.im| < a})"), "ℂ", "set-builder binder type ends at ` | `");
assert.strictEqual(bc.localVariableInfo("v", "def map (f : X) : Y where\n  carrier := f '' { v | ∀ i, v i ∈ p i }").typeSignature, "v : _");
const ascr = "theorem map_nonempty (f : X) (p : Π i, Submodule R (M i)) :\n    (map f p : Set N).Nonempty := by\n  exact (p i).zero_mem";
assert.strictEqual(bc.findBinderType("p", ascr), "Π i, Submodule R (M i)", "type ascriptions in the statement are not binders");
assert.strictEqual(bc.localVariableInfo("h₁", "theorem coe_mk (f : X → N) (h₁ h₂) : True := by\n  exact h₁").typeSignature, "h₁ : _", "untyped header binders");
assert.strictEqual(bc.findBinderType("h", "def cantorRec (o : Ordinal) : C o :=\n  if h : o = 0 then h ▸ zero else foo"), "o = 0", "`if h : P then`");
assert.strictEqual(bc.findBinderType("ha", "  · intro a\n    by_cases ha : a ∈ f.support\n    exact ha"), "a ∈ f.support", "`by_cases h : P`");
assert.strictEqual(bc.findBinderType("IH'", "  have IH' (e') : f e' < b := by\n    exact IH'"), "∀ (e'), f e' < b", "`have h (x) : T`");
assert.strictEqual(bc.localVariableInfo("o", "theorem foo : True := by\n  ext o a\n  exact o").typeSignature, "o : _", "`ext` binders");
assert.strictEqual(bc.findBinderType("h₁", "structure M where\n  (h₁ : ∀ (m : Π i, M i) (i : ι),"), "∀ (m : Π i, M i) (i : ι),", "binders spanning lines");

// Types
assert.strictEqual(bc.typeHead("Injective fun g : (Π i, M₂ i) →ₘₛₗ[σ₂₃] N₃ => g.compLinearMap f", null), "Injective", "operators inside a lambda don't count");
assert.strictEqual(bc.typeHead("Differentiable 𝕜 fun x => Complex.exp (f x)", null), "Differentiable", "`=>` is not `>`");
assert.strictEqual(bc.typeHead("((cantorNF b o).map Prod.fst).SortedGT", null), "SortedGT", "`(term).Field` gives a partial namespace");
assert.strictEqual(bc.codomainOf("Rˣ →* R ≃o R"), "R ≃o R");
assert.strictEqual(bc.structureBeingBuilt("def map (f : X) (p : Y) : SubMulAction R M where\n  carrier := f '' s"), "SubMulAction");
assert.strictEqual(bc.namedArgFunction("  have hb := le_mul_exp_of_forall_abs_lt (b := a) (c := M) ("), "le_mul_exp_of_forall_abs_lt");
assert.strictEqual(bc.namedArgFunction("  have hb := norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := T)\n      ("), "norm_integral_le_of_norm_le_const");

// PR declarations: qualified suffixes never fall back to a sibling's short name.
prScanner.reset();
prScanner.scanDiffLines({ querySelectorAll: (sel) => (sel === '.diff-text-inner' ? [
  cell("theorem _root_.List.SortedLT.sort_toFinset [LinearOrder α] {l : List α} (hl : l.SortedLT) : True := by", { line: 99 }),
  cell("theorem _root_.List.SortedGT.sort_toFinset [LinearOrder α] {l : List α} (hl : l.SortedGT) : True := by", { line: 103 }),
  cell("alias CNF.eval := cantorEval", { line: 350 })
] : []) }, "Mathlib/Data/Finset/Sort.lean");
assert.strictEqual(prScanner.find("SortedGT.sort_toFinset").lineNumber, 103);
assert.strictEqual(prScanner.find("sortedGT.sort_toFinset").lineNumber, 103, "qualifiers compare case-insensitively");
assert.strictEqual(prScanner.find("SortedEQ.sort_toFinset"), null);
assert.strictEqual(prScanner.find("CNF.eval").kind, "alias", "`alias` declarations are indexed");

// Scope origins: the current namespace is marked so it can win over `open`ed ones.
const orig = JSON.parse(JSON.stringify(context.scopeAt("namespace Finset\nopen Multiset Nat\ntheorem _root_.List.foo : True := by\n  exact pairwise_sort _ r", 4)));
assert.deepStrictEqual(orig.map(o => `${o.ns}:${o.origin}`), ["List:namespace", "Finset:namespace", "Multiset:open", "Nat:open"]);
console.log("   ✓ Sweep regressions verified.\n");

// 13. Inferring types of locals without a written type
console.log("13. Testing local type inference...");
const lt = (name, text) => { const r = bc.localVariableInfo(name, text); return r && r.typeSignature; };
const hvert = [
  "theorem foo {s : ℝ} : True := by",
  "  have hvert : ∀ y ∈ Set.uIcc (0 : ℝ) s,",
  "      g ((T : ℂ) + (y : ℂ) * Complex.I) = g ((y : ℂ) * Complex.I) := by",
  "    intro y hy"
].join("\n");
assert.strictEqual(lt("y", hvert), "y : ℝ", "element type of an interval with a typed endpoint");
assert.strictEqual(lt("hy", hvert), "hy : y ∈ Set.uIcc (0 : ℝ) s");
const hsub = "theorem foo : True := by\n  have hsub : Set.uIcc (0 : ℝ) T ×ℂ Set.uIcc (0 : ℝ) s ⊆ {z : ℂ | |z.im| < a} := by\n    intro z hz";
assert.strictEqual(lt("z", hsub), "z : ℂ", "`⊆` goals: element type");
assert.strictEqual(lt("hz", hsub), "hz : z ∈ Set.uIcc (0 : ℝ) T ×ℂ Set.uIcc (0 : ℝ) s");
const hbound = "theorem foo : True := by\n  have hbound : ∀ s : ℝ, |s| < a → ‖c‖ ≤ M * Real.exp (e * s) := by\n    intro t hsb";
assert.strictEqual(lt("t", hbound), "t : ℝ");
assert.strictEqual(lt("hsb", hbound), "hsb : |t| < a", "renamed binders are substituted");
const stmt = "theorem bar (f : ℕ → ℕ) : ∀ n : ℕ, ∀ m, n ≤ m → f n ≤ f m := by\n  intro a\n  intro b hab";
assert.strictEqual(lt("a", stmt), "a : ℕ", "intro on the declaration statement");
assert.strictEqual(lt("hab", stmt), "hab : a ≤ b", "consecutive intro lines");
assert.strictEqual(lt("b", stmt), "b : _", "untyped ∀ binders stay unknown");
const termFun = "theorem baz : ∀ x : ℝ, 0 ≤ x → 0 ≤ x ^ 2 :=\n  fun x hx => by positivity";
assert.strictEqual(lt("hx", termFun), "hx : 0 ≤ x", "term-mode `fun`");
const notGoal = "theorem q : ¬ P := by\n  intro hp";
assert.strictEqual(lt("hp", notGoal), "hp : P");
const afterRw = "theorem r : ∀ x, P x := by\n  rw [foo]\n  intro x hx";
assert.strictEqual(lt("hx", afterRw), "hx : _", "goals changed by earlier tactics are not guessed");

// Destructuring local terms
const obt = [
  "theorem t (h : ∃ x : ℝ, 0 < x ∧ x < 1) (h' : A ↔ B) : True := by",
  "  obtain ⟨x, hx0, hx1⟩ := h",
  "  rcases h' with ⟨mp, mpr⟩",
  "  set y := x + 1 with hy"
].join("\n");
assert.strictEqual(lt("x", obt), "x : ℝ");
assert.strictEqual(lt("hx0", obt), "hx0 : 0 < x");
assert.strictEqual(lt("hx1", obt), "hx1 : x < 1");
assert.strictEqual(lt("mpr", obt), "mpr : B → A");
assert.strictEqual(lt("hy", obt), "hy : y = x + 1");
const alt = "theorem u (h : a < b ∨ b < a) : True := by\n  rcases h with h1 | h2\n  · exact h1\n  · exact h2";
assert.strictEqual(lt("h2", alt), "h2 : b < a");
const ev = "theorem v (hf : ∀ᶠ x in l, 0 < f x) : True := by\n  filter_upwards [hf] with y hy";
assert.strictEqual(lt("hy", ev), "hy : 0 < f y");
// Constant terms are deferred to the worker, with the bullet they're used in.
const cst = "theorem w {b : Ordinal} : True := by\n  obtain hb | hb := le_or_gt b 1\n  · simp\n  · have := hb";
const pend = bc.localVariableInfo("hb", cst).inferNeeded;
assert(pend && pend.term === "le_or_gt b 1" && pend.caseIdx === 2, JSON.stringify(pend));
// Receivers use inferred types.
assert.strictEqual(bc.inferReceiverNamespace("hx0", obt), "LT.lt");
console.log("   ✓ Local type inference verified.\n");

// 14. Replaying `rw … at h` (async: collected and awaited before the final verdict)
console.log("14. Testing rewrite replay...");
const asyncChecks = [];
const roundTrip = ["y ∈ Set.uIcc (0 : ℝ) s", "|x| < 1", "a * b * c = 1", "c * (a * b) = 1", "¬a = b", "∀ x ∈ s, f x = 0",
  "‖f x - g x‖ ≤ ε", "(f ∘ g) x = f (g x)", "x⁻¹ * x = 1", "↑n + 1 = ↑(n + 1)", "-(a - b) = b - a", "x ∈ {z : ℂ | |z.im| < a}",
  "‖fourierCoeff f k‖ ≤ M * Real.exp (-(2 * π * a / T) * |(k : ℝ)|)", "a ≤ b ∧ b ≤ c → a ≤ c"];
for (const t of roundTrip) assert.strictEqual(bc.showTerm(bc.parseTerm(t)), t, `parse/print round trip: ${t}`);
assert.strictEqual(bc.parseTerm("x +"), null, "malformed terms don't parse");

const SIGS = {
  "Set.uIcc_of_le": "{α : Type u_1} [Lattice α] {a b : α} (h : a ≤ b) : Set.uIcc a b = Set.Icc a b",
  "Set.uIcc_of_ge": "{α : Type u_1} [Lattice α] {a b : α} (h : b ≤ a) : Set.uIcc a b = Set.Icc b a",
  "mul_comm": "{G : Type u_1} [CommMagma G] (a b : G) : a * b = b * a",
  "sub_nonneg": "{α : Type u_1} [AddGroup α] [LE α] [AddRightMono α] {a b : α} : 0 ≤ a - b ↔ b ≤ a",
  "abs_of_nonneg": "{α : Type u_1} [Lattice α] [AddGroup α] {a : α} [AddLeftMono α] (h : 0 ≤ a) : |a| = a",
  "Nat.succ_eq_add_one": "(n : ℕ) : n.succ = n + 1",
  "add_zero": "{M : Type u} [AddZeroClass M] (a : M) : a + 0 = a",
  "add_comm": "{G : Type u_1} [AddCommMagma G] (a b : G) : a + b = b + a",
  "div_eq_iff": "{G₀ : Type u_3} [GroupWithZero G₀] {a b c : G₀} (hb : b ≠ 0) : a / b = c ↔ a = c * b"
};
const sigOf = async (n) => SIGS[n] || null;
const replayed = (text, name) => {
  const info = name.includes(".") ? bc.projectionInfo(name, text) : bc.localVariableInfo(name, text);
  if (!info.replay) return Promise.resolve(info.typeSignature);
  return bc.replayChanges(info.replay.baseType, info.replay.changes, text, sigOf).then(r => bc.describeReplay(info, r).typeSignature);
};
const expectReplay = (text, name, want, why) =>
  asyncChecks.push(replayed(text, name).then(got => assert.strictEqual(got, want, why)));

const uIccFull = uIccDecl + "\n  · rw [Set.uIcc_of_ge h] at hy\n    rw [abs_of_nonpos h]\n    exact (abs_le).mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩";
expectReplay(uIccDecl, "hy", "hy : y ∈ Set.Icc (0 : ℝ) s", "rw with a lemma (Lean: hy : y ∈ Set.Icc 0 s)");
expectReplay(uIccDecl, "hy.1", "hy.1 : (0 : ℝ) ≤ y", "projection after the rewrite");
expectReplay(uIccFull, "hy", "hy : y ∈ Set.Icc s (0 : ℝ)", "only the rewrite in the current `·` case applies");
expectReplay("example (a b c : ℕ) (h : a = b + c) (hb : b = 2) : a = 2 + c := by\n  rw [hb] at h\n  exact h", "h", "h : a = 2 + c", "local equation");
expectReplay("example (x y : ℝ) (h : x * y = 1) : True := by\n  rw [mul_comm] at h\n  trivial", "h", "h : y * x = 1", "first instance fixes the variables");
expectReplay("example (a b c : ℝ) (h : a * b * c = 1) : True := by\n  nth_rw 1 [mul_comm] at h\n  trivial", "h", "h : c * (a * b) = 1", "outermost instance first, parentheses where needed");
expectReplay("example (a b : ℝ) (h : a ≤ b) : True := by\n  rw [← sub_nonneg] at h\n  trivial", "h", "h : 0 ≤ b - a", "reversed iff");
expectReplay("example (x : ℝ) (h : |x| < 1) (hx : 0 ≤ x) : x < 1 := by\n  rw [abs_of_nonneg hx] at h\n  exact h", "h", "h : x < 1", "hypothesis argument fixes variables");
expectReplay("example (a : ℝ) (h : 2 * a = 4) : True := by\n  rw [show (2 : ℝ) * a = a * 2 by ring] at h\n  trivial", "h", "h : a * 2 = 4", "`show … by` rules");
expectReplay("example (n : ℕ) (h : n.succ = 5) : True := by\n  rw [Nat.succ_eq_add_one] at h\n  trivial", "h", "h : n + 1 = 5", "dot notation in the lemma");
expectReplay("example (a b : ℝ) (h : a + b = b + a + 0) : True := by\n  rw [add_zero, add_comm] at h\n  trivial", "h", "h : b + a = b + a", "several rules in order");
expectReplay("example (f : ℕ → ℕ) (hf : ∀ n, f n = n + 1) (h : f 3 = 4) : True := by\n  rw [hf 3] at h\n  trivial", "h", "h : 3 + 1 = 4", "local ∀-equation with an argument");
expectReplay("example (x : ℝ) (h : x ∈ Set.Icc (0:ℝ) 1) : True := by\n  simp only [Set.mem_Icc] at h\n  trivial", "h", "h : x ∈ Set.Icc (0:ℝ) 1  -- outdated", "simp can't be replayed: flagged, not presented as current");
expectReplay("example (x : ℝ) (h : x ∈ Set.Icc (0:ℝ) 1) : True := by\n  simp only [Set.mem_Icc] at h\n  exact h.1", "h.1", "h.1 : _  -- outdated", "projections of an outdated type are unknown");
expectReplay("example (a b : ℕ) (h : a = b) (hb : b = 2) : True := by\n  have : a = 2 := by rw [hb] at h; exact h\n  exact trivial", "h", "h : a = b", "a rewrite inside a nested `by` doesn't leak out");
expectReplay("example (p q : Prop) (hpq : p ↔ q) (hp : p ∧ True) : q := by\n  rw [hpq] at hp\n  exact hp.1", "hp", "hp : q ∧ True", "rewriting with an iff");
expectReplay("example (x : ℝ) (h : x = 1) : True := by\n  change x = 1 at h\n  trivial", "h", "h : x = 1", "`change … at h`");
expectReplay("example (a b c : ℝ) (hc : c ≠ 0) (h : a / c = b) : True := by\n  rw [div_eq_iff hc] at h\n  trivial", "h", "h : a = b * c",
  "the lemma's own variables can't capture locals with the same names (Lean: a = b * c)");
assert.deepStrictEqual(JSON.parse(JSON.stringify(bc.hypothesisChanges("hy", "(hy : P)\n  rw [a] at hy hz ⊢\n  -- rw [b] at hy\n  norm_num at *\n  exact hy", 0).map(c => c.kind))),
  ["rw", "opaque"], "comments are ignored; `at *` counts");

// 15. Checked against Lean on PR 45909: binders, `have h := lemma args`, ranges, big operators
console.log("15. Testing cases from checking PR 45909 against Lean...");
// Big-operator bodies use Mathlib's precedences (∑ body: 67), so `+ f n` is outside the sum.
assert.strictEqual(bc.parseTerm("∑ x ∈ Finset.range n, f x + f n").k, "bin", "∑ x ∈ s, f x + f n = (∑ …) + f n");
assert.strictEqual(bc.showTerm(bc.parseTerm("∑ x ∈ Finset.range n, (f x + f n)")), "∑ x ∈ Finset.range n, (f x + f n)");
// Binders match up to annotations and renaming; ranges match as terms.
const intA = bc.parseTerm("∫ y in (0 : ℝ)..s, g ((y : ℂ) * Complex.I)");
const intB = bc.parseTerm("∫ y : ℝ in (0:ℝ)..s, g ((y:ℂ) * Complex.I)");
const intC = bc.parseTerm("∫ (t : ℝ) in 0..s, g (↑t * Complex.I)");
assert(bc.matchTerm(intA, intB, new Set(), new Map()) && bc.matchTerm(intA, intC, new Set(), new Map()), "same integral, different spelling");
assert(!bc.matchTerm(intA, bc.parseTerm("∫ y in (0 : ℝ)..T, g ((y : ℂ) * Complex.I)"), new Set(), new Map()), "different range");
// `a..b` ranges are substituted; field accesses are not.
assert.strictEqual(bc.replaceWord("x in a..b, f x", "b", "T"), "x in a..T, f x");
assert.strictEqual(bc.replaceWord("x.b + b", "b", "T"), "x.b + T");

const hrectDecl = [
  "theorem foo : True := by",
  "  have hrect' : (∫ x : ℝ in (0:ℝ)..T, g ((x:ℂ)))",
  "      + Complex.I • (∫ y : ℝ in (0:ℝ)..s, g ((T:ℂ) + (y:ℂ) * Complex.I)) = 0 := by",
  "    simpa using hrect",
  "  have hvert_int : ∫ y in (0 : ℝ)..s, g ((T : ℂ) + (y : ℂ) * Complex.I)",
  "      = ∫ y in (0 : ℝ)..s, g ((y : ℂ) * Complex.I) :=",
  "    intervalIntegral.integral_congr (fun y hy => hvert y hy)",
  "  rw [hvert_int] at hrect'",
  "  linear_combination hrect'"
].join("\n");
expectReplay(hrectDecl, "hrect'", "hrect' : (∫ x : ℝ in (0:ℝ)..T, g (x : ℂ)) + Complex.I • (∫ y in (0 : ℝ)..s, g ((y : ℂ) * Complex.I)) = 0",
  "rewriting an integral spelled differently in the hypothesis (Lean agrees)");

// `have hb := lemma (a := …) … (f := fun x => …)`: instantiate and beta-reduce, as Lean does.
const NORM_INT = "{E : Type u_5} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b C : ℝ} {f : ℝ → E} (h : ∀ x ∈ Set.uIoc a b, ‖f x‖ ≤ C) : ‖∫ (x : ℝ) in a..b, f x‖ ≤ C * |b - a|";
const haveDecl = [
  "theorem foo : True := by",
  "    have hb := norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := T)",
  "      (C := M * Real.exp (2 * π * k * s / T))",
  "      (f := fun x : ℝ => H ((x : ℂ) + (s : ℂ) * Complex.I))",
  "      (fun x _ => hpoint x)",
  "    rwa [sub_zero, abs_of_pos hT.out] at hb"
].join("\n");
const hbInfo = bc.localVariableInfo("hb", haveDecl);
assert(hbInfo.inferNeeded && hbInfo.inferNeeded.term.startsWith("norm_integral_le_of_norm_le_const (a := (0 : ℝ))"), "the whole multi-line term is read");
asyncChecks.push(bc.inferPending(hbInfo.inferNeeded, haveDecl, async () => NORM_INT).then(r => assert.strictEqual(r.typeSignature,
  "hb : ‖∫ (x : ℝ) in (0 : ℝ)..T, H ((x : ℂ) + (s : ℂ) * Complex.I)‖ ≤ M * Real.exp (2 * π * k * s / T) * |T - (0 : ℝ)|",
  "Lean: ‖∫ (x : ℝ) in 0..T, H (↑x + ↑s * Complex.I)‖ ≤ M * rexp (2 * π * ↑k * s / T) * |T - 0|")));
// A local function applied to arguments: `have hb := hbound (-s) (by …)`.
const localApp = "theorem foo : True := by\n  have hbound : ∀ s : ℝ, |s| < a → ‖c‖ ≤ M * Real.exp (e * s) := by\n    intro s hsb\n    exact sorry\n  have hb := hbound (-s) (by rwa [abs_neg])\n  exact hb";
assert.strictEqual(bc.localVariableInfo("hb", localApp).typeSignature, "hb : ‖c‖ ≤ M * Real.exp (e * -s)");

// 16. Non-Mathlib PRs (AxiomMath/RogersRamanujan#3): files read at the PR's commit
console.log("16. Testing project indexing for collapsed diffs and non-Mathlib repos...");
const src = [
  "module",
  "public import RogersRamanujan.NumberTheory.QTheory.Defs",
  "public import Mathlib.Analysis.Normed.Ring.Basic",
  "/-! # Module doc",
  "theorem notReal : True := trivial -/",
  "namespace QTheory",
  "/-- Pentagonal sum. -/",
  "theorem hasSum_qPochhammerInf_self {R : Type*} [CommRing R]",
  "    {q : R} (hq : IsTopologicallyNilpotent q := by simp) :",
  "    HasSum (fun k : ℤ ↦ q ^ k) (q; q)_∞ := by",
  "  simp",
  "section",
  "theorem _root_.enormAt_X : enormAt φ q X = ‖q‖ₑ := rfl",
  "end",
  "@[deprecated (since := \"2026-11-12\")] alias old_name := hasSum_qPochhammerInf_self",
  "end QTheory"
].join("\n");
const scanned = JSON.parse(JSON.stringify(prScanner.scanSource(src, "RogersRamanujan/NumberTheory/QTheory/Pentagonal.lean")));
assert.deepStrictEqual(scanned.map(d => d.name), ["QTheory.hasSum_qPochhammerInf_self", "enormAt_X", "QTheory.old_name"], "namespaces qualify names; comments are skipped");
assert(scanned[0].typeSignature.endsWith(": HasSum (fun k : ℤ ↦ q ^ k) (q; q)_∞"), `a default value inside a binder doesn't end the signature: ${scanned[0].typeSignature}`);
assert.strictEqual(scanned[0].docstring, "Pentagonal sum.");
assert.strictEqual(scanned[0].module, "RogersRamanujan.NumberTheory.QTheory.Pentagonal");
prScanner.reset();
prScanner.declarations.set("enormAt_X", { name: "enormAt_X", element: {}, source: "pr_diff" });
prScanner.addDeclarations(scanned);
assert.strictEqual(prScanner.find("enormAt_X").source, "pr_diff", "declarations read from the page keep priority");
assert.strictEqual(prScanner.find("hasSum_qPochhammerInf_self").name, "QTheory.hasSum_qPochhammerInf_self", "short names find fetched declarations");
assert.strictEqual(prScanner.find("QTheory.hasSum_qPochhammerInf_self").lineNumber, 8);

// Tokens that aren't names: `∑'`, notation suffixes, simp options.
assert.strictEqual(tok("  ∑' n : ℤ, f n", "'"), null);
assert.strictEqual(tok("  enormAt φ q (a; g)_N ≠ ⊤", "_N"), null);
assert.strictEqual(tok("  simp +contextual [coeff_X_pow]", "contextual"), null);
assert.strictEqual(bc.localVariableInfo("m", "def evalAt (f : R⟦X⟧) : 𝕜 := ∑' m, φ (f.coeff m)").typeSignature, "m : _", "`∑'` binds its variable");
// Notation types and heads.
assert.strictEqual(bc.typeHead("ℝ≥0∞", null), "ENNReal");
assert.strictEqual(bc.typeHead("(Polynomial ℤ)⟦X⟧", null), "PowerSeries");
assert.strictEqual(bc.typeHead("R[X]", null), "Polynomial");
assert.strictEqual(bc.typeHead("(∀ᶠ (x : α) in l, ∀ i ∈ I, p i x) ↔ ∀ i ∈ I, ∀ᶠ (x : α) in l, p i x", null), "Iff", "binders inside parentheses don't hide a top-level ↔");
// The receiver fills its parameter, matched as a term (also instance parameters).
assert.strictEqual(bc.receiverResultType("{p : Prop} [self : Fact p] : p", "Fact (0 < T)"), "0 < T");
// (the type once the field is applied to its remaining arguments: `h.mpr hq : P x`)
assert.strictEqual(bc.receiverResultType("{a b : Prop} (self : a ↔ b) : b → a", "P x ↔ Q x"), "P x");
// `have h (i : ℕ) := lemma …` has a ∀ type.
const paramHave = "theorem t (ha : 0 < a) : True := by\n  have hag (i : ℕ) := hpos ha i\n  exact trivial";
asyncChecks.push(bc.inferPending(bc.localVariableInfo("hag", paramHave).inferNeeded, paramHave,
  async () => "{a : ℝ} (ha : 0 < a) (i : ℕ) : 0 < a ^ i").then(r => assert.strictEqual(r.typeSignature, "hag : ∀ (i : ℕ), 0 < a ^ i")));

// The worker follows in-repo imports (not Mathlib's) and marks the PR's own files.
const fakeFiles = {
  "RogersRamanujan/A.lean": "import RogersRamanujan.B\nimport Mathlib.Data.Nat.Basic\ntheorem a_thm : True := trivial",
  "RogersRamanujan/B.lean": "public import RogersRamanujan.C\nnamespace QTheory\ntheorem b_thm : True := trivial\nend QTheory",
  "RogersRamanujan/C.lean": "def c_def : ℕ := 0"
};
const realGetFileText = context.getFileText;
const fetched = [];
context.getFileText = async (ref) => { fetched.push(ref.path); return fakeFiles[ref.path] || null; };
asyncChecks.push(context.projectDeclarations({ owner: "AxiomMath", repo: "RogersRamanujan", sha: "abc", paths: ["RogersRamanujan/A.lean"] }).then(ds => {
  context.getFileText = realGetFileText;
  const plain = JSON.parse(JSON.stringify(ds));
  assert.deepStrictEqual(plain.map(d => `${d.name}${d.inPR ? "*" : ""}`), ["a_thm*", "QTheory.b_thm", "c_def"]);
  assert(!fetched.some(p => p.startsWith("Mathlib/")), "Mathlib imports are left to Loogle");
}));

// 17. Every message the worker handles works end to end (no network in tests: lookups find nothing).
console.log("17. Testing the worker's message handlers...");
assert.strictEqual(workerListeners.length, 1, "the worker registers one message listener");
const workerSrc = fs.readFileSync(path.join(__dirname, '..', 'background/service_worker.js'), 'utf8');
const handlerBlock = workerSrc.slice(workerSrc.indexOf('const MESSAGE_HANDLERS = {'), workerSrc.indexOf('const MESSAGE_FALLBACKS'));
const handled = [...handlerBlock.matchAll(/^  ([A-Z_]+): /gm)].map(m => m[1]);
assert(handled.length >= 9, `found the handler table (${handled.join(', ')})`);
// Every action the page, popup or options page sends must have a handler (the content
// script answers GET_PAGE_INFO / SETTINGS_UPDATED itself).
const senders = ['content/content.js', 'popup/popup.js', 'options/options.js'].map(f => fs.readFileSync(path.join(__dirname, '..', f), 'utf8')).join('\n');
const sent = new Set([...senders.matchAll(/action:\s*["']([A-Z_]+)["']/g)].map(m => m[1]));
['GET_PAGE_INFO', 'SETTINGS_UPDATED'].forEach(a => sent.delete(a));
for (const a of sent) assert(handled.includes(a), `the worker handles ${a}`);
const sampleRequests = {
  LOOKUP_TOKEN: { token: 'foo_bar', subToken: 'foo_bar' },
  PROJECT_DECLARATIONS: { owner: 'o', repo: 'r', sha: 'abc', paths: ['A.lean'] },
  CONSTANT_SIGNATURE: { name: 'foo_bar' },
  INFER_PATTERN: { pattern: 'h', term: 'foo_bar x', name: 'h' },
  STRUCTURE_FIELD: { type: 'α ≃ β', index: 1, rest: [] },
  GET_SETTINGS: {},
  SET_SETTINGS: { settings: { hoverDelay: 300 } },
  CLEAR_CACHE: {},
  TEST_HELPER: { url: 'http://127.0.0.1:9', token: 'x' },
  EXACT_HOVER: { fileRef: null },
  HELPER_RUN: { owner: 'o', repo: 'r', paths: ['A.lean'] },
  HELPER_ALLOW: { repo: 'o/r' },
  FILE_VARIABLE: { name: 'hT', fileRef: null },
  FILE_INSTANCES: { fileRef: null },
  NOTATION_DOC: { name: '«term_+_»' },
  VERSO_REGIONS: { fileRef: null }
};
// Handlers run concurrently; the worker logs failures as "[Lean Lens] message handler failed: ACTION …".
const realWarn = console.warn;
const handlerFailures = [];
console.warn = (...a) => {
  const text = a.map(x => (x instanceof Error ? `${x.name}: ${x.message}` : String(x))).join(' ');
  if (/message handler failed/.test(text)) handlerFailures.push(text);
  else realWarn(...a);
};
const handlerRuns = handled.map(action => new Promise((resolve, reject) => {
  const timer = setTimeout(() => reject(new Error(`${action}: no response`)), 10000);
  let keptOpen;
  try {
    keptOpen = workerListeners[0](Object.assign({ action }, sampleRequests[action] || {}), {}, (res) => { clearTimeout(timer); resolve(res); });
  } catch (err) {
    clearTimeout(timer);
    reject(new Error(`${action} threw: ${err.message}`));
    return;
  }
  if (keptOpen !== true) { clearTimeout(timer); reject(new Error(`${action} doesn't respond asynchronously`)); }
}));
asyncChecks.push(Promise.all(handlerRuns).then(() => {
  console.warn = realWarn;
  assert.deepStrictEqual(handlerFailures, [], `message handlers failed:\n${handlerFailures.join('\n')}`);
}, (err) => { console.warn = realWarn; throw err; }));
assert.strictEqual(workerListeners[0]({ action: 'NO_SUCH_ACTION' }, {}, () => {}), false, "unknown actions are ignored");

// 18. Hovering a gap shows the term there with its type, as Lean's infoview does (`a b : Y`).
//     Expected outputs were checked against Lean's own hovers (lean-lsp) on the same code.
console.log("18. Testing gap hovers (terms and their types)...");
{
  const SIGS = {
    'mul_pos': '{α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Preorder α] [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b',
    'abs_le': '{α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearOrder α] [IsOrderedAddMonoid α] {a b : α} : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b',
    'Iff.mp': '{a b : Prop} (self : a ↔ b) : a → b',
    'Iff.mpr': '{a b : Prop} (self : a ↔ b) : b → a',
    'le_trans': '{α : Type u_1} [inst : Preorder α] {a b c : α} : a ≤ b → b ≤ c → a ≤ c',
    'LE.le.trans': '{α : Type u_1} [inst : Preorder α] {a b c : α} : a ≤ b → b ≤ c → a ≤ c',
    'Set.mem_Icc': '{α : Type u_1} [inst : Preorder α] {a b x : α} : x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b',
    'Nat.cast_le': '{α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α] [CharZero α] {m n : ℕ} : (↑m : α) ≤ ↑n ↔ m ≤ n',
    'Finset.sum_le_sum': '{ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι} [AddLeftMono N] (h : ∀ i ∈ s, f i ≤ g i) : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i',
    'Filter.Tendsto.mono_left': '{α : Type u_1} {β : Type u_2} {f : α → β} {x y : Filter α} {z : Filter β} (hx : Filter.Tendsto f x z) (h : y ≤ x) : Filter.Tendsto f y z',
    'ContinuousAt.tendsto': '{X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {x : X} (h : ContinuousAt f x) : Filter.Tendsto f (nhds x) (nhds (f x))'
  };
  const sigOf = async (n) => SIGS[n] || null;
  // `|` marks the hovered character in the last line of `code`.
  const gap = async (code, marker) => {
    const lines = code.split('\n');
    const line = lines[lines.length - 1];
    const at = line.indexOf(marker.replace('|', '')) + marker.indexOf('|');
    const j = bc.joinStatement(lines, lines.length - 1);
    const hit = bc.termAtOffset(j.text, j.lineStart + at);
    if (!hit) return null;
    const type = await bc.termTypeOf(hit.node, hit.src, code, sigOf, { parent: hit.parent, path: hit.path, expected: hit.expected });
    return type ? `${bc.termDisplay(hit.node, code)} : ${type}` : `${hit.text} : ?`;
  };
  const H = (binders, body) => `example ${binders} : True := by\n  ${body}`;
  const cases = [
    [H('(X Y : Type) (a : X → Y) (b : X)', 'have := a b'), 'a| b', 'a b : Y'],
    [H('(f : ℕ → ℕ → ℕ) (n : ℕ)', 'have := f n'), 'f| n', 'f n : ℕ → ℕ'],
    // Lean prints unassigned implicit arguments as metavariables.
    [H('(x : ℝ) (hx : 0 < x)', 'have := mul_pos hx'), 'mul_pos| hx', 'mul_pos hx : 0 < ?b → 0 < x * ?b'],
    [H('(x y : ℝ) (hx : 0 < x) (hy : 0 < y)', 'have := mul_pos hx hy'), 'mul_pos hx| hy', 'mul_pos hx hy : 0 < x * y'],
    [H('(a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c)', 'exact le_trans h1 h2'), 'le_trans| h1', 'le_trans h1 h2 : a ≤ c'],
    // Generalized field notation, on a local and on a constant.
    [H('(a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c)', 'exact h1.trans h2'), 'h1.trans| h2', 'h1.trans h2 : a ≤ c'],
    [H('(x : ℝ) (h : |x| ≤ 1)', 'have := abs_le.mp h'), 'abs_le.mp| h', 'abs_le.mp h : -1 ≤ x ∧ x ≤ 1'],
    [H('(x : ℝ) (h : |x| ≤ 1)', 'have := (abs_le.mp h).2'), 'h)|.2', '(abs_le.mp h).2 : x ≤ 1'],
    [H('(x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)', 'have := Set.mem_Icc.mp hx'), 'Set.mem_Icc.mp| hx', 'Set.mem_Icc.mp hx : 0 ≤ x ∧ x ≤ 1'],
    // An anonymous constructor fixes variables through its components.
    [H('(u : ℝ) (h1 : -1 ≤ u) (h2 : u ≤ 1)', 'exact (abs_le).mpr ⟨h1, h2⟩'), '(abs_le).mpr| ⟨', 'abs_le.mpr ⟨h1, h2⟩ : |u| ≤ 1'],
    // …and so does the use of a term: `(abs_le)` here is `|u| ≤ 1 ↔ …`, as Lean shows it.
    [H('(u : ℝ) (h1 : -1 ≤ u) (h2 : u ≤ 1)', 'exact (abs_le).mpr ⟨h1, h2⟩'), '|(abs_le)', 'abs_le : |u| ≤ 1 ↔ -1 ≤ u ∧ u ≤ 1'],
    [H('(m n : ℕ) (hmn : m ≤ n)', 'have := (Nat.cast_le (α := ℝ)).mpr hmn'), '(Nat.cast_le (α := ℝ)).mpr| hmn', '(Nat.cast_le (α := ℝ)).mpr hmn : ↑m ≤ ↑n'],
    [H('(s : Finset ℕ) (g k : ℕ → ℝ) (hg : ∀ i ∈ s, g i ≤ k i)', 'have := Finset.sum_le_sum hg'), 'Finset.sum_le_sum| hg', 'Finset.sum_le_sum hg : ∑ i ∈ s, g i ≤ ∑ i ∈ s, k i'],
    // Operators, binders, numerals (typed from their neighbours), `fun`, coercions.
    [H('(x : ℝ)', 'have : x + 1 = 2 * x ^ 2 := sorry'), 'x |+', 'x + 1 : ℝ'],
    [H('(x : ℝ)', 'have : x + 1 = 2 * x ^ 2 := sorry'), 'x ^ |2', '2 : ℕ'],
    [H('(x : ℝ)', 'have : x + 1 = 2 * x ^ 2 := sorry'), '= |2', '2 : ℝ'],
    [H('(n : ℕ) (g : ℕ → ℝ)', 'have : ∑ i ∈ Finset.range n, g i = 0 := sorry'), 'g i |=', '∑ i ∈ Finset.range n, g i = 0 : Prop'],
    [H('(n : ℕ) (g : ℕ → ℝ)', 'have : ∑ i ∈ Finset.range n, g i = 0 := sorry'), '|∑', '∑ i ∈ Finset.range n, g i : ℝ'],
    [H('(p : ℝ → Prop)', 'have : ∀ z : ℝ, p z := sorry'), '|∀', '∀ z : ℝ, p z : Prop'],
    [H('(s : Set ℝ)', 'have : ∀ x ∈ s, 0 ≤ x := sorry'), '0 |≤', '0 ≤ x : Prop'],
    [H('(n : ℕ)', 'have := fun (x : ℝ) => x + 1'), '|fun', 'fun (x : ℝ) => x + 1 : ℝ → ℝ'],
    [H('(n : ℕ)', 'have := ((n : ℝ) + 1)'), '((n : ℝ) |+', '↑n + 1 : ℝ'],
    [H('(f g : ℕ → ℕ)', 'have := f ∘ g'), 'f |∘', 'f ∘ g : ℕ → ℕ'],
    [H('(t : ℝ → ℝ) (s : Set ℝ)', "have := t ⁻¹' s"), "t |⁻¹'", "t ⁻¹' s : Set ℝ"],
    [H('(k : ℤ) (s : ℝ)', 'have := 2 * π * k * s'), '2 * π * k |*', '2 * π * k * s : ℝ'],
    [H('(hf : ∀ n, f n = n + 1)', 'rw [hf 3] at h'), 'hf| 3', 'hf 3 : f 3 = 3 + 1'],
    // `hs : A ⊆ B` applied to a membership proof.
    [H('(x : ℝ) (A B : Set ℝ) (hs : A ⊆ B) (hx : x ∈ A)', 'have := hs hx'), 'hs| hx', 'hs hx : x ∈ B'],
    // The declared type of `have h : T := term` fixes what the term leaves open.
    [H('(c e b : ℝ)', 'have ht : Filter.Tendsto (fun s : ℝ => c * Real.exp (e * s)) (nhdsWithin b (Set.Iio b)) (nhds (c * Real.exp (e * b))) :=\n    (ContinuousAt.tendsto (h := by fun_prop)).mono_left nhdsWithin_le_nhds'),
      '.mono_left| nhds', '(ContinuousAt.tendsto (h := by fun_prop)).mono_left nhdsWithin_le_nhds : Filter.Tendsto (fun s : ℝ => c * Real.exp (e * s)) (nhdsWithin b (Set.Iio b)) (nhds (c * Real.exp (e * b)))'],
    // Not terms: binder names, `intro` names, patterns, `linear_combination` syntax.
    [H('(n : ℕ)', 'intro x y'), 'x| y', null],
    [H('(n : ℕ)', 'obtain ⟨x, hx⟩ := foo n'), '⟨x,| hx', null],
    [H('(h : 2 ≤ 3)', 'linear_combination h + 2 * h'), 'h |+', null],
    ['theorem foo {s y : ℝ} (f g : ℕ → ℕ) : True := by', 'f| g', null],
    [H('(n : ℕ)', 'exact foo (f g : ℕ)'), 'f| g', 'f g : ?']
  ];
  for (const [code, marker, want] of cases) {
    asyncChecks.push(gap(code, marker).then(got => assert.strictEqual(got, want, `gap hover at ${marker}`)));
  }

  // A term broken across lines is read whole; a `by` block on the line before isn't continued.
  const joined = bc.joinStatement(['  exact foo a', '    (bar b) c', '  trivial'], 1);
  assert.strictEqual(joined.text.replace(/\s+/g, ' ').trim(), 'exact foo a (bar b) c', 'continuation lines join the statement');
  assert.strictEqual(bc.termAtOffset(joined.text, joined.lineStart + 11).text, 'foo a (bar b) c', 'the gap after `(bar b)` is the whole application');
  const calc = bc.joinStatement(['  calc a = b := by rw [h]', '    _ = c + d := by ring'], 1);
  assert(/by rw \[h\];/.test(calc.text), `a line ending a \`by\` block is closed before the next one: ${calc.text}`);
  assert.strictEqual(bc.termAtOffset(calc.text, calc.lineStart + 10).text, 'c + d', 'calc step after a `by` line');
  const nested = bc.joinStatement(['  have h : P := by', '    exact foo a b'], 1);
  assert.strictEqual(nested.lineStart, 0, 'a nested tactic block starts its own statement');

  // Constants are shown as Lean's hover shows them: `name.{u} binders : type`.
  assert.strictEqual(bc.leanSignature('mul_pos', SIGS.mul_pos),
    'mul_pos.{u_1} {α : Type u_1} [MulZeroClass α] {a b : α} [Preorder α] [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b');
  assert.strictEqual(bc.leanSignature('Finset.sum_le_sum', SIGS['Finset.sum_le_sum']).slice(0, 52), 'Finset.sum_le_sum.{u_1, u_5} {ι : Type u_1} {N : Typ');
  assert.strictEqual(bc.leanSignature('Real.exp', 'ℝ → ℝ'), 'Real.exp : ℝ → ℝ');
  assert.strictEqual(bc.leanSignature('foo', ': True'), 'foo : True');
  assert.strictEqual(bc.leanSignature('Foo', '(α : Type*)'), 'Foo (α : Type*)', 'binders without a type (a structure)');
  const loogleHit = context.hitToResult({ name: 'abs_le', type: SIGS.abs_le, doc: 'd', module: 'Mathlib.Algebra.Order.AbsoluteValue' });
  assert(loogleHit.typeSignature.startsWith('abs_le.{u_1} {α : Type u_1} [AddCommGroup α]'), `Loogle hits print like Lean: ${loogleHit.typeSignature}`);
  // PR declarations too, keeping the bare `binders : type` for the term machinery.
  prScanner.reset();
  prScanner.scanDiffLines({ querySelectorAll: (sel) => (sel === '.diff-text-inner' ? [
    { textContent: 'theorem foo_le {x : ℝ} (hx : 0 ≤ x) : x ≤ x + 1 := by', classList: { contains: () => false }, getAttribute: () => null, closest: () => null }
  ] : []) }, 'A.lean');
  const fooLe = prScanner.declarations.get('foo_le');
  assert.strictEqual(fooLe.typeSignature, 'foo_le {x : ℝ} (hx : 0 ≤ x) : x ≤ x + 1', 'PR declaration printed like Lean');
  assert.strictEqual(fooLe.signature, '{x : ℝ} (hx : 0 ≤ x) : x ≤ x + 1');
  prScanner.reset();

  // Under a term, Lean's hover shows its notation's docstring: these names have it (on Loogle).
  const docOf = (t, o) => { const h = bc.termAtOffset(t, o); return h && bc.notationDocName(h); };
  assert.strictEqual(docOf('x + 1 = 2', 2), '«term_+_»');
  assert.strictEqual(docOf('x + 1 = 2', 6), '«term_=_»');
  assert.strictEqual(docOf('(x + 1) * 2', 0), 'Lean.Parser.Term.paren', 'on the parentheses: their docs');
  assert.strictEqual(docOf('(x + 1) * 2', 3), '«term_+_»', 'inside them: the operator');
  assert.strictEqual(docOf('(n : ℝ) + 1', 0), 'Lean.Parser.Term.typeAscription');
  assert.strictEqual(docOf('(abs_le.mp h).2', 13), 'Lean.Parser.Term.proj');
  assert.strictEqual(docOf('∀ x ∈ s, 0 ≤ x', 0), 'Lean.«term∀__,_»', 'binder predicates have their own notation');
  assert.strictEqual(docOf('∀ x, 0 ≤ x', 0), null, 'a plain `∀` has none');
  assert.strictEqual(docOf('∑ i ∈ s, f i', 0), 'BigOperators.bigsum');
  assert.strictEqual(docOf("t ⁻¹' s", 2), "Set.«term_⁻¹'_»");
  assert.strictEqual(docOf('f x y', 1), null, 'applications have no docstring');
  assert.strictEqual(docOf('¬p', 0), '«term¬_»');
  // Joined lines know where they start (to shade a term on each of its lines).
  const multi = bc.joinStatement(['  exact foo a', '    (bar b) c'], 1);
  assert.deepStrictEqual(JSON.parse(JSON.stringify([multi.from, multi.starts])), [0, [0, 14]], 'line starts in the joined text (one character joins lines)');

  // Docstrings: code spans are kept as code (`a * b` isn't emphasis), indented bullets are lists.
  const md = tooltipView.renderMarkdown('`a * b` computes the product of `a` and `b`.\n\nConventions for notations in identifiers:\n\n * The recommended spelling of `*` in identifiers is `mul`.');
  assert(md.includes('<code class="verso-inline-code">a * b</code>') && !md.includes('<em>'), `inline code isn't emphasis: ${md}`);
  assert(md.includes('<ul><li>The recommended spelling of <code class="verso-inline-code">*</code>'), `indented bullets are a list: ${md}`);
  const fenced = tooltipView.renderMarkdown('```lean\nexample : a < b := h\n```');
  assert(fenced.includes('a &lt; b') && !fenced.includes('&amp;lt;'), `code blocks are escaped once: ${fenced}`);
}
console.log("   ✓ Gap hovers verified.\n");

// 19. Section variables: a declaration's signature includes the `variable`s it takes, as Lean
//     decides (PR 45935: `gelfandRadiusNorm (x : L)` is `gelfandRadiusNorm K L x`). Expected
//     signatures are Lean's own hovers on the same code (lean-lsp).
console.log("19. Testing section variables in declaration signatures...");
{
  const src = [
    'variable (K L M : Type*) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]',
    '  [Algebra L M] [IsScalarTower K L M] {F : Type*} [FunLike F L M] [AlgHomClass F K L M]',
    '',
    'section',
    '',
    'variable [FiniteDimensional K L]',
    '',
    'open Classical in',
    '/-- A probe. -/',
    'noncomputable def gNorm (x : L) : ℝ := if algebraMap K L 1 = x then 1 else 0',
    '',
    'variable {K L} in',
    'theorem gNorm_eq_zero {x : L} (hx : algebraMap K L 1 ≠ x) : gNorm K L x = 0 := by',
    '  simp [gNorm, hx]',
    '',
    'variable {M K L} in',
    'omit [Algebra L M] [IsScalarTower K L M] in',
    'theorem gNorm_map (f : F) (x : L) : gNorm K L x = gNorm K L x := rfl',
    '',
    'theorem gNorm_self (x : K) : gNorm K K x = gNorm K K x := rfl',
    '',
    'end',
    '',
    'theorem outside (x : L) : x = x := by',
    '  have := gNorm K L x',
    '  rfl',
    '',
    'include K in',
    'theorem included (x : L) : x = x := rfl',
    '',
    'alias outside_def := outside',
    'theorem after_alias (x : M) : x = x := rfl'
  ].join('\n');
  const sigs = new Map(prScanner.scanSource(src, 'Probe.lean').map(d => [d.name, d.typeSignature]));
  // Lean's hovers: theorems take the variables their statement mentions, the ones those
  // depend on, and every instance argument whose variables are all included…
  assert.strictEqual(sigs.get('gNorm_eq_zero'), 'gNorm_eq_zero.{u_1, u_2} {K : Type u_1} {L : Type u_2} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {x : L} (hx : algebraMap K L 1 ≠ x) : gNorm K L x = 0');
  // …with universes named when the `variable` command is elaborated (`F` is `u_4` without `M`).
  assert.strictEqual(sigs.get('gNorm_map'), 'gNorm_map.{u_1, u_2, u_4} {K : Type u_1} {L : Type u_2} [Field K] [Field L] [Algebra K L] {F : Type u_4} [FiniteDimensional K L] (f : F) (x : L) : gNorm K L x = gNorm K L x');
  assert.strictEqual(sigs.get('gNorm_self'), 'gNorm_self.{u_1} (K : Type u_1) [Field K] (x : K) : gNorm K K x = gNorm K K x');
  // A definition also takes the variables its body mentions (`K` here).
  assert(sigs.get('gNorm').startsWith('gNorm.{u_1, u_2} (K : Type u_1) (L : Type u_2) [Field K] [Field L] [Algebra K L]'), sigs.get('gNorm'));
  // A theorem doesn't take variables only its proof mentions; the section's variable is gone after `end`.
  assert.strictEqual(sigs.get('outside'), 'outside.{u_2} (L : Type u_2) [Field L] (x : L) : x = x');
  assert.strictEqual(sigs.get('included'), 'included.{u_1, u_2} (K : Type u_1) (L : Type u_2) [Field K] [Field L] [Algebra K L] (x : L) : x = x', '`include K in`');
  assert.strictEqual(sigs.get('outside_def'), 'alias outside_def := outside', 'an alias is one line');
  assert.strictEqual(sigs.get('after_alias'), 'after_alias.{u_3} (M : Type u_3) [Field M] (x : M) : x = x', 'the line after an alias is read');
  // Diff rows give the same; a fetched full file upgrades a page entry (hunks may hide `variable`s).
  prScanner.reset();
  const rowsOf = (lines) => lines.map(l => ({ textContent: l, classList: { contains: () => false }, getAttribute: () => null, closest: () => null }));
  prScanner.scanDiffLines({ querySelectorAll: (sel) => (sel === '.diff-text-inner' ? rowsOf(['noncomputable def gNorm (x : L) : ℝ := if algebraMap K L 1 = x then 1 else 0']) : []) }, 'Probe.lean');
  const pageDecl = prScanner.declarations.get('gNorm');
  assert.strictEqual(pageDecl.typeSignature, 'gNorm (x : L) : ℝ', 'without the `variable` line, the page only knows the written binders');
  prScanner.addDeclarations(prScanner.scanSource(src, 'Probe.lean'));
  assert.strictEqual(prScanner.declarations.get('gNorm'), pageDecl, 'the page entry is kept (it can jump to the line)');
  assert(pageDecl.signature.startsWith('(K : Type u_1) (L : Type u_2) [Field K]'), `…with the full file's signature: ${pageDecl.signature}`);
  prScanner.reset();
  // Gap hovers apply arguments to the full signature: `gelfandRadiusNorm K L x : ℝ`.
  asyncChecks.push(bc.termTypeOf(bc.parseTerm('gNorm K L x'), 'gNorm K L x', 'example (K L : Type*) (x : L) : True := by\n  trivial',
    async (n) => (n === 'gNorm' ? '(K : Type u_1) (L : Type u_2) [Field K] [Field L] [Algebra K L] (x : L) : ℝ' : null)).then(t => assert.strictEqual(t, 'ℝ', 'all three arguments')));
  // A norm is a bundled function: `gelfandRadiusNormAux K L x : ℝ` for `gelfandRadiusNormAux K L : AlgebraNorm K L`.
  asyncChecks.push(bc.termTypeOf(bc.parseTerm('gAux K L x'), 'gAux K L x', 'example (K L : Type*) (x : L) : True := by\n  trivial',
    async (n) => (n === 'gAux' ? '(K : Type u_1) (L : Type u_2) [NormedField K] [Field L] [Algebra K L] : AlgebraNorm K L' : null)).then(t => assert.strictEqual(t, 'ℝ', 'applying an AlgebraNorm')));
}
console.log("   ✓ Section variables verified.\n");

// 20. PR 45819 (semilinear PiTensorProduct): shadowed variables, out-param instances, universes,
//     semilinear notation, binders printed as Lean prints them. Expected outputs are Lean's own
//     hovers (lean-lsp) on a probe with the same `variable` layout.
console.log("20. Testing semilinear maps, universes and Lean's binder printing (PR 45819)...");
{
  const src = [
    'open Function PiTensorProduct TensorProduct',
    'namespace LeanLensProbe',
    'section Semiring',
    'variable {ι ι₂ ι₃ : Type*}',
    'variable {R S : Type*} [CommSemiring R] [CommSemiring S] {σ : R →+* S}',
    'variable {R₁ R₂ : Type*}',
    'variable {s : ι → Type*} [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]',
    'variable {M : Type*} [AddCommMonoid M] [Module R M]',
    'variable {E : Type*} [AddCommMonoid E] [Module S E]',
    'variable {F : Type*} [AddCommMonoid F]',
    'variable (R) (s)',
    'variable {s}',
    'def tp (f : Π i, s i) : ⨂[R] i, s i := tprod R f',
    'variable {R}',
    'theorem upd [DecidableEq ι] (f : Π i, s i) (i : ι) (m : s i) : update f i m = update f i m := rfl',
    'theorem ri_symm (e : ι ≃ ι₂) (x : ⨂[R] i : ι₂, s (e.symm i)) :',
    '    (reindex R s e).symm x = (reindex R s e).symm x := rfl',
    'section map',
    'variable {R₃ : Type*} [CommSemiring R₂] [CommSemiring R₃]',
    '  {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]',
    '  {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]',
    '  {s t t\' : ι → Type*} {N₃ : Type*}',
    '  [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]',
    '  [∀ i, AddCommMonoid (t i)] [∀ i, Module R₂ (t i)]',
    '  [∀ i, AddCommMonoid (t\' i)] [∀ i, Module R₃ (t\' i)]',
    '  [AddCommMonoid N₃] [Module R₃ N₃]',
    '  (g : Π i, t i →ₛₗ[σ₂₃] t\' i) (f : Π i, s i →ₛₗ[σ₁₂] t i)',
    'def mp : (Π i, s i) → (Π i, t i) := fun x i ↦ f i (x i)',
    'theorem mp_apply (x : Π i, s i) (i : ι) : mp f x i = f i (x i) := rfl',
    'theorem comp_apply\' (i : ι) (x : s i) : (g i ∘ₛₗ f i) x = g i (f i x) := rfl',
    'def eqv (e : Π i, s i ≃ₛₗ[σ₁₂] t i) : (Π i, s i) → (Π i, t i) := fun x i ↦ e i (x i)',
    'theorem upd2 [DecidableEq ι] (i : ι) (u : s i →ₛₗ[σ₁₂] t i) : update f i u = update f i u := rfl',
    'variable (R s t) in',
    'def mpm : (Π i, s i →ₛₗ[σ₁₂] t i) → (Π i, s i) → (Π i, t i) := fun f x i ↦ f i (x i)',
    'end map',
    'variable (R s) in',
    'def ri (e : ι ≃ ι₂) : (⨂[R] i : ι, s i) ≃ₗ[R] ⨂[R] i : ι₂, s (e.symm i) := reindex R s e',
    'variable {t : ι → Type*} [∀ i, AddCommMonoid (t i)] [∀ i, Module S (t i)]',
    'def bb : ℕ → ℕ := fun t ↦ t + 1',
    'def eq0 : ℕ ≃ ℕ where',
    '  toFun n := n',
    '  invFun t := t',
    '  left_inv t := rfl',
    '  right_inv t := rfl',
    'theorem tt (f : Π i, t i) : f = f := rfl',
    'end Semiring',
    'end LeanLensProbe'
  ].join('\n');
  const sigs = new Map(prScanner.scanSource(src, 'Probe.lean').map(d => [d.name.replace(/^LeanLensProbe\./, ''), d.typeSignature]));
  const I = (x, R = 'R') => `[(i : ι) → AddCommMonoid (${x} i)] [(i : ι) → Module ${R} (${x} i)]`;
  const LEAN = {
    // The redeclared `s` shadows the first: Lean still names the first's universe (`u_8`),
    // and the first's instances don't come along.
    tp: `LeanLensProbe.tp.{u_1, u_4, u_8} {ι : Type u_1} (R : Type u_4) [CommSemiring R] {s : ι → Type u_8} ${I('s')} (f : (i : ι) → s i) : ⨂[R] (i : ι), s i`,
    upd: 'LeanLensProbe.upd.{u_1, u_8} {ι : Type u_1} {s : ι → Type u_8} [(i : ι) → AddCommMonoid (s i)] [DecidableEq ι] (f : (i : ι) → s i) (i : ι) (m : s i) : update f i m = update f i m',
    ri_symm: `LeanLensProbe.ri_symm.{u_1, u_2, u_4, u_8} {ι : Type u_1} {ι₂ : Type u_2} {R : Type u_4} [CommSemiring R] {s : ι → Type u_8} ${I('s')} (e : ι ≃ ι₂) (x : ⨂[R] (i : ι₂), s (e.symm i)) : (reindex R s e).symm x = (reindex R s e).symm x`,
    mp: `LeanLensProbe.mp.{u_1, u_4, u_7, u_13, u_14} {ι : Type u_1} {R : Type u_4} [CommSemiring R] {R₂ : Type u_7} [CommSemiring R₂] {σ₁₂ : R →+* R₂} {s : ι → Type u_13} {t : ι → Type u_14} ${I('s')} ${I('t', 'R₂')} (f : (i : ι) → s i →ₛₗ[σ₁₂] t i) : ((i : ι) → s i) → (i : ι) → t i`,
    // A bundled map applied through the coercion prints `(f i) (x i)`.
    mp_apply: `LeanLensProbe.mp_apply.{u_1, u_4, u_7, u_13, u_14} {ι : Type u_1} {R : Type u_4} [CommSemiring R] {R₂ : Type u_7} [CommSemiring R₂] {σ₁₂ : R →+* R₂} {s : ι → Type u_13} {t : ι → Type u_14} ${I('s')} ${I('t', 'R₂')} (f : (i : ι) → s i →ₛₗ[σ₁₂] t i) (x : (i : ι) → s i) (i : ι) : mp f x i = (f i) (x i)`,
    // `∘ₛₗ` needs `RingHomCompTriple σ₁₂ σ₂₃ ?σ₁₃`: instance search takes `σ₁₃` and the instance.
    "comp_apply'": `LeanLensProbe.comp_apply'.{u_1, u_4, u_7, u_12, u_13, u_14, u_15} {ι : Type u_1} {R : Type u_4} [CommSemiring R] {R₂ : Type u_7} {R₃ : Type u_12} [CommSemiring R₂] [CommSemiring R₃] {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] {s : ι → Type u_13} {t : ι → Type u_14} {t' : ι → Type u_15} ${I('s')} ${I('t', 'R₂')} ${I("t'", 'R₃')} (g : (i : ι) → t i →ₛₗ[σ₂₃] t' i) (f : (i : ι) → s i →ₛₗ[σ₁₂] t i) (i : ι) (x : s i) : (g i ∘ₛₗ f i) x = (g i) ((f i) x)`,
    // `≃ₛₗ[σ₁₂]` needs `RingHomInvPair σ₁₂ ?σ₂₁`.
    eqv: `LeanLensProbe.eqv.{u_1, u_4, u_7, u_13, u_14} {ι : Type u_1} {R : Type u_4} [CommSemiring R] {R₂ : Type u_7} [CommSemiring R₂] {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {s : ι → Type u_13} {t : ι → Type u_14} ${I('s')} ${I('t', 'R₂')} (e : (i : ι) → s i ≃ₛₗ[σ₁₂] t i) : ((i : ι) → s i) → (i : ι) → t i`,
    upd2: `LeanLensProbe.upd2.{u_1, u_4, u_7, u_13, u_14} {ι : Type u_1} {R : Type u_4} [CommSemiring R] {R₂ : Type u_7} [CommSemiring R₂] {σ₁₂ : R →+* R₂} {s : ι → Type u_13} {t : ι → Type u_14} ${I('s')} ${I('t', 'R₂')} (f : (i : ι) → s i →ₛₗ[σ₁₂] t i) [DecidableEq ι] (i : ι) (u : s i →ₛₗ[σ₁₂] t i) : update f i u = update f i u`,
    mpm: `LeanLensProbe.mpm.{u_1, u_4, u_7, u_13, u_14} {ι : Type u_1} (R : Type u_4) [CommSemiring R] {R₂ : Type u_7} [CommSemiring R₂] {σ₁₂ : R →+* R₂} (s : ι → Type u_13) (t : ι → Type u_14) ${I('s')} ${I('t', 'R₂')} : ((i : ι) → s i →ₛₗ[σ₁₂] t i) → ((i : ι) → s i) → (i : ι) → t i`,
    ri: `LeanLensProbe.ri.{u_1, u_2, u_4, u_8} {ι : Type u_1} {ι₂ : Type u_2} (R : Type u_4) [CommSemiring R] (s : ι → Type u_8) ${I('s')} (e : ι ≃ ι₂) : (⨂[R] (i : ι), s i) ≃ₗ[R] ⨂[R] (i : ι₂), s (e.symm i)`,
    // Names bound in a body (`fun t ↦`, `invFun t :=`) aren't the section variable `t`.
    bb: 'LeanLensProbe.bb : ℕ → ℕ',
    eq0: 'LeanLensProbe.eq0 : ℕ ≃ ℕ',
    tt: 'LeanLensProbe.tt.{u_1, u_12} {ι : Type u_1} {t : ι → Type u_12} [(i : ι) → AddCommMonoid (t i)] (f : (i : ι) → t i) : f = f'
  };
  for (const [name, want] of Object.entries(LEAN)) assert.strictEqual(sigs.get(name), want, `Lean's hover of ${name}`);
  // Lean's universe names for the variables at a line (`s : ι → Type u_8`), shadowed ones included.
  const at = (line, name) => prScanner.variablesAt(src, line).filter(v => v.name === name).pop();
  assert.strictEqual(at(7, 's').type, 'ι → Type u_8');
  assert.strictEqual(at(30, 's').type, 'ι → Type u_13', 'the redeclared `s` in section map');
  assert.strictEqual(at(30, 'R₃').type, 'Type u_12');

  // A dotted declaration's last segment doesn't take the key of a declaration with that name.
  prScanner.reset();
  const row = (t, n) => ({ textContent: t, classList: { contains: () => false }, getAttribute: () => null, closest: (sel) => (sel === '[data-line-number]' ? { getAttribute: () => String(n) } : null) });
  prScanner.scanDiffLines({ querySelectorAll: (sel) => (sel === '.diff-text-inner' ? [row('theorem lift.tprod (f : Π i, s i) : lift φ (tprod R f) = φ f := rfl', 445)] : []) }, 'Basic.lean');
  prScanner.addDeclarations([{ name: 'PiTensorProduct.tprod', declaredAs: 'tprod', shortName: 'tprod', kind: 'def', typeSignature: 'PiTensorProduct.tprod : X', signature: ': X', filePath: 'Basic.lean', source: 'project' }]);
  assert.strictEqual(prScanner.declarations.get('tprod').name, 'PiTensorProduct.tprod', '`tprod` is the def, not `lift.tprod`');
  prScanner.reset();

  // Binder misreadings: `ext` alone on a line, the lemma `MultilinearMap.ext`, names inside a
  // `fun` binder's type, a parenthesised term inside a hypothesis' type.
  assert.strictEqual(bc.findUntypedBinder('simp', 'theorem foo : x = y := by\n  ext\n  simp [bar]'), null);
  assert.strictEqual(bc.findUntypedBinder('reindex_tprod', 'theorem foo : x = y :=\n  MultilinearMap.ext <| reindex_tprod e'), null);
  const funTyped = 'def foo : X :=\n  liftAddHom (fun p : R × Π i, s i ↦ σ p.1 • φ p.2)';
  assert.strictEqual(bc.findUntypedBinder('R', funTyped), null);
  assert.strictEqual(bc.findUntypedBinder('s', funTyped), null);
  assert(bc.findUntypedBinder('p', funTyped), 'the `fun` binder itself');
  assert.strictEqual(bc.findUntypedBinder('tprod', 'theorem ext {φ₁ φ₂ : M}\n    (H : φ₁.compMultilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂ := by'), null);
  assert(bc.findUntypedBinder('i', 'def foo (f : X) : ⨂[R] i, s i := tprod R f'), '`⨂[R] i,` binds `i`');
  // Names a body uses free (a definition takes the section variables among them).
  const free = (t) => [...bc.freeNamesInText(t)];
  assert(!free('fun t ↦ t + 1').includes('t'));
  assert(!free('  invFun t := t\n  right_inv t := rfl').includes('t'));
  assert(!free('(subsingletonEquiv (s := fun _ ↦ M) i₀).symm x').includes('s'));
  assert(free('fun x i ↦ f i (x i)').includes('f') && !free('e.symm i').includes('symm'));

  // Binder types from their use: `i` in `∀ i, AddCommMonoid (s i)` is `i : ι`.
  const varText = 'variable {s : ι → Type*} [∀ i, AddCommMonoid (s i)]';
  const iInfo = bc.localVariableInfo('i', varText);
  assert(iInfo && iInfo.inferNeeded && iInfo.inferNeeded.use, 'an untyped `∀` binder waits on its use');
  asyncChecks.push(bc.inferPending(iInfo.inferNeeded, varText, null, async (n) => (n === 's' ? 'ι → Type u_8' : null))
    .then(r => assert.strictEqual(r.typeSignature, 'i : ι')));
  const fUse = 'theorem foo (x : Π i, s i) : tprod R fun i ↦ f i (x i) = 0 := by';
  asyncChecks.push(bc.inferPending(bc.localVariableInfo('i', fUse).inferNeeded, fUse, null,
    async (n) => ({ f: 'Π i, s i →ₛₗ[σ₁₂] t i', s: 'ι → Type u_13' })[n] || null).then(r => assert.strictEqual(r.typeSignature, 'i : ι', '`f i` with `f : Π i, …`')));
  const eUse = 'theorem foo (e : ι ≃ ι₂) : tprod R fun i ↦ f (e.symm i) = 0 := by';
  asyncChecks.push(bc.inferPending(bc.localVariableInfo('i', eUse).inferNeeded, eUse, null, async () => null)
    .then(r => assert.strictEqual(r.typeSignature, 'i : ι₂', '`e.symm i` with `e : ι ≃ ι₂`')));

  // `:= .ofLinearMap …`: the declared type's namespace.
  const before = 'noncomputable def congr (f : Π i, s i ≃ₛₗ[σ₁₂] t i) :\n    (⨂[R] i, s i) ≃ₛₗ[σ₁₂] ⨂[R₂] i, t i :=\n  ';
  assert.strictEqual(bc.typeHead(bc.declaredTypeBefore(before), null), 'LinearEquiv');
  // A structure field's name and arguments aren't a term.
  const fieldLine = bc.joinStatement(['def lift : A ≃ₗ[S] B where', '  left_inv φ := by', '    simp'], 1);
  assert.strictEqual(bc.termAtOffset(fieldLine.text, fieldLine.lineStart + 10), null, '`left_inv φ :=`');

  // Gap hovers with Mathlib's signatures (universe parameters solved like other variables).
  const SIGS = {
    CommSemiring: '(R : Type u) : Type u',
    DecidableEq: '(α : Sort u) : Sort (max 1 u)',
    Module: '(R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] : Type (max u v)',
    AddCommMonoid: '(M : Type u) : Type u',
    PiTensorProduct: '{ι : Type u_1} (R : Type u_2) [CommSemiring R] (s : ι → Type u_3) [(i : ι) → AddCommMonoid (s i)] [(i : ι) → Module R (s i)] : Type (max (max u_1 u_2) u_3)',
    'Function.update': '{α : Sort u} {β : α → Sort v} [DecidableEq α] (f : (a : α) → β a) (a\' : α) (v : β a\') (a : α) : β a',
    'PiTensorProduct.tprod': '{ι : Type u_1} (R : Type u_2) [CommSemiring R] {s : ι → Type u_3} [(i : ι) → AddCommMonoid (s i)] [(i : ι) → Module R (s i)] : MultilinearMap R s (⨂[R] (i : ι), s i)',
    'LinearEquiv.symm': '{R : Type u_1} {S : Type u_6} {M : Type u_8} {M₂ : Type u_10} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid M₂] {module_M : Module R M} {module_S_M₂ : Module S M₂} {σ : R →+* S} {σ\' : S →+* R} {re₁ : RingHomInvPair σ σ\'} {re₂ : RingHomInvPair σ\' σ} (e : M ≃ₛₗ[σ] M₂) : M₂ ≃ₛₗ[σ\'] M',
    map: '{ι : Type u_1} {R : Type u_4} [CommSemiring R] {R₂ : Type u_7} [CommSemiring R₂] {σ₁₂ : R →+* R₂} {s : ι → Type u_13} {t : ι → Type u_14} [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)] [∀ i, AddCommMonoid (t i)] [∀ i, Module R₂ (t i)] (f : Π i, s i →ₛₗ[σ₁₂] t i) : (⨂[R] i, s i) →ₛₗ[σ₁₂] ⨂[R₂] i, t i',
    reindex: '{ι : Type u_1} {ι₂ : Type u_2} (R : Type u_4) [CommSemiring R] (s : ι → Type u_8) [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)] (e : ι ≃ ι₂) : (⨂[R] i : ι, s i) ≃ₗ[R] ⨂[R] i : ι₂, s (e.symm i)'
  };
  SIGS.update = SIGS['Function.update']; // `open Function`
  SIGS.tprod = SIGS['PiTensorProduct.tprod'];
  const VARS = { 'ι': 'Type u_1', 'ι₂': 'Type u_2', R: 'Type u_4', 'R₂': 'Type u_7', s: 'ι → Type u_8', M: 'Type u_9', 'σ₁₂': 'R →+* R₂', t: 'ι → Type u_14',
    f: 'Π i, s i →ₛₗ[σ₁₂] t i', e: 'ι ≃ ι₂' };
  const gap2 = async (code, marker, vars = VARS) => {
    const lines = code.split('\n');
    const line = lines[lines.length - 1];
    const off = line.indexOf(marker.replace('|', '')) + marker.indexOf('|');
    const j = bc.joinStatement(lines, lines.length - 1);
    const hit = bc.termAtOffset(j.text, j.lineStart + off);
    if (!hit) return null;
    const coerced = new Map(), binders = new Map();
    const type = await bc.termTypeOf(hit.node, hit.src, code, async (n) => SIGS[n] || null,
      { parent: hit.parent, path: hit.path, expected: hit.expected, variableOf: async (n) => vars[n] || null, coerced, binders });
    return type ? `${bc.termDisplay(hit.node, code, coerced, binders)} : ${type}` : null;
  };
  const T = (body) => `theorem probe : True := by\n  have := ${body}`;
  const gapCases = [
    // Lean: `CommSemiring R : Type u_4`, `DecidableEq ι : Type u_1`, `Module R M : Type (max u_4 u_9)`.
    ['variable {R S : Type*} [CommSemiring R] [CommSemiring S]', 'CommSemiring| R', 'CommSemiring R : Type u_4'],
    [T('DecidableEq ι'), 'DecidableEq| ι', 'DecidableEq ι : Type u_1'],
    [T('Module R M'), 'Module| R', 'Module R M : Type (max u_4 u_9)'],
    // Lean keeps the shape of a constant's level: `Type (max (max u_1 u_4) u_8)`.
    [T('PiTensorProduct R s'), 'PiTensorProduct| R', 'PiTensorProduct R s : Type (max (max u_1 u_4) u_8)'],
    // A pi type into types is a type: `Type (max u_1 u_8)`, printed `(i : ι) → …`.
    ['variable {s : ι → Type*} [∀ i, AddCommMonoid (s i)]', '|∀ i', '(i : ι) → AddCommMonoid (s i) : Type (max u_1 u_8)'],
    [T('update x i m'), 'update| x', 'update x i m : (a : ι) → s a', Object.assign({}, VARS, { x: 'Π i, s i', i: 'ι', m: 's i' })],
    // `?β a` against `s a →ₛₗ[σ₁₂] t a` (a higher-order pattern).
    [T('update f i u'), 'update| f', 'update f i u : (a : ι) → s a →ₛₗ[σ₁₂] t a', Object.assign({}, VARS, { i: 'ι', u: 's i →ₛₗ[σ₁₂] t i' })],
    // Semilinear notation unifies (`σ₁₂ : R →+* R₂` fixes `R`, `R₂`); `⨂` binders get their types.
    [T('map f'), 'map| f', 'map f : (⨂[R] (i : ι), s i) →ₛₗ[σ₁₂] ⨂[R₂] (i : ι), t i'],
    // `≃ₗ[R]` is `≃ₛₗ[RingHom.id R]`, whose inverse pair is the identity again.
    [T('(reindex R s e).symm'), 's e)|.symm', '(reindex R s e).symm : (⨂[R] (i : ι₂), s (e.symm i)) ≃ₗ[R] ⨂[R] (i : ι), s i'],
    // A bundled map applied to a point: `(tprod R) x`, typed from the point.
    [T('tprod R x'), 'tprod| R', '(tprod R) x : ⨂[R] (i : ι), s i', Object.assign({}, VARS, { x: 'Π i, s i' })]
  ];
  for (const [code, marker, want, vars] of gapCases) {
    asyncChecks.push(gap2(code, marker, vars).then(got => assert.strictEqual(got, want, `gap hover at ${marker}`)));
  }
  // Out-params found by instance search, from the instances in scope.
  const symm = bc.residualSignature(SIGS['LinearEquiv.symm'], [], {}, '', { receiver: { term: '(e i)', type: 's i ≃ₛₗ[σ₁₂] t i', binders: [] },
    instances: ['RingHomInvPair σ₁₂ σ₂₁', 'RingHomInvPair σ₂₁ σ₁₂'] });
  assert.strictEqual(bc.displayType(symm, ''), 't i ≃ₛₗ[σ₂₁] s i', '`(e i).symm` finds `σ₂₁` from `[RingHomInvPair σ₁₂ σ₂₁]`');
  // Levels as Lean prints them.
  const sort = (t) => bc.displayType(t, '');
  assert.strictEqual(sort('Sort (max 1 (u_1 + 1))'), 'Type u_1');
  assert.strictEqual(sort('Type (max u_4 (max u_1 u_8))'), 'Type (max u_4 u_1 u_8)', 'right-nested `max` prints flat');
  assert.strictEqual(sort('Type (max (max u_1 u_4) u_8)'), 'Type (max (max u_1 u_4) u_8)', 'left-nested stays');
  assert.strictEqual(sort('Sort 0'), 'Prop');
}
console.log("   ✓ PR 45819 cases verified.\n");

// 21. seewoo5/DifferentProofs (closed PRs): Verso blueprint chapters, structure fields, unused
//     instances, and words that are also Object's properties. Expected signatures are Lean's
//     hovers on the project's own files (lean-lsp).
console.log("21. Testing cases from sweeping DifferentProofs PRs...");
{
  const PR = context.LeanPRScanner, bc = context.VersoBinderContext;
  // A Verso document is prose from `#doc` on, except its ```lean blocks.
  const chapter = ['import VersoManual', 'open Verso.Genre Manual', '', '#doc (Manual) "Tiling a Rectangle" =>', '',
    'theorem of Wagon: a tiling by rectangles with an integer side', '```lean', 'example : 1 = 1 := rfl', '```',
    ':::theorem "thm:x" (lean := "IntegerRectangleTheorem, IntegerRectangle.intWidth_of_forall")', ':::'].join('\n');
  assert.deepStrictEqual(JSON.parse(JSON.stringify(PR.versoRegions(chapter))), { docLine: 4, fences: [[7, 9]] });
  assert.deepStrictEqual(JSON.parse(JSON.stringify(PR.versoRegions('theorem foo : True := trivial'))), { docLine: 0, fences: [] });
  assert.strictEqual(PR.scanSource(chapter, 'Chapter.lean').length, 0, 'nothing is declared in prose');

  // Structure fields are projections: `S.f {params} (self : S params) : T`. The section
  // variables a structure doesn't use (`[Fintype ι]`) are left out, as by a `def`.
  const links = [
    'namespace IntegerRectangle', '', 'structure Rectangle where', '  /-- Left edge. -/', '  x₀ : ℝ', '  /-- Right edge. -/', '  x₁ : ℝ', '',
    'variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}', '',
    'def Blocked (T : ι → Rectangle) (c y : ℝ) : Prop :=', '  ∃ i, (T i).x₀ < c ∧ c < (T i).x₁', '',
    'structure Link (R : Rectangle) (T : ι → Rectangle) where', '  /-- The abscissa of the link. -/', '  c : ℝ', '  lo : ℝ', '  hi : ℝ',
    '  lo_lt_hi : lo < hi', '  free : ∀ y, lo < y → y < hi → ¬ Blocked T c y', '',
    'noncomputable def area (T : ι → Rectangle) : ℝ := ∑ i, ((T i).x₁ - (T i).x₀)', '',
    'variable [Nonempty ι]', '', 'def some (T : ι → Rectangle) : Rectangle := T (Classical.arbitrary ι)',
    'def someEdge (T : ι → Rectangle) : ℝ := (some T).x₀', '', 'end IntegerRectangle'].join('\n');
  const sig = (name) => { const d = PR.scanSource(links, 'Defs.lean').find(x => x.name === name); return d && d.typeSignature; };
  assert.strictEqual(sig('IntegerRectangle.Rectangle'), 'IntegerRectangle.Rectangle : Type');
  assert.strictEqual(sig('IntegerRectangle.Rectangle.x₀'), 'IntegerRectangle.Rectangle.x₀ (self : Rectangle) : ℝ');
  assert.strictEqual(PR.scanSource(links, 'Defs.lean').find(x => x.name === 'IntegerRectangle.Rectangle.x₀').docstring, 'Left edge.');
  assert.strictEqual(sig('IntegerRectangle.Blocked'), 'IntegerRectangle.Blocked {ι : Type} (T : ι → Rectangle) (c y : ℝ) : Prop', 'no unused `[Fintype ι]`');
  assert.strictEqual(sig('IntegerRectangle.Link'), 'IntegerRectangle.Link {ι : Type} (R : Rectangle) (T : ι → Rectangle) : Type', "the structure's own `R`, `T` shadow the variables");
  assert.strictEqual(sig('IntegerRectangle.Link.c'), 'IntegerRectangle.Link.c {ι : Type} {R : Rectangle} {T : ι → Rectangle} (self : Link R T) : ℝ');
  assert.strictEqual(sig('IntegerRectangle.Link.lo_lt_hi'), 'IntegerRectangle.Link.lo_lt_hi {ι : Type} {R : Rectangle} {T : ι → Rectangle} (self : Link R T) : self.lo < self.hi');
  assert.strictEqual(sig('IntegerRectangle.Link.free'),
    'IntegerRectangle.Link.free {ι : Type} {R : Rectangle} {T : ι → Rectangle} (self : Link R T) (y : ℝ) : self.lo < y → y < self.hi → ¬Blocked T self.c y',
    '`y` has the type of `lo`, the other side of `<`; a leading `∀` is a parameter');
  assert.strictEqual(sig('IntegerRectangle.area'), 'IntegerRectangle.area {ι : Type} [Fintype ι] (T : ι → Rectangle) : ℝ', '`∑ i, …` uses `[Fintype ι]`');
  assert.strictEqual(sig('IntegerRectangle.some'), 'IntegerRectangle.some {ι : Type} [Nonempty ι] (T : ι → Rectangle) : Rectangle');
  assert.strictEqual(sig('IntegerRectangle.someEdge'), 'IntegerRectangle.someEdge {ι : Type} [Nonempty ι] (T : ι → Rectangle) : ℝ', 'through `some`, which takes it');
  // `Prop where` on its own (indented) line.
  const strip = ['structure Strip (R : Rectangle) (a b : ℝ) :', '    Prop where', '  /-- Inside `R`. -/', '  mem : ∀ y, a < y → y ≤ b → R.x₀ ≤ y'].join('\n');
  assert.strictEqual(PR.scanSource(strip, 'S.lean').pop().typeSignature, 'Strip.mem {R : Rectangle} {a b : ℝ} (self : Strip R a b) (y : ℝ) : a < y → y ≤ b → R.x₀ ≤ y');
  // A constant without parameters types its arguments (Lean: `a_ge_two (n : ℕ) : 2 ≤ a n`).
  assert.strictEqual(PR.scanSource('def a : ℕ → ℕ\n  | 0 => 2\n  | n + 1 => a n + 1\nlemma a_ge_two : ∀ n, 2 ≤ a n := by\n  sorry', 'S.lean').pop().typeSignature, 'a_ge_two (n : ℕ) : 2 ≤ a n');
  // A theorem takes every instance on its variables.
  const withTheorem = links.replace('\nend IntegerRectangle', '\ntheorem t (T : ι → Rectangle) : T = T := rfl\nend IntegerRectangle');
  assert.strictEqual(PR.scanSource(withTheorem, 'Defs.lean').pop().typeSignature,
    'IntegerRectangle.t {ι : Type} [Fintype ι] [Nonempty ι] (T : ι → Rectangle) : T = T');
  // Lean's signature printer: leading named `∀`s are parameters, same-kind same-type binders one
  // group, a name bound twice `n✝` (checked against Lean's hovers on probes).
  const sigCases = [
    ['(lo hi : ℝ) : ∀ y, lo < y → y < hi', 'foo (lo hi y : ℝ) : lo < y → y < hi'],
    ['(a : ℕ) (b : ℕ) : a + b = b + a', 'foo (a b : ℕ) : a + b = b + a'],
    ['(s : Set ℕ) : ∀ t : Set ℕ, t ⊆ s → t ⊆ s', 'foo (s t : Set ℕ) : t ⊆ s → t ⊆ s'],
    ['(s : Finset ℕ) : ∀ x ∈ s, x ∈ s', 'foo (s : Finset ℕ) (x : ℕ) : x ∈ s → x ∈ s'],
    ['(n : ℕ) : ∀ n : ℕ, n = n', 'foo (n n✝ : ℕ) : n✝ = n✝'],
    [': ∀ (a : ℕ) {b : ℕ}, a + b = b + a', 'foo (a : ℕ) {b : ℕ} : a + b = b + a'],
    [': ∀ {k l n : ℕ}, P k n → P l n → k = l', 'foo {k l n : ℕ} : P k n → P l n → k = l'],
    ['{T : ι → R} : ∀ i, (T i).Nondegenerate', 'foo {T : ι → R} (i : ι) : (T i).Nondegenerate'],
    // An unknown binder type stays in the type; so does a non-dependent arrow.
    [': ∀ n, 0 < n → Nat.Prime n', 'foo : ∀ n, 0 < n → Nat.Prime n'],
    // `∃` binders print without types (Lean: `harmonic_unbounded (M : ℝ) : ∃ n, …`).
    [': ∀ M : ℕ, ∃ n : ℕ, n > M', 'foo (M : ℕ) : ∃ n, n > M'],
    // Ascriptions as elaborated (Lean: `(hmem : (x, y) ∈ …)`); a numeral's stays.
    ['{x y : ℝ} (n : ℕ) (hmem : ((x, y) : ℝ × ℝ) ∈ S) (h : (n : ℝ) < x) : (2 : ℝ) ≤ x', 'foo {x y : ℝ} (n : ℕ) (hmem : (x, y) ∈ S) (h : ↑n < x) : (2 : ℝ) ≤ x'],
    ['(s : Set ℕ) : ∃ x ∈ s, ∃ (y : ℕ), x < y', 'foo (s : Set ℕ) : ∃ x ∈ s, ∃ y, x < y'],
    ['{T : ι → R} (hT : P T) : ∀ i, (T i).x₀ = 0 → Q (some i, true)', 'foo {T : ι → R} (hT : P T) (i : ι) : (T i).x₀ = 0 → Q (some i, true)'],
    ['(f : ℕ → ℕ) : ℕ → ℕ', 'foo (f : ℕ → ℕ) : ℕ → ℕ'],
    ['[Fintype ι] [DecidableEq ι] (a : ι) : a = a', 'foo [Fintype ι] [DecidableEq ι] (a : ι) : a = a']
  ];
  for (const [s, want] of sigCases) assert.strictEqual(bc.leanSignature('foo', s), want, s);
  // `∀ t ∈ S p` with a file's `S (p : ℕ) : Finset (ℕ × ℕ × ℕ)` (Lean: `(t : ℕ × ℕ × ℕ) : t ∈ S p → …`).
  const zagier = ['def S (p : ℕ) : Finset (ℕ × ℕ × ℕ) := ∅', 'def invol (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := t',
    'lemma invol_mem {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) : ∀ t ∈ S p, invol t ∈ S p := by', '  sorry'].join('\n');
  assert.strictEqual(PR.scanSource(zagier, 'Zagier.lean').pop().typeSignature,
    'invol_mem {p : ℕ} (hp : Nat.Prime p) (hp4 : p % 4 = 1) (t : ℕ × ℕ × ℕ) : t ∈ S p → invol t ∈ S p', 'and `@[pp_nodot]` `Nat.Prime`, as Lean prints it');
  assert.strictEqual(bc.leanSignature('foo', '(x : ℝ) (n : ℕ) : x.exp ≠ 0 ∧ ¬n.Prime ∧ (n.log 2 = 0)'),
    'foo (x : ℝ) (n : ℕ) : Real.exp x ≠ 0 ∧ ¬Nat.Prime n ∧ n.log 2 = 0', 'an applied `n.log 2` keeps its dot');

  // Scoped notations by the file's opens (Lean's hovers: `cexp` is `Complex.exp (z : ℂ) : ℂ`
  // with `open Complex`, `I` is `unitInterval : Set ℝ` with `open unitInterval`).
  const scopedFile = ['open Complex', 'open scoped unitInterval', 'theorem foo : cexp 0 = 1 := by', '  sorry',
    'namespace PowerSeries', 'theorem bar (x : I) : d⁄dX = d⁄dX := rfl', 'end PowerSeries', 'theorem baz : I = I := rfl'].join('\n');
  const target = (tok, line) => { const t = context.notationTarget(tok, scopedFile, line); return t && t[0]; };
  assert.strictEqual(target('cexp', 3), 'Complex.exp');
  assert.strictEqual(target('rexp', 3), null, 'no `open Real`');
  assert.strictEqual(target('I', 6), 'unitInterval', '`open scoped` brings notation');
  assert.strictEqual(target('d⁄dX', 6), 'PowerSeries.derivative', 'in its own namespace');
  assert.strictEqual(target('d⁄dX', 8), null, 'outside it');
  // Several notations for one token: the latest `open` decides (`π`: `Real.pi` with `open Real`).
  assert.strictEqual(context.notationTarget('π', 'open Nat.Prime\nopen Real\ntheorem t : π = π := rfl', 3)[0], 'Real.pi');
  assert.strictEqual(context.notationTarget('π', 'open Real\nopen Nat.Prime\ntheorem t : π = π := rfl', 3)[0], 'Nat.primeCounting');
  assert.strictEqual(tokenizer.extractTokenFromLine('  ∀ x : ℝ≥0∞, x ≤ ∞', 9).token, 'ℝ≥0∞', 'the longest notation');
  assert.strictEqual(tokenizer.extractTokenFromLine('  Tendsto f (𝓝 x) l', 14).token, '𝓝', 'a notation outside the BMP');
  assert(!JSON.stringify(context.scopeAt(scopedFile, 3)).includes('unitInterval'), '`open scoped` still brings no names');
  const dTok = tokenizer.extractTokenFromLine('  (d⁄dX ℤ g * x)', 5);
  assert.strictEqual(dTok && dTok.token, 'd⁄dX', '`d⁄dX` is one token');
  assert.strictEqual(tokenizer.extractTokenFromLine('  (d⁄dX ℤ g * x)', 10).token, 'g');

  // Field notation on a set-builder or an ascription: `hfin : {p : ℕ | p.Prime}.Finite` gives
  // `hfin.toFinset` = `Set.Finite.toFinset`.
  assert.strictEqual(bc.typeHead('{p : ℕ | p.Prime}.Finite', null), 'Set.Finite');
  assert.strictEqual(bc.typeHead('(S : Set ℕ).Finite', null), 'Set.Finite');
  assert.strictEqual(bc.typeHead('((cantorNF b o).map Prod.fst).SortedGT', null), 'SortedGT', 'untyped term: the field alone');

  // Subtype binders: `{d // corner T d = p}` binds `d` (its type from its use).
  const sub = 'theorem foo (T : ι → R) (p : ℤ × ℤ) : Nat.card {d // corner T d = p} = Nat.card {i : ι // H i} := by';
  assert.strictEqual(JSON.stringify(bc.localVariableInfo('d', sub).inferNeeded.use), '{"fn":"corner","k":1}');
  assert.strictEqual(bc.localVariableInfo('i', sub).typeSignature, 'i : ι');
  // A trailing `fun` argument with more to follow (Lean: `(f fun i ↦ g i + 1) = f fun i ↦ g i`).
  assert.strictEqual(bc.leanSignature('foo', '(f : (ℕ → ℕ) → ℕ) : f (fun i => g i + 1) = f fun i => g i'), 'foo (f : (ℕ → ℕ) → ℕ) : (f fun i => g i + 1) = f fun i => g i');
  // A dependent arrow inside `×` keeps its parentheses; a binder's type keeps its own binders.
  assert.strictEqual(bc.leanSignature('foo', '{s : ι → Type*} (p : FreeAddMonoid (R × ((i : ι) → s i))) : ∀ f : Π i, s i, φ (0, f) = 0'),
    'foo {s : ι → Type*} (p : FreeAddMonoid (R × ((i : ι) → s i))) (f : (i : ι) → s i) : φ (0, f) = 0');
  // Notation with its parenthesis right after a name stays as written.
  assert.strictEqual(bc.leanSignature('fourier', '{T : ℝ} (n : ℤ) : C(AddCircle T, ℂ)'), 'fourier {T : ℝ} (n : ℤ) : C(AddCircle T, ℂ)');
  assert.strictEqual(bc.leanSignature('foo', '(γ : SL(2, ℤ)) : f (a, b) = 0'), 'foo (γ : SL(2, ℤ)) : f (a, b) = 0');
  // `intro` on `Injective (fun g ↦ …)` (Lean: `h : (fun g ↦ f g + 1) a = (fun g ↦ f g + 1) b`).
  const inj = 'example (f : ℕ → ℕ) : Function.Injective (fun g : ℕ => f g + 1) := by\n  intro a b h';
  assert.strictEqual(bc.localVariableInfo('h', inj).typeSignature, 'h : (fun g : ℕ => f g + 1) a = (fun g : ℕ => f g + 1) b');

  // Tactic names that are also Object's properties (`constructor`) are tactics, not `Object`.
  const tdocs2 = context.parseTacticDocs('<div id="Lean.Parser.Tactic.constructor"><div id="userName-constructor"><h2>constructor</h2>' +
    '<p>applies the first matching constructor</p><dl></dl></div></div>');
  assert.strictEqual(typeof tdocs2.constructor, 'object', '`constructor` is parsed');
  assert(tdocs2.constructor.doc.includes('first matching constructor'));
  assert.strictEqual(context.VersoBuiltins.get('toString'), null, 'no builtin from Object.prototype');

  // The content script: `constructor` is looked up as itself; Verso prose has no hovers.
  const cctx = {
    console, setTimeout, clearTimeout, location: { pathname: '/seewoo5/DifferentProofs/pull/40/changes' },
    document: { addEventListener: () => {}, getElementById: () => null, querySelectorAll: () => [], body: {} },
    Node: { ELEMENT_NODE: 1, TEXT_NODE: 3 }, MutationObserver: function () { this.observe = () => {}; },
    chrome: { runtime: { sendMessage: () => {}, onMessage: { addListener: () => {} }, lastError: null }, storage: { local: { get: (k, cb) => cb({}), set: () => {} } } }
  };
  cctx.window = cctx; cctx.self = cctx; cctx.addEventListener = () => {};
  vm.createContext(cctx);
  for (const f of ['content/builtins_db.js', 'content/lean_tokenizer.js', 'content/lean_terms.js', 'content/binder_context.js', 'content/term_hover.js', 'content/pr_scanner.js', 'content/content.js']) {
    vm.runInContext(fs.readFileSync(path.join(__dirname, '..', f), 'utf8'), cctx);
  }
  const CI = cctx.VersoContentInternals, cbc = cctx.VersoBinderContext;
  // The keyword a declaration starts with shows `#where`; other keywords and words don't.
  assert(CI.isDeclKeyword({ token: 'theorem', linePrefix: '' }));
  assert(CI.isDeclKeyword({ token: 'lemma', linePrefix: '@[simp] private ' }));
  assert(CI.isDeclKeyword({ token: 'theorem', linePrefix: 'open Real in ' }));
  assert(!CI.isDeclKeyword({ token: 'def', linePrefix: '  exact foo ' }), 'not after other code');
  assert(!CI.isDeclKeyword({ token: 'have', linePrefix: '  ' }));
  // Stepping with the card fixed: the tactic stepped to scrolls out from under it (900 high).
  const line = (top, left = 100) => ({ top, bottom: top + 20, left, right: left + 200 });
  const cardTop = { top: 40, bottom: 400, left: 50, right: 510 };
  assert.strictEqual(CI.scrollBeside(line(500), cardTop, 900), 0, 'in view below the card');
  assert.strictEqual(CI.scrollBeside(line(300), cardTop, 900), -340, 'under the card: to the middle of the room below it');
  assert.strictEqual(CI.scrollBeside(line(1000), cardTop, 900), 360, 'off the screen');
  assert.strictEqual(CI.scrollBeside(line(300, 600), cardTop, 900), 0, 'beside the card, not under it');
  const cardLow = { top: 500, bottom: 860, left: 50, right: 510 };
  assert.strictEqual(CI.scrollBeside(line(520), cardLow, 900), 280, 'to the room above it, the nearer');
  assert.strictEqual(CI.scrollBeside(line(30, 600), cardTop, 900, 100), -460, 'under a sticky header');
  const wc = CI.whereCard({ where: 'namespace A  -- line 3', decl: { kind: 'theorem', name: 'b', fullName: 'A.b', line: 5 }, isNew: true,
    similar: [{ name: "b'", line: 9, score: 1 }, { name: 'c', line: 12, score: 0.6 }], hints: [{ kind: 'far', line: 9, text: 'Most like `b\'` at line 9: it may belong next to it.' }] },
  { path: 'A.lean', line: 5 });
  assert.strictEqual(wc.name, 'A.b');
  assert.strictEqual(wc.typeSignature, 'namespace A  -- line 3');
  assert(wc.docstring.startsWith('**Placement**') && wc.docstring.includes('Similar in this file: `c` (line 12).') && !wc.docstring.includes("`b'` (line 9)."), wc.docstring);
  cbc.contextFromDom = () => 'theorem foo : P ∧ Q := by\n  constructor';
  const lc = CI.lookupContext({ token: 'constructor', subToken: 'constructor', chainUpToCursor: 'constructor', linePrefix: '  ', lineSuffix: '', textNode: {} });
  assert.strictEqual(lc.queryToken, 'constructor', 'not `NOTATION_ALIASES.constructor`');
  // `exact .inl h` in a proof is `Or.inl`.
  assert.strictEqual(CI.lookupContext({ token: 'inl', subToken: 'inl', chainUpToCursor: 'inl', linePrefix: '  · exact .', lineSuffix: ' h', textNode: {} }).queryToken, 'Or.inl');
  // Below `#doc`, a word is prose, a name in `(lean := "…")` a declaration; read from the file.
  let asked = 0;
  cctx.chrome.runtime.sendMessage = (msg, cb) => { if (msg.action === 'VERSO_REGIONS') { asked++; cb(cctx.LeanPRScanner.versoRegions(chapter)); } else cb(null); };
  cbc.versoAbove = () => null;
  const at = (line, linePrefix) => { cbc.fileRefFromDom = () => ({ owner: 'o', repo: 'r', sha: 's', side: 'right', path: 'Chapter.lean', line }); return CI.versoState({ textNode: {}, linePrefix }); };
  const first = at(6, 'theorem of ');
  assert(first && typeof first.then === 'function', 'the first hover waits for the file');
  asyncChecks.push(first.then((state) => {
    assert.strictEqual(state, 'prose');
    assert.strictEqual(at(6, 'theorem of '), 'prose', 'then known at once');
    assert.strictEqual(at(4, '#'), 'prose', 'the `#doc` line itself');
    assert.strictEqual(at(2, 'open '), null, 'Lean code before `#doc`');
    assert.strictEqual(at(8, 'example : '), null, 'a ```lean block');
    assert.strictEqual(at(10, ':::theorem "thm:x" (lean := "IntegerRectangleTheorem, '), 'name');
    assert.strictEqual(asked, 1, 'the file is read once');
    // A `#doc` line in view settles it without the file.
    cbc.versoAbove = () => 'prose';
    cbc.fileRefFromDom = () => null;
    assert.strictEqual(CI.versoState({ textNode: {}, linePrefix: 'The first ' }), 'prose');
  }));
}
console.log("   ✓ DifferentProofs cases verified.\n");

// 22. Real Lean, from the local helper. SubVerso's output for test/fixtures/Sample.lean (made by
//     running Lean on it) becomes the data the extension reads; the worker and the page use it.
console.log("22. Testing real Lean data (the local helper)...");
{
  const { pathToFileURL } = require('url');
  const os = require('os');
  const sampleSource = fs.readFileSync(path.join(__dirname, 'fixtures/Sample.lean'), 'utf8');
  const sampleModule = JSON.parse(fs.readFileSync(path.join(__dirname, 'fixtures/Sample.subverso.json'), 'utf8'));
  const srcLines = sampleSource.split('\n');
  /** Column (UTF-16, as the browser counts) of the `nth` occurrence of `word` on a 1-based line. */
  const col = (line, word, nth = 0) => {
    let i = -1;
    for (let k = 0; k <= nth; k++) i = srcLines[line - 1].indexOf(word, i + 1);
    assert(i >= 0, `"${word}" is on line ${line}`);
    return i;
  };
  const tick = (ms = 0) => new Promise((resolve) => setTimeout(resolve, ms));
  loadScript('background/exact_data.js');
  const exact = context.LeanLensExact;

  asyncChecks.push((async () => {
    const helperDir = path.join(__dirname, '..', 'helper');
    const { convertModule, DATA_FORMAT_VERSION } = await import(pathToFileURL(path.join(helperDir, 'convert.mjs')).href);
    const helper = await import(pathToFileURL(path.join(helperDir, 'lean-lens-helper.mjs')).href);
    const { spawnSync } = require('child_process');

    // --- The converter: Lean's hovers, proof states and messages, by line and column.
    const data = Object.assign(convertModule(sampleModule, sampleSource), { lean: 'leanprover/lean4:v4.35.0' });
    assert.strictEqual(data.version, DATA_FORMAT_VERSION);
    assert.strictEqual(exact.FORMAT_VERSION, DATA_FORMAT_VERSION, 'the extension reads the format the helper writes');
    const at = (line, word, nth = 0, caretIn = 0) => {
      const c = col(line, word, nth);
      return exact.describe(data, line, c, c + word.length, c + caretIn);
    };
    // A constant: Lean's signature and docstring.
    const dbl = at(4, 'double', 1);
    assert.strictEqual(dbl.token.kind, 'const');
    assert.strictEqual(dbl.token.name, 'double');
    assert.strictEqual(dbl.token.typeSignature, 'double (n : Nat) : Nat');
    assert.strictEqual(dbl.token.docstring, 'Doubles a number.');
    assert.strictEqual(dbl.goals, null, 'a statement is not in a proof');
    assert.strictEqual(dbl.lean, 'leanprover/lean4:v4.35.0');
    // A variable and a numeral: their types.
    assert.strictEqual(at(4, 'n', 0).token.typeSignature, 'n : Nat');
    assert.strictEqual(at(4, 'n', 0).token.kind, 'variable');
    assert.strictEqual(at(4, '2').token.typeSignature, '2 : Nat');
    // The pointer at a token's right edge still means that token.
    assert.strictEqual(at(5, 'double', 0, 6).token.name, 'double');
    // A tactic: its docs, and the goals after it.
    const omega = at(6, 'omega');
    assert.strictEqual(omega.token.kind, 'tactic');
    assert(/omega/.test(omega.token.docstring), 'the tactic\'s docstring');
    assert.strictEqual(JSON.stringify(omega.goals.goals), '[]', 'no goals after `omega`');
    assert.strictEqual(omega.goals.at, false);
    const unfold = at(5, 'unfold');
    assert.strictEqual(unfold.goals.tactic, 'unfold double');
    assert.strictEqual(unfold.goals.goals.join('|'), 'n : Nat\n⊢ n + n = 2 * n');
    // `by`: the goal the proof starts from.
    const by4 = at(4, 'by');
    assert.strictEqual(by4.goals.at, true);
    assert.strictEqual(by4.goals.goals.join('|'), 'n : Nat\n⊢ double n = 2 * n');
    // Several goals; hypotheses of one type share a line, as in Lean's infoview.
    assert.strictEqual(at(14, 'constructor').goals.goals.join('|'),
      'case left\np q : Prop\nhp : p\nhq : q\n⊢ p|case right\np q : Prop\nhp : p\nhq : q\n⊢ q');
    // `have … := by`: SubVerso records the theorem's opening goal on that `by` (`⊢ p ∧ q`, where
    // Lean's goal is `⊢ q`). That state is dropped; the `have` shows the state after it.
    assert(!data.tactics.some((t) => t[0] === 16 && t[1] === col(16, 'by')), 'no state on the nested `by`');
    const nestedBy = at(16, 'by');
    assert.strictEqual(nestedBy.goals.tactic, "have hq' : q := by exact hq");
    assert.strictEqual(nestedBy.goals.goals.join('|'), "case right\np q : Prop\nhp : p\nhq hq' : q\n⊢ q");
    assert.strictEqual(at(16, 'exact').goals.goals.length, 0);
    // A case of `induction … with`: the goal it starts from; each `rw` rule: the goal after it.
    const succ = at(22, 'succ');
    assert.strictEqual(succ.goals.at, true);
    assert.strictEqual(succ.goals.goals.join('|'), 'case succ\nk : Nat\nih : 0 + k = k\n⊢ 0 + (k + 1) = k + 1');
    const rule = at(23, 'Nat.add_succ');
    assert(rule.token.typeSignature.startsWith('Nat.add_succ '), rule.token.typeSignature);
    assert.strictEqual(rule.goals.goals.join('|'), 'case succ\nk : Nat\nih : 0 + k = k\n⊢ (0 + k).succ = k + 1');
    const same = (a, b, m) => assert.strictEqual(JSON.stringify(a), JSON.stringify(b), m);
    // The goals before a tactic: after the one before it at the same level, or for a `rw` rule
    // the goals before its `rw`. The first tactic of a nested `have … := by` has none recorded.
    const lastLine = (goals) => goals && goals.map((g) => g.split('\n').pop());
    same(lastLine(at(5, 'unfold').goals.before), ['⊢ double n = 2 * n']);
    same(lastLine(at(6, 'omega').goals.before), ['⊢ n + n = 2 * n']);
    same(lastLine(at(11, 'rw').goals.before), ['⊢ a + b = b + a'], '`rw [h₁]` follows the `have`');
    assert.strictEqual(at(10, 'rw').goals.before, null, 'the first tactic of `have … := by` has no state before it');
    same(lastLine(at(23, 'Nat.add_succ').goals.before), ['⊢ 0 + (k + 1) = k + 1'], 'the first rule: before its `rw`');
    same(lastLine(at(23, 'ih').goals.before), ['⊢ (0 + k).succ = k + 1'], 'the next rule: after the one before');
    same(lastLine(at(14, 'constructor').goals.before), ['⊢ p ∧ q']);
    assert.strictEqual(at(4, 'by').goals.before, null, 'a `by` shows the state there, not a change');
    // Stepping through a proof: its tactics in the order they finish (a `have`'s proof before
    // the `have`, a `rw`'s rules before the `rw`), and where the hovered one is among them.
    const two = at(16, 'exact');
    assert.strictEqual(two.goals.steps, 8);
    assert.strictEqual(two.goals.step, 5);
    const steps = exact.stepsOfProof(data, two.goals.index);
    same(steps.map((st) => st.tactic), ['by', 'constructor', '·', 'exact hp', '·', 'exact hq', "have hq' : q := by exact hq", "exact hq'"]);
    same(steps[1].range, [14, 2, 14, 13]);
    assert.strictEqual(exact.stepsOfProof(data, at(6, 'omega').goals.index).length, 3, 'only the proof the tactic is in');
    same(exact.stepsOfProof(data, at(23, 'rw').goals.index).map((st) => st.tactic),
      ['by', '| zero =>', 'rfl', '| succ k ih =>', 'Nat.add_succ,', 'ih', 'rw [Nat.add_succ, ih]']);
    same(exact.stepsOfProof(data, at(11, 'rw').goals.index).map((st) => st.tactic),
      ['by', 'Nat.add_comm', 'rw [Nat.add_comm]', 'have h₁ : b + a = a + b := by …', 'h₁', 'rw [h₁]']);

    // What a tactic changed, as in Lean's infoview.
    const diff = context.LeanGoalDiff;
    const constructorDiff = diff.diffStates(at(14, 'constructor').goals.before, at(14, 'constructor').goals.goals);
    same(constructorDiff.after.map((v) => v.status), ['ins', 'ins'], 'goals with new case names are new');
    same(constructorDiff.before.map((v) => v.status), ['del'], 'the goal split up is gone');
    const haveDiff = diff.diffStates(at(16, 'have').goals.before, at(16, 'have').goals.goals);
    const hq = haveDiff.after[0].lines.find((l) => l.segments.map((x) => x.text).join('').startsWith('hq'));
    assert.strictEqual(hq.status, 'changed');
    same(hq.segments.filter((x) => x.changed).map((x) => x.text.trim()), ["hq'"], 'only the new name is marked');
    const unfoldDiff = diff.diffStates(at(5, 'unfold').goals.before, at(5, 'unfold').goals.goals);
    const target = unfoldDiff.after[0].lines[1];
    assert.strictEqual(target.status, 'changed');
    same(target.segments.filter((x) => x.changed).map((x) => x.text), ['n +'], 'the part of the target that changed (one `n` is shared)');
    same(unfoldDiff.before[0].lines[1].segments.filter((x) => x.changed).map((x) => x.text), ['double']);
    assert.strictEqual(unfoldDiff.after[0].lines[0].status, 'same', 'an unchanged hypothesis');
    const intro = diff.diffStates(['p q : Prop\n⊢ p → q'], ['p q : Prop\nhp : p\n⊢ q']);
    same(intro.after[0].lines.map((l) => l.status), ['same', 'ins', 'changed']);
    assert.strictEqual(diff.diffStates(['⊢ a'], ['⊢ a']).changed, false);
    // The tooltip: the goals after with what is new marked, and the goals before on request.
    const titleEl = { innerHTML: '' };
    const bodyEl = { innerHTML: '' };
    tooltipView.goalsSide = 'after';
    tooltipView.renderGoals(at(5, 'unfold').goals, { go() {} }, titleEl, bodyEl);
    assert(bodyEl.innerHTML.includes('<span class="verso-diff-ins">n +</span>'), bodyEl.innerHTML);
    assert(titleEl.innerHTML.includes('data-side="before"') && titleEl.innerHTML.includes('2/3'), titleEl.innerHTML);
    tooltipView.goalsSide = 'before';
    tooltipView.renderGoals(at(5, 'unfold').goals, null, titleEl, bodyEl);
    assert(bodyEl.innerHTML.includes('<span class="verso-diff-del">double</span>'), bodyEl.innerHTML);
    assert(!titleEl.innerHTML.includes('data-step'), 'no step buttons without a stepper');
    tooltipView.goalsSide = 'after';
    tooltipView.renderGoals(at(4, 'by').goals, null, titleEl, bodyEl);
    assert(!bodyEl.innerHTML.includes('verso-diff') && titleEl.innerHTML.startsWith('<span class="verso-goals-label">Goal at'), 'a `by`: the state alone');

    // Regions Lean records at a bracket: `simp_rw`'s `[` (named after its tactic) and the closing
    // `]` of a `rw` (named after the `rw` and not stepped through: it repeats the `rw`'s state).
    const bracket = {
      hovers: [{ k: 'doc', n: 'simp_rw', p: 'Mathlib.Tactic.tacticSimp_rw___' }, { k: 'doc', n: 'by', p: 'Lean.Parser.Term.byTactic' }],
      lines: { 1: [20, 22, 1], 2: [2, 9, 0] },
      strings: ['⊢ a', '⊢ b', 'by', '[', 'h', 'rw [h]', ']'],
      goals: [[0], [1]],
      tactics: [[1, 20, 1, 22, 1, [0], 2], [2, 10, 2, 11, 0, [0], 3], [2, 11, 2, 12, 0, [1], 4], [3, 2, 3, 8, 0, [1], 5], [3, 7, 3, 8, 0, [1], 6]]
    };
    assert.strictEqual(exact.tacticAt(bracket, 2, 10).tactic, 'simp_rw [');
    same(exact.stepsOfProof(bracket, 0).map((st) => st.tactic), ['by', 'simp_rw [', 'h', 'rw [h]']);
    const closing = exact.tacticAt(bracket, 3, 7);
    same([closing.tactic, closing.step, closing.steps], ['rw [h]', 3, 4], 'the `]` counts as its `rw`');
    // A `rw` and its rules, with `rfl` at the `]` doing nothing (lines 2, 3) or closing the goal
    // (line 4): `rw [h]` is its rule over again, so it stands for it; `rw [p, q]` repeats its
    // last rule, so it is left out; `rw [r]`'s `]` is a step of its own, named after the `rw`.
    const rws = {
      hovers: [], lines: {},
      strings: ['⊢ a', '⊢ b', '⊢ c', '⊢ d', '⊢ e', 'by', 'rw [h]', 'h', 'rw [p, q]', 'p', 'q', ']', 'rw [r]', 'r'],
      goals: [[0], [1], [2], [3], [4]],
      tactics: [[1, 15, 1, 17, 1, [0], 5], [2, 2, 2, 8, 0, [1], 6], [2, 6, 2, 7, 0, [1], 7],
        [3, 2, 3, 11, 0, [3], 8], [3, 6, 3, 7, 0, [2], 9], [3, 9, 3, 10, 0, [3], 10], [3, 10, 3, 11, 0, [3], 11],
        [4, 2, 4, 8, 0, [], 12], [4, 6, 4, 7, 0, [4], 13], [4, 7, 4, 8, 0, [], 11]]
    };
    const rwSteps = exact.stepsOfProof(rws, 0);
    same(rwSteps.map((st) => st.tactic), ['by', 'rw [h]', 'p', 'q', 'r', 'rw [r]']);
    same([rwSteps[5].before, rwSteps[5].goals], [['⊢ e'], []], 'what the `rfl` did');
    same([2, 3, 6, 7, 9].map((i) => { const t = rws.tactics[i]; return exact.tacticAt(rws, t[0], t[1]).step; }), [1, 3, 3, 5, 5],
      'each counts as the step showing its goals');

    // Read like a person would: one change for what replaced a term, shared terms kept whole.
    const differ2 = context.LeanGoalDiff;
    const simpOnly = differ2.diffStates(['⊢ ∫ (v : V), Complex.exp (↑(-2 * π * ⟪v, w⟫) * Complex.I) • (f ∘ ⇑A) v = c'], ['⊢ ∫ (v : V), g (A v) = c']);
    same(simpOnly.after[0].lines[0].segments.filter((x) => x.changed).map((x) => x.text), ['g (A v)'], 'not `g` and `)` with a stray `(`, `A`, `v`');
    const fourierEq = differ2.tokenDiff('𝓕 (f ∘ ⇑A) w', '∫ (v : V), e v • (f ∘ ⇑A) v');
    same(fourierEq.b.map((x) => [x.text, x.changed]), [['∫ (v : V), e v •', true], [' (f ∘ ⇑A) ', false], ['v', true]]);
    same(fourierEq.a.map((x) => [x.text, x.changed]), [['𝓕', true], [' (f ∘ ⇑A) ', false], ['w', true]]);
    // What replaced a term is marked where it now is (`(a).toReal` → `a`, as the infoview marks it).
    same(differ2.tokenDiff('(a).toReal • b', 'a • b').b.filter((x) => x.changed).map((x) => x.text), ['a']);
    // A line that only lost something: marked on the side where it changed, a bar on the other.
    tooltipView.goalsSide = 'after';
    tooltipView.renderGoals({ at: false, tactic: 'rw [h]', goals: ['⊢ a • b'], before: ['⊢ c • a • b'], step: 0, steps: 1 }, null, titleEl, bodyEl);
    assert(bodyEl.innerHTML.includes('verso-diff-line-touched-ins') && !bodyEl.innerHTML.includes('verso-diff-ins'), bodyEl.innerHTML);
    // A tactic that changed nothing: its goals, without a before/after switch.
    tooltipView.renderGoals({ at: false, tactic: 'skip', goals: ['⊢ a'], before: ['⊢ a'], step: 0, steps: 1 }, null, titleEl, bodyEl);
    assert(titleEl.innerHTML.includes('(no change)') && !titleEl.innerHTML.includes('data-side'), titleEl.innerHTML);

    // Stepping keeps the card's top-left corner where it is, inside the window: in a 1200×900
    // window, a 460-wide card at (700, 500) stays, and scrolls in the 388 pixels below its top.
    const placed = (left, top, height) => {
      const card = { offsetHeight: height, offsetWidth: 440, style: { maxHeight: '' } };
      const box = { style: { left: `${left}px`, top: `${top}px` }, querySelector: () => card };
      Object.assign(context, { innerWidth: 1200, innerHeight: 900, getComputedStyle: () => ({ maxWidth: '460px' }) });
      try { tooltipView.keepPlace.call({ container: box }); } finally { delete context.getComputedStyle; }
      return [box.style.left, box.style.top, card.style.maxHeight];
    };
    same(placed(700, 500, 600), ['700px', '500px', '388px']);
    same(placed(700, 100, 300), ['700px', '100px', ''], 'fits as it is');
    // Moved only when it would not fit: no room for its widest on the right, little below it.
    same(placed(900, 800, 600), ['728px', '648px', '240px']);

    // Lean's messages: an error, and `#check`'s output.
    const failed = at(30, 'rfl');
    assert.strictEqual(failed.messages[0].severity, 'error');
    assert(failed.messages[0].text.startsWith('Tactic `rfl` failed'), failed.messages[0].text);
    assert.strictEqual(at(27, '#check').messages[0].text, 'double (n : Nat) : Nat');
    // Columns count UTF-16 units: `𝕜` is two.
    assert.strictEqual(at(32, 'h𝕜').token.typeSignature, 'h𝕜 : 𝕜 = 𝕜');
    assert.strictEqual(at(32, 'by').goals.goals.join('|'), '𝕜 : Nat\nh𝕜 : 𝕜 = 𝕜\n⊢ 𝕜 + 0 = 𝕜');
    // A field in its place. Lean's hover on `mp` alone is `Iff.mp`'s general statement; with the
    // hover of what comes before the dot, the tooltip says what it is here, and keeps Lean's below.
    const field = (line, chain, word) => {
      const start = col(line, chain);
      const c = start + chain.length - word.length;
      return exact.describe(data, line, c, c + word.length, c + 1, chain, start).token;
    };
    const mp = field(35, 'h.mp', 'mp');
    assert.strictEqual(mp.typeSignature, 'h.mp : p → q');
    assert.strictEqual(mp.display, 'h.mp');
    assert.strictEqual(mp.name, 'Iff.mp', 'the constant is still the one the docs link to');
    assert(mp.docstring.includes('```lean\nIff.mp {a b : Prop} (self : a ↔ b) : a → b\n```'), mp.docstring);
    assert(mp.docstring.startsWith("Worked out from `h` and Lean's hover for `mp`:"), mp.docstring);
    assert.strictEqual(field(37, 'h.right', 'right').typeSignature, 'h.right : q');
    assert.strictEqual(field(37, 'h.left', 'left').typeSignature, 'h.left : p');
    // On a lemma, its own parameters stay in front, as in the lemma's hover.
    const mpr = field(39, 'Nat.lt_iff_add_one_le.mpr', 'mpr');
    assert.strictEqual(mpr.typeSignature, 'Nat.lt_iff_add_one_le.mpr {m n : Nat} : m + 1 ≤ n → m < n');
    assert.strictEqual(mpr.display, 'Nat.lt_iff_add_one_le.mpr');
    // The lemma itself, and a field hovered without its chain, show Lean's hover unchanged.
    assert.strictEqual(field(39, 'Nat.lt_iff_add_one_le', 'Nat.lt_iff_add_one_le').typeSignature, 'Nat.lt_iff_add_one_le {m n : Nat} : m < n ↔ m + 1 ≤ n');
    assert.strictEqual(at(35, 'mp').token.typeSignature, 'Iff.mp {a b : Prop} (self : a ↔ b) : a → b');
    // The same from signatures alone (what the estimate uses, with Loogle's).
    const terms = context.LeanTerms;
    assert.strictEqual(terms.fieldTypeOf('{a b : Prop} (self : a ↔ b) : a → b', 'Nat.even_add_one', 'Even (n + 1) ↔ ¬Even n'), 'Even (n + 1) → ¬Even n');
    assert.strictEqual(terms.fieldTypeOf('{p : Prop} [self : Fact p] : p', 'hT', 'Fact (0 < T)'), '0 < T', 'a receiver that is an instance argument');
    assert.strictEqual(terms.fieldTypeOf('{α : Type u_1} [LE α] {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c', 'h', 'x ≤ y + 1'), 'y + 1 ≤ ?c → x ≤ ?c');
    assert.strictEqual(terms.fieldTypeOf('{a b : Prop} (self : a ↔ b) : a → b', 'h', 'ℕ'), null, 'not a field of that type');
    assert.strictEqual(terms.fieldChainInPlace({ name: 'hT', type: 'Fact (0 < T)' }, [
      { text: 'out', name: 'Fact.out', signature: 'Fact.out {p : Prop} [self : Fact p] : p' },
      { text: 'le', name: 'LT.lt.le', signature: 'LT.lt.le.{u_1} {α : Type u_1} [Preorder α] {a b : α} (h : a < b) : a ≤ b' }]).signature, 'hT.out.le : 0 ≤ T');
    assert.strictEqual(terms.fieldChainInPlace({ name: 'foo', signature: 'foo (h : p) : a ↔ b' }, [{ text: 'mp', name: 'Iff.mp', signature: 'Iff.mp {a b : Prop} (self : a ↔ b) : a → b' }]), null,
      'a constant that takes an argument first');
    const estimate = context.fieldResultInPlace(
      { name: 'Iff.mp', typeSignature: 'Iff.mp {a b : Prop} (self : a ↔ b) : a → b', docstring: 'Modus ponens.', sourceUrl: 'u' },
      { name: 'Iff.mp', type: '{a b : Prop} (self : a ↔ b) : a → b' },
      { name: 'Nat.even_add_one', signature: 'Nat.even_add_one {n : ℕ} : Even (n + 1) ↔ ¬Even n' },
      [{ text: 'mp', hit: { name: 'Iff.mp', type: '{a b : Prop} (self : a ↔ b) : a → b' } }]);
    assert.strictEqual(estimate.typeSignature, 'Nat.even_add_one.mp {n : ℕ} : Even (n + 1) → ¬Even n');
    assert.strictEqual(estimate.name, 'Nat.even_add_one.mp');
    assert.strictEqual(estimate.sourceUrl, 'u');
    assert(estimate.docstring.includes('Iff.mp {a b : Prop} (self : a ↔ b) : a → b') && estimate.docstring.endsWith('Modus ponens.'), estimate.docstring);

    // Output that doesn't rebuild the source is refused rather than shown at the wrong place.
    assert.throws(() => convertModule(sampleModule, sampleSource.replace('double', 'triple')), /does not match the source/);

    // Whitespace is the one thing SubVerso may drop (the blank lines between a Verso document's
    // blocks); any other difference is refused.
    const blocks = { items: [{ code: 0, defines: [] }, { code: 1, defines: [] }],
      data: { tokens: {}, goals: {}, messageContents: {}, code: { 0: { unparsed: { str: '#doc (Manual) "T" =>' } }, 1: { unparsed: { str: ':::group "g"\nProse.\n:::' } } } } };
    assert.strictEqual(convertModule(blocks, '#doc (Manual) "T" =>\n\n:::group "g"\nProse.\n:::\n').tactics.length, 0);
    assert.throws(() => convertModule(blocks, '#doc (Manual) "T" =>\n\nextra\n:::group "g"\nProse.\n:::\n'), /does not match the source/);
    assert.throws(() => convertModule(blocks, '#doc (Manual) "T" =>\n\n:::group "g"\nProse.\n:::\nmore'), /covers/);

    // --- The helper: what it accepts, and what it answers without running anything.
    assert(helper.isRepo('seewoo5/DifferentProofs') && helper.isRepo('leanprover-community/mathlib4'));
    for (const bad of ['../x', 'a/b/c', 'a/..', 'a', '-a/b', 'a/b c']) assert(!helper.isRepo(bad), `not a repository: ${bad}`);
    assert(helper.isSha('1adf3d0cad950f5a9059596b4df342c38aae8353') && !helper.isSha('1adf3d0') && !helper.isSha('HEAD'));
    assert(helper.isLeanPath('A/B.lean') && helper.isLeanPath('Formal/DF_1/DF_1_2.lean'));
    for (const bad of ['../A.lean', '/abs/A.lean', 'A/../B.lean', 'A/B.txt', 'A\\B.lean', 'A//B.lean']) assert(!helper.isLeanPath(bad), `not a file path: ${bad}`);
    assert.strictEqual(helper.importsOf(['module', '', 'public import Mathlib.A', 'import all B.C -- note', '/- import Not.This -/', 'meta import D', '',
      '/-- doc: import Nope -/', 'theorem x : True := trivial', 'import Late'].join('\n')).join(' '), 'Mathlib.A B.C D');
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'lean-lens-test-'));
    try {
      fs.mkdirSync(path.join(root, 'src'));
      assert.strictEqual(helper.moduleNameFor(root, './.', 'A/B/C.lean'), 'A.B.C');
      assert.strictEqual(helper.moduleNameFor(root, `./.${path.delimiter}${path.join(root, 'src')}`, 'src/Foo/Bar.lean'), 'Foo.Bar', 'the deepest source root');
      assert.strictEqual(helper.moduleNameFor(root, path.join(root, 'src'), 'Other/X.lean'), null, 'outside every source root');
      fs.writeFileSync(path.join(root, 'lakefile.toml'), 'name = "x"\n');
      fs.mkdirSync(path.join(root, 'sub', 'deep'), { recursive: true });
      fs.writeFileSync(path.join(root, 'sub', 'lakefile.lean'), '');
      assert.strictEqual(helper.lakeRootFor(root, 'A/B.lean'), '');
      assert.strictEqual(helper.lakeRootFor(root, 'sub/deep/C.lean'), 'sub');
      assert(helper.usesMathlib('{"name":"x","packages":[{"name":"mathlib"}]}') && helper.usesMathlib('{"name":"mathlib","packages":[]}'));
      assert(!helper.usesMathlib('{"name":"x","packages":[{"name":"batteries"}]}') && !helper.usesMathlib('not json'));
      // Only this machine's extension, with the token.
      const ok = { host: '127.0.0.1:5326', origin: 'chrome-extension://abcdef', 'x-lean-lens-token': 'secret-token' };
      assert(helper.authorized(ok, 5326, 'secret-token'));
      assert(helper.authorized(Object.assign({}, ok, { origin: undefined }), 5326, 'secret-token'), 'no Origin: not a browser');
      assert(!helper.authorized(Object.assign({}, ok, { origin: 'https://evil.example' }), 5326, 'secret-token'), 'a web page');
      assert(!helper.authorized(Object.assign({}, ok, { host: 'evil.example:5326' }), 5326, 'secret-token'), 'DNS rebinding');
      assert(!helper.authorized(Object.assign({}, ok, { 'x-lean-lens-token': 'wrong' }), 5326, 'secret-token'));
      assert(!helper.authorized(Object.assign({}, ok, { 'x-lean-lens-token': undefined }), 5326, 'secret-token'));

      // The sandbox profile (macOS): only the paths given, no network unless asked, and a
      // checkout's own `.git` kept as it is.
      const copy = '/Users/me/Library/Caches/lean-lens/repos/o/r';
      const profile = helper.seatbeltProfile({ readable: ['/opt/lean'], writable: [copy], guarded: [`${copy}/.git`], home: '/Users/me' });
      assert(profile.includes('(deny network*)'));
      assert(!helper.seatbeltProfile({ network: true, readable: ['/opt/lean'] }).includes('(deny network*)'), 'network only when asked');
      assert(profile.includes('(deny file-read* (subpath "/Users")'), profile);
      assert(profile.includes(`(allow file-read* (subpath "/opt/lean") (subpath "${copy}"))`), profile);
      assert(profile.includes(`(deny file-write* (subpath "${copy}/.git"))`), profile);
      assert(profile.indexOf('(deny file-write* (subpath') > profile.indexOf('(allow file-write*'), 'the guard comes after the allowance, so it wins');
      // The writable folder itself can't be moved or swapped for a link to another place, which
      // the helper would then open to the sandbox or run `git` in.
      assert(profile.includes(`(deny file-write* (literal "${copy}"))`), profile);
      assert(profile.indexOf(`(deny file-write* (literal "${copy}"))`) > profile.indexOf('(allow file-write*'));
      assert(profile.includes('(literal "/Users/me/Library/Caches")'), 'folders above an allowed path can be looked through');
      assert(!/\(allow file-read\*\s*\)/.test(helper.seatbeltProfile({})), 'no allowance without a path (it would allow everything)');
      assert(helper.seatbeltProfile({ readable: ['/a "b"'] }).includes('(subpath "/a \\"b\\"")'), 'paths are quoted');
      if (process.platform === 'darwin' && fs.existsSync('/usr/bin/sandbox-exec')) {
        // The real thing, on files made for the purpose.
        const box = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'lean-lens-box-')));
        try {
          fs.mkdirSync(path.join(box, 'in', '.git'), { recursive: true });
          fs.mkdirSync(path.join(box, 'out'));
          fs.mkdirSync(path.join(box, 'empty'));
          fs.writeFileSync(path.join(box, 'in', 'a.txt'), 'inside');
          fs.writeFileSync(path.join(box, 'out', 'b.txt'), 'outside');
          const confined = helper.seatbeltProfile({ writable: [path.join(box, 'in'), path.join(box, 'empty')], guarded: [path.join(box, 'in', '.git')] });
          const sb = (...command) => spawnSync('/usr/bin/sandbox-exec', ['-p', confined, ...command], { encoding: 'utf8' });
          if (sb('/usr/bin/true').status === 0) { // (not when the tests themselves run in a sandbox)
            assert.strictEqual(sb('/bin/cat', path.join(box, 'in', 'a.txt')).stdout, 'inside');
            assert.notStrictEqual(sb('/bin/cat', path.join(box, 'out', 'b.txt')).status, 0, 'a file outside is not readable');
            assert.strictEqual(sb('/usr/bin/touch', path.join(box, 'in', 'new.txt')).status, 0);
            assert.notStrictEqual(sb('/usr/bin/touch', path.join(box, 'out', 'new.txt')).status, 0, 'nor writable');
            assert.notStrictEqual(sb('/usr/bin/touch', path.join(box, 'in', '.git', 'hook')).status, 0, 'the checkout\'s .git is kept');
            assert(!fs.existsSync(path.join(box, 'out', 'new.txt')) && !fs.existsSync(path.join(box, 'in', '.git', 'hook')));
            // A writable folder itself stays what and where it is.
            assert.notStrictEqual(sb('/bin/rmdir', path.join(box, 'empty')).status, 0, 'an empty writable folder cannot be removed (and a link put there)');
            assert.notStrictEqual(sb('/bin/mv', path.join(box, 'in'), path.join(box, 'empty', 'moved')).status, 0, 'nor moved away, .git and all');
            assert(fs.lstatSync(path.join(box, 'empty')).isDirectory() && fs.existsSync(path.join(box, 'in', '.git')));
            assert.strictEqual(sb('/usr/bin/touch', path.join(box, 'empty', 'x')).status, 0, 'writing inside it still works');
          }
        } finally {
          fs.rmSync(box, { recursive: true, force: true });
        }
      }

      const h = helper.createHelper({ cacheDir: path.join(root, 'cache'), log: () => {} });
      assert(['seatbelt', 'bwrap', 'none'].includes(await h.sandbox()), 'the sandbox is on wherever the system has one');
      assert.strictEqual(await helper.createHelper({ cacheDir: path.join(root, 'cache'), log: () => {}, sandbox: false }).sandbox(), 'off');
      const sha = '1adf3d0cad950f5a9059596b4df342c38aae8353';
      const ask = (method, url, body) => { const r = h.handle(method, url, body); return { status: r.status, body: JSON.parse(r.body) }; };
      assert(h.config.token.length >= 20, 'a token is made on first run');
      assert.strictEqual(helper.createHelper({ cacheDir: path.join(root, 'cache'), log: () => {} }).config.token, h.config.token, 'and kept');
      assert.strictEqual(ask('GET', '/status').body.format, DATA_FORMAT_VERSION);
      assert.strictEqual(ask('GET', '/status').body.sandbox, await h.sandbox());
      // A repository that was not allowed is never touched.
      const refused = ask('POST', '/run', { repo: 'o/r', sha, paths: ['A.lean'] });
      assert.strictEqual(refused.status, 403);
      assert.strictEqual(refused.body.state, 'not_allowed');
      assert.strictEqual(ask('POST', '/file', { repo: 'o/r', sha, path: 'A.lean' }).body.state, 'not_allowed');
      assert.strictEqual(ask('POST', '/allow', { repo: 'o/r' }).body.ok, true);
      assert.strictEqual(ask('POST', '/file', { repo: 'o/r', sha, path: 'A.lean' }).body.state, 'missing');
      assert.strictEqual(ask('GET', `/job?repo=o/r&sha=${sha}`).body.state, 'idle');
      assert.strictEqual(ask('POST', '/file', { repo: 'o/r', sha: 'main', path: 'A.lean' }).status, 400);
      assert.strictEqual(ask('POST', '/file', { repo: 'o/r', sha, path: '../../etc/passwd.lean' }).status, 400);
      assert.strictEqual(ask('POST', '/run', { repo: 'o/r', sha, paths: ['A.lean', '/etc/x.lean'] }).status, 400);
      assert.strictEqual(ask('POST', '/allow', { repo: '../..' }).status, 400);
      // Once Lean has run, the file's data is served from disk.
      const stored = path.join(root, 'cache', 'data', `v${DATA_FORMAT_VERSION}`, 'o', 'r', sha, 'Sample.lean.json');
      fs.mkdirSync(path.dirname(stored), { recursive: true });
      fs.writeFileSync(stored, JSON.stringify(data));
      const ready = ask('POST', '/file', { repo: 'o/r', sha, path: 'Sample.lean' });
      assert.strictEqual(ready.body.state, 'ready');
      assert.strictEqual(ready.body.data.hovers.length, data.hovers.length);

      // Started through a link to its folder (as `/var` is on macOS), the helper still runs.
      fs.symlinkSync(helperDir, path.join(root, 'linked-helper'));
      const viaLink = spawnSync(process.execPath, [path.join(root, 'linked-helper', 'lean-lens-helper.mjs'), '--help'], { encoding: 'utf8' });
      assert(viaLink.stdout.includes('Lean Lens helper'), `the helper said nothing: ${viaLink.stderr}`);

      // Its port taken: it says by what, and what to do about it.
      {
        const { spawn } = require('child_process');
        const helperFile = path.join(helperDir, 'lean-lens-helper.mjs');
        const freePort = () => new Promise((resolve) => {
          const probe = require('net').createServer();
          probe.listen(0, '127.0.0.1', () => { const { port } = probe.address(); probe.close(() => resolve(port)); });
        });
        const taken = require('net').createServer();
        await new Promise((resolve) => taken.listen(0, '127.0.0.1', resolve));
        const byOther = spawnSync(process.execPath, [helperFile, '--port', String(taken.address().port), '--cache', path.join(root, 'cache-port')], { encoding: 'utf8' });
        taken.close();
        assert(/Port \d+ is in use by another program/.test(byOther.stderr) && byOther.status === 1, byOther.stderr);
        const port = await freePort();
        const first = spawn(process.execPath, [helperFile, '--port', String(port), '--cache', path.join(root, 'cache-port')], { stdio: ['ignore', 'pipe', 'ignore'] });
        try {
          await new Promise((resolve, reject) => {
            let said = '';
            first.stdout.on('data', (chunk) => { said += chunk; if (said.includes('helper is running')) resolve(); });
            first.on('close', () => reject(new Error(`the helper did not start: ${said}`)));
          });
          const second = spawnSync(process.execPath, [helperFile, '--port', String(port), '--cache', path.join(root, 'cache-port')], { encoding: 'utf8' });
          assert(/A Lean Lens helper is already running on port \d+\. Stop that one first/.test(second.stderr), second.stderr);
          const elsewhere = spawnSync(process.execPath, [helperFile, '--port', String(port), '--cache', path.join(root, 'cache-port-2')], { encoding: 'utf8' });
          assert(/A Lean Lens helper is already running/.test(elsewhere.stderr), `also one with other settings: ${elsewhere.stderr}`);
        } finally {
          first.kill('SIGTERM');
          await new Promise((resolve) => first.on('close', resolve));
        }
      }

      // The Lean version a project pins goes to elan, outside the sandbox: a plain file naming a
      // version, never a link to some other file.
      const project = path.join(root, 'project');
      fs.mkdirSync(project);
      assert.throws(() => helper.toolchainOf(project), /no lean-toolchain file/);
      fs.writeFileSync(path.join(project, 'lean-toolchain'), 'leanprover/lean4:v4.35.0\n');
      assert.strictEqual(helper.toolchainOf(project), 'leanprover/lean4:v4.35.0');
      // Each Lean version has an extractor of its own, also versions whose names read alike.
      const rev = '892d6dc520270b5fb8c1291dd1b131e8c16255ed';
      // The folder a Lean is installed in is that Lean's alone: it has `lib/lean`, and is not a
      // place where other things are installed, the home folder or the helper's folders among them.
      {
        const at = fs.realpathSync(root);
        for (const dir of ['own/bin', 'own/lib/lean', 'bare/bin', 'shared/bin', 'shared/lib/lean', 'shared/home/me', 'shared/cache']) fs.mkdirSync(path.join(at, dir), { recursive: true });
        assert.strictEqual(helper.leanInstallation(path.join(at, 'own/bin/lake'), { home: path.join(at, 'shared/home/me') }), path.join(at, 'own'));
        assert.throws(() => helper.leanInstallation(path.join(at, 'bare/bin/lake')), /not in a Lean installation/);
        assert.throws(() => helper.leanInstallation(path.join(at, 'own/lake')), /not in a Lean installation/);
        assert.throws(() => helper.leanInstallation(path.join(at, 'shared/bin/lake'), { home: path.join(at, 'shared/home/me') }), /folder of its own/);
        assert.throws(() => helper.leanInstallation(path.join(at, 'shared/bin/lake'), { home: '/nowhere', others: [path.join(at, 'shared/cache')] }), /folder of its own/);
        assert.throws(() => helper.leanInstallation(path.join(at, 'own/bin/lake'), { home: path.join(at, 'own') }), /folder of its own/);
        if (process.platform !== 'win32') for (const lake of ['/usr/bin/lake', '/usr/local/bin/lake', '/bin/lake']) assert.throws(() => helper.leanInstallation(lake), /folder of its own|not in a Lean installation/);
      }
      const lean = (name, at = '/toolchains/x', files = ['bin/lean 1 2']) => ({ name, root: at, files });
      const dirFor = (toolchain, from = 'https://example.invalid/subverso') => helper.extractorFor(toolchain, from, rev).dirName;
      assert(/^leanprover_lean4_v4\.35\.0-[0-9a-f]{32}$/.test(dirFor(lean('leanprover/lean4:v4.35.0'))));
      assert.strictEqual(dirFor(lean('a/b:c')), dirFor(lean('a/b:c')));
      assert.notStrictEqual(dirFor(lean('a_b/c:d')), dirFor(lean('a/b_c:d')));
      assert.notStrictEqual(dirFor(lean('a/b:stable', '/toolchains/v1')), dirFor(lean('a/b:stable', '/toolchains/v2')));
      assert.notStrictEqual(dirFor(lean('a/b:stable', '/t', ['bin/lean 1 2'])), dirFor(lean('a/b:stable', '/t', ['bin/lean 1 3'])));
      assert.notStrictEqual(dirFor(lean('a/b:c')), dirFor(lean('a/b:c'), 'https://example.invalid/other'));
      assert.notStrictEqual(dirFor(lean('a/b:c')), helper.extractorFor(lean('a/b:c'), 'https://example.invalid/subverso', 'f'.repeat(40)).dirName);
      fs.writeFileSync(path.join(project, 'lean-toolchain'), 'v4; curl example.com\n');
      assert.throws(() => helper.toolchainOf(project), /does not name a Lean version/);
      fs.rmSync(path.join(project, 'lean-toolchain'));
      fs.writeFileSync(path.join(root, 'elsewhere.txt'), 'leanprover/lean4:v4.35.0\n');
      fs.symlinkSync(path.join(root, 'elsewhere.txt'), path.join(project, 'lean-toolchain'));
      assert.throws(() => helper.toolchainOf(project), /does not name a Lean version/, 'a link is not read');

      // --- Lean in a codespace, the parts that need none: the script that starts the helper
      // there, and the Linux sandbox it runs a pull request's code in.
      const cs = await import(pathToFileURL(path.join(helperDir, 'codespaces.mjs')).href);
      assert.strictEqual(cs.displayNameFor('seewoo5/DifferentProofs'), 'Lean Lens DifferentProofs');
      assert.strictEqual(cs.displayNameFor('o/my.repo_1-x'), 'Lean Lens my-repo_1-x', 'GitHub refuses a colon or a dot in the name');
      assert(cs.displayNameFor(`o/${'x'.repeat(80)}`).length <= 48, 'GitHub allows 48 characters');
      assert(cs.confines('seatbelt') && cs.confines('bwrap') && !cs.confines('none') && !cs.confines('off'));
      const boot = cs.bootstrapScript({ files: { 'a.mjs': "it's here" }, token: 'tok-1', repo: 'o/r', port: 6000, sandbox: false, cloneBase: 'file:///x y/' });
      assert(boot.includes(`put 'a.mjs' '${Buffer.from("it's here").toString('base64')}'`), 'the helper\'s files travel with it');
      assert(boot.includes('--port 6000') && boot.includes("--allow 'o/r'") && boot.includes('--no-sandbox') && boot.includes("--clone-base 'file:///x y/'"), boot);
      assert(boot.includes('/workspaces/r}}"') && boot.includes(`--commits-only --link 'o/r='"$CHECKOUT"`), 'it starts from the commits of the codespace\'s own checkout');
      assert(!cs.bootstrapScript({ files: {}, token: 't', repo: 'o/r' }).includes('--no-sandbox'));
      if (spawnSync('bash', ['--version']).status === 0) {
        assert.strictEqual(spawnSync('bash', ['-n'], { input: boot, encoding: 'utf8' }).status, 0, 'the script is valid bash');
      }
      assert.strictEqual(helper.bwrapArgs({ readable: ['/opt/lean'], writable: ['/c/copy'], guarded: ['/c/copy/.git'], cwd: '/c/copy', system: ['--ro-bind', '/usr', '/usr'] }).join(' '),
        '--unshare-all --die-with-parent --new-session --proc /proc --dev /dev --ro-bind /usr /usr --ro-bind /opt/lean /opt/lean --bind /c/copy /c/copy --ro-bind-try /c/copy/.git /c/copy/.git --remount-ro / --chdir /c/copy');
      assert(helper.bwrapArgs({ network: true, system: [] }).includes('--share-net'), 'the network only when asked');

      // --- Disk. Only the results stay: a repository's copy and its build go when they are not
      // in use. At start, what an earlier helper left behind is removed.
      assert.strictEqual(helper.formatBytes(10.6e9), '10.6 GB');
      assert.strictEqual(helper.formatBytes(225e6), '225 MB');
      assert.strictEqual(helper.formatBytes(412e3), '412 KB');
      const cache2 = path.join(root, 'cache2');
      const stateOf = (cache, repo) => path.join(cache, 'state', helper.sha256(repo).slice(0, 32));
      const fakeCopy = (cache, repo, owner) => {
        fs.mkdirSync(path.join(cache, 'repos', ...repo.split('/'), '.git'), { recursive: true });
        fs.writeFileSync(path.join(cache, 'repos', ...repo.split('/'), '.git', 'HEAD'), 'ref: refs/heads/main\n');
        fs.mkdirSync(stateOf(cache, repo), { recursive: true });
        if (owner) fs.writeFileSync(path.join(stateOf(cache, repo), 'owner'), `${owner}\n`);
      };
      const gone = spawnSync(process.execPath, ['-e', '']).pid; // a process that has ended
      fakeCopy(cache2, 'o/left', gone); // its helper was killed
      fakeCopy(cache2, 'o/old', null); // from a version that did not note who uses a copy
      fakeCopy(cache2, 'o/inuse', process.ppid); // a process that is running
      fs.mkdirSync(path.join(cache2, 'work', `${gone}-abc`), { recursive: true });
      fs.mkdirSync(path.join(cache2, 'work', `${process.ppid}-abc`), { recursive: true });
      fs.mkdirSync(path.join(cache2, 'home'));
      const said = [];
      const h2 = helper.createHelper({ cacheDir: cache2, log: (message) => said.push(message) });
      assert(!fs.existsSync(path.join(cache2, 'repos', 'o', 'left')) && !fs.existsSync(path.join(cache2, 'repos', 'o', 'old')), 'copies no running helper uses go at start');
      assert(!fs.existsSync(stateOf(cache2, 'o/left')), 'with what was noted about them');
      assert(fs.existsSync(path.join(cache2, 'repos', 'o', 'inuse', '.git')), 'a copy a running helper uses is left');
      assert(!fs.existsSync(path.join(cache2, 'work', `${gone}-abc`)) && fs.existsSync(path.join(cache2, 'work', `${process.ppid}-abc`)), 'scratch folders likewise');
      assert(!fs.existsSync(path.join(cache2, 'home')), 'the scratch folders of earlier versions go');
      assert(said.some((message) => message.includes('o/left') && message.includes('The results stay')), said.join('\n'));
      fakeCopy(cache2, 'o/kept', gone);
      helper.createHelper({ cacheDir: cache2, keepBuilds: true, log: () => {} });
      assert(fs.existsSync(path.join(cache2, 'repos', 'o', 'kept')), '--keep-builds removes nothing');
      assert.throws(() => helper.createHelper({ cacheDir: cache2, tidyMinutes: -1, log: () => {} }), /number of minutes/);

      // A copy that cannot be removed (here: a folder that may not be changed) does not keep the
      // helper from starting. It says so, and the next start tries again.
      if (process.getuid && process.getuid() !== 0) {
        fakeCopy(cache2, 'o/stuck', gone);
        const stuck = path.join(cache2, 'repos', 'o', 'stuck', '.git');
        fs.chmodSync(stuck, 0o555);
        const complaints = [];
        try {
          helper.createHelper({ cacheDir: cache2, log: (message) => complaints.push(message) });
          assert(complaints.some((message) => message.includes('The copy of o/stuck could not be removed now')), complaints.join('\n'));
        } finally {
          fs.chmodSync(stuck, 0o755);
        }
        helper.createHelper({ cacheDir: cache2, log: () => {} });
        assert(!fs.existsSync(path.join(cache2, 'repos', 'o', 'stuck')), 'gone at the next start');
      }

      // `clean`: everything but the settings and the results; with `results`, those too.
      fs.mkdirSync(path.join(cache2, 'extractors', 'x'), { recursive: true });
      fs.writeFileSync(path.join(cache2, 'extractors', 'x', 'subverso-extract-mod'), 'binary');
      fs.mkdirSync(path.join(cache2, 'data', 'v2'), { recursive: true });
      fs.writeFileSync(path.join(cache2, 'data', 'v2', 'r.json'), '{}');
      await assert.rejects(helper.cleanCache(cache2), /A helper is running/, 'not under a helper that is using the files');
      assert(fs.existsSync(path.join(cache2, 'repos', 'o', 'inuse')));
      const cleaned = await helper.cleanCache(cache2, { force: true });
      assert.deepStrictEqual(fs.readdirSync(cache2).sort(), ['config.json', 'data']);
      assert.strictEqual(cleaned.removed.map((entry) => entry.what).join(' | '), 'copies of repositories with their builds | SubVerso extractors | scratch files');
      assert(cleaned.bytes >= 0 && (cleaned.freed === null || cleaned.freed >= 0));
      assert.strictEqual(JSON.parse(fs.readFileSync(path.join(cache2, 'config.json'), 'utf8')).token, h2.config.token, 'the token stays');
      await helper.cleanCache(cache2, { results: true });
      assert.deepStrictEqual(fs.readdirSync(cache2), ['config.json']);
      // Builds kept in a folder of their own (--builds) are found there, at start and by `clean`.
      const builds2 = path.join(root, 'builds2');
      fakeCopy(builds2, 'o/elsewhere', gone);
      helper.createHelper({ cacheDir: cache2, buildsDir: builds2, keepBuilds: true, log: () => {} });
      assert(fs.existsSync(path.join(builds2, 'repos', 'o', 'elsewhere')) && !fs.existsSync(path.join(cache2, 'repos')));
      assert.strictEqual((await helper.cleanCache(cache2)).removed.length, 0, 'not without being told where the builds are');
      assert.strictEqual((await helper.cleanCache(cache2, { buildsDir: builds2 })).removed[0].what, 'copies of repositories with their builds');
      assert.deepStrictEqual(fs.readdirSync(builds2), []);
      fakeCopy(builds2, 'o/elsewhere', gone);
      helper.createHelper({ cacheDir: cache2, buildsDir: builds2, log: () => {} });
      assert(!fs.existsSync(path.join(builds2, 'repos', 'o', 'elsewhere')), 'a copy nobody uses goes at start, wherever builds are kept');
      assert.strictEqual((await helper.cleanCache(cache2)).removed.length, 0);
      fs.mkdirSync(path.join(cache2, 'repos', 'o'), { recursive: true });
      assert.strictEqual((await helper.cleanCache(cache2)).removed.length, 0, 'an empty folder goes without a mention');
      assert.deepStrictEqual(fs.readdirSync(cache2), ['config.json']);

      if (spawnSync('git', ['--version']).status === 0) {
        // Runs as far as git goes: a repository with one Lean file and no Lake project.
        const git = (cwd, ...args) => {
          const result = spawnSync('git', ['-c', 'user.name=t', '-c', 'user.email=t@example.invalid', '-c', 'commit.gpgsign=false', '-c', 'init.defaultBranch=main', ...args], { cwd, encoding: 'utf8' });
          assert.strictEqual(result.status, 0, result.stderr);
          return result.stdout.trim();
        };
        const origin = path.join(root, 'origin');
        fs.mkdirSync(origin);
        git(origin, 'init', '--quiet');
        fs.writeFileSync(path.join(origin, 'A.lean'), 'def a := 1\n');
        git(origin, 'add', 'A.lean');
        git(origin, 'commit', '--quiet', '-m', 'one');
        const commit = git(origin, 'rev-parse', 'HEAD');
        fs.mkdirSync(path.join(root, 'remotes', 'o'), { recursive: true });
        git(root, 'clone', '--quiet', '--bare', origin, path.join(root, 'remotes', 'o', 'r.git'));
        const cloneBase = pathToFileURL(path.join(root, 'remotes')).href;
        const cache3 = path.join(root, 'cache3');
        const copy3 = path.join(cache3, 'repos', 'o', 'r');
        const runOnce = async (options) => {
          const made = helper.createHelper(Object.assign({ cacheDir: cache3, cloneBase, log: () => {} }, options));
          made.allow('o/r');
          made.start({ repo: 'o/r', sha: commit, pr: null, paths: ['A.lean'] });
          while (made.status('o/r', commit).state === 'pending') await tick(20);
          assert.strictEqual(made.status('o/r', commit).state, 'done', made.status('o/r', commit).error);
          assert.strictEqual(made.fileState('o/r', commit, 'A.lean').error, 'This file is not inside a Lake project');
          await made.idle();
          return made;
        };
        // The copy stays for a while after a run, and goes when the helper stops.
        const h3 = await runOnce({});
        assert.strictEqual(fs.readFileSync(path.join(copy3, 'A.lean'), 'utf8'), 'def a := 1\n', 'the commit is checked out in the copy');
        assert.strictEqual(fs.readFileSync(path.join(stateOf(cache3, 'o/r'), 'owner'), 'utf8').trim(), String(process.pid), 'and this helper is noted as using it');
        h3.shutdown();
        assert(!fs.existsSync(copy3) && !fs.existsSync(stateOf(cache3, 'o/r')), 'stopping removes the copy');
        assert.deepStrictEqual(fs.readdirSync(path.join(cache3, 'work')), [], 'and the scratch folders');
        // --tidy-after 0: it goes as soon as its run is over.
        const h4 = await runOnce({ tidyMinutes: 0 });
        assert(!fs.existsSync(copy3), 'removed when the run is over');
        h4.shutdown();
        // --keep-builds: it stays, also when the helper stops.
        (await runOnce({ keepBuilds: true })).shutdown();
        assert(fs.existsSync(path.join(copy3, 'A.lean')));
        // Something else where the copy should be, a link to another checkout: the helper makes
        // its own copy there, and leaves alone what the link points to.
        fs.rmSync(copy3, { recursive: true, force: true });
        const theirs = path.join(root, 'theirs');
        fs.mkdirSync(path.join(theirs, '.git'), { recursive: true });
        fs.writeFileSync(path.join(theirs, 'mine.txt'), 'mine');
        fs.symlinkSync(theirs, copy3);
        (await runOnce({ keepBuilds: true })).shutdown();
        assert(fs.lstatSync(copy3).isDirectory(), 'a real folder now');
        assert.strictEqual(fs.readFileSync(path.join(theirs, 'mine.txt'), 'utf8'), 'mine');
        assert(!fs.existsSync(path.join(theirs, 'A.lean')), 'nothing was checked out through the link');

        // --- The Lean of a run is resolved once, before the project's code runs. Lean, Lake and
        // elan are played by scripts: `lean-a` and `lean-b` are two installed Leans, each of whose
        // `lake` signs the extractor it builds. The project o/s asks for lean-a, and its code
        // (which `lake` runs while preparing the project) then rewrites `lean-toolchain` to
        // lean-b. Its files are still elaborated by lean-a, with an extractor kept for lean-a,
        // and their results say lean-a; a project that asks for lean-b gets one built by lean-b.
        if (process.platform !== 'win32') {
          const stubs = path.join(root, 'stub-lean');
          const toolchains = path.join(stubs, 'toolchains');
          const script = (file, lines) => { fs.mkdirSync(path.dirname(file), { recursive: true }); fs.writeFileSync(file, ['#!/bin/sh', ...lines, ''].join('\n'), { mode: 0o755 }); };
          script(path.join(stubs, 'bin', 'elan'), [
            'name="${ELAN_TOOLCHAIN:-$(cat lean-toolchain 2>/dev/null)}"',
            'case "$1 $2" in',
            `  "toolchain list") ls "${toolchains}" ;;`,
            `  "which lake") [ -x "${toolchains}/$name/bin/lake" ] && echo "${toolchains}/$name/bin/lake" ;;`,
            '  *) exit 1 ;;',
            'esac',
          ]);
          const lakeLines = [
            'me="$(basename "$(dirname "$(dirname "$0")")")"',
            'case "$1 $2" in',
            // (the project's own code, as its lakefile would run it)
            `  "env true") if [ -f next-lean ]; then cp next-lean lean-toolchain; echo "$me" >> "${stubs}/switched"; fi ;;`,
            '  "build subverso-extract-mod")',
            '    mkdir -p .lake/build/bin',
            `    printf '#!/bin/sh\\necho "%s" >> "${stubs}/used"\\ncp "${path.join(__dirname, 'fixtures', 'Sample.subverso.json')}" "$2"\\n' "$me" > .lake/build/bin/subverso-extract-mod`,
            '    chmod +x .lake/build/bin/subverso-extract-mod',
            '    echo "$me" > built-by ;;',
            '  "build "*) ;;',
            '  "env printenv") pwd ;;',
            '  "env "*) shift; exec "$@" ;;',
            '  *) exit 1 ;;',
            'esac',
          ];
          for (const name of ['lean-a', 'lean-b']) {
            script(path.join(toolchains, name, 'bin', 'lake'), lakeLines);
            fs.mkdirSync(path.join(toolchains, name, 'lib', 'lean'), { recursive: true });
          }
          // A Lean elan lists but has no Lake for, and one whose `lake` is not in a Lean installation.
          fs.mkdirSync(path.join(toolchains, 'lean-c'));
          script(path.join(toolchains, 'lean-d', 'bin', 'lake'), lakeLines);
          const subverso = path.join(stubs, 'subverso');
          fs.mkdirSync(subverso);
          git(subverso, 'init', '--quiet');
          fs.writeFileSync(path.join(subverso, 'lakefile.toml'), 'name = "subverso"\n');
          git(subverso, 'add', '.');
          git(subverso, 'commit', '--quiet', '-m', 'subverso');
          const subversoRev = git(subverso, 'rev-parse', 'HEAD');
          const projectAt = (name, files) => {
            const at = path.join(stubs, name);
            fs.mkdirSync(at);
            git(at, 'init', '--quiet');
            for (const [file, text] of Object.entries(files)) fs.writeFileSync(path.join(at, file), text);
            git(at, 'add', '.');
            git(at, 'commit', '--quiet', '-m', 'one');
            git(root, 'clone', '--quiet', '--bare', at, path.join(root, 'remotes', 'o', `${name}.git`));
            return git(at, 'rev-parse', 'HEAD');
          };
          const sample = fs.readFileSync(path.join(__dirname, 'fixtures', 'Sample.lean'), 'utf8');
          const lakefile = 'name = "p"\n';
          const shaS = projectAt('s', { 'lean-toolchain': 'lean-a\n', 'next-lean': 'lean-b\n', 'lakefile.toml': lakefile, 'Sample.lean': sample });
          const shaT = projectAt('t', { 'lean-toolchain': 'lean-b\n', 'lakefile.toml': lakefile, 'Sample.lean': sample, 'Again.lean': sample, 'More.lean': sample });
          const shaU = projectAt('u', { 'lean-toolchain': 'lean-c\n', 'lakefile.toml': lakefile, 'Sample.lean': sample });
          const shaV = projectAt('v', { 'lean-toolchain': 'lean-d\n', 'lakefile.toml': lakefile, 'Sample.lean': sample });
          const cache5 = path.join(root, 'cache5');
          const kept = path.join(cache5, 'extractors');
          // An extractor kept by an earlier version of the helper, under the name alone.
          fs.mkdirSync(path.join(kept, `lean-b-${'0'.repeat(32)}-${subversoRev.slice(0, 12)}`, '.lake', 'build', 'bin'), { recursive: true });
          fs.writeFileSync(path.join(kept, `lean-b-${'0'.repeat(32)}-${subversoRev.slice(0, 12)}`, '.lake', 'build', 'bin', 'subverso-extract-mod'), 'old');
          // (and what a helper that stopped while removing such ones left aside)
          fs.mkdirSync(path.join(kept, '.gone-1-abc', 'lean-c-old'), { recursive: true });
          const said = [];
          const h5 = helper.createHelper({ cacheDir: cache5, cloneBase, subverso, subversoRev, sandbox: false, log: (line) => said.push(line) });
          const elaborate = async (repo, sha, file) => {
            h5.allow(repo);
            h5.start({ repo, sha, pr: null, paths: [file] });
            while (h5.status(repo, sha).state === 'pending') await tick(20);
            assert.strictEqual(h5.fileState(repo, sha, file).state, 'ready', `${h5.status(repo, sha).error || h5.fileState(repo, sha, file).error}\n${said.join('\n')}`);
            await h5.idle();
            return JSON.parse(h5.readData(repo, sha, file));
          };
          const builtBy = () => fs.readdirSync(path.join(kept, `v${helper.EXTRACTOR_FORMAT}`)).sort().map((entry) =>
            `${entry.replace(/-[0-9a-f]{32}$/, '')} by ${fs.readFileSync(path.join(kept, `v${helper.EXTRACTOR_FORMAT}`, entry, 'built-by'), 'utf8').trim()}`);
          const read = (file) => fs.readFileSync(path.join(stubs, file), 'utf8').trim().split('\n').join(' ');
          const pathBefore = process.env.PATH;
          process.env.PATH = `${path.join(stubs, 'bin')}${path.delimiter}${pathBefore}`;
          try {
            assert.strictEqual((await elaborate('o/s', shaS, 'Sample.lean')).lean, 'lean-a', 'the results name the Lean that was resolved');
            assert.strictEqual(read('switched'), 'lean-a', "the project's code did rewrite lean-toolchain");
            assert.deepStrictEqual(builtBy(), ['lean-a by lean-a'], 'the extractor is kept for the Lean that built it');
            assert.strictEqual(read('used'), 'lean-a');
            assert.deepStrictEqual(fs.readdirSync(kept), [`v${helper.EXTRACTOR_FORMAT}`], 'extractors kept the earlier way are removed');
            // A project that asks for lean-b: its extractor is built by lean-b.
            assert.strictEqual((await elaborate('o/t', shaT, 'Sample.lean')).lean, 'lean-b');
            assert.deepStrictEqual(builtBy(), ['lean-a by lean-a', 'lean-b by lean-b']);
            assert.strictEqual(read('used'), 'lean-a lean-b');
            const stamp = JSON.parse(fs.readFileSync(path.join(kept, `v${helper.EXTRACTOR_FORMAT}`, fs.readdirSync(path.join(kept, `v${helper.EXTRACTOR_FORMAT}`)).sort()[1], 'lean-lens-extractor.json'), 'utf8'));
            assert.strictEqual(stamp.lean, 'lean-b');
            assert.strictEqual(stamp.toolchain, fs.realpathSync(path.join(toolchains, 'lean-b')));
            // The same name is another Lean once its programs changed (`stable` after a release, a
            // local build made again): it gets a new extractor. Unchanged, it uses the one it has.
            const builds = () => said.filter((line) => /Building the SubVerso extractor/.test(line)).length;
            assert.strictEqual(builds(), 2);
            assert.strictEqual((await elaborate('o/t', shaT, 'More.lean')).lean, 'lean-b');
            assert.strictEqual(builds(), 2, 'an unchanged Lean uses the extractor it has');
            assert.deepStrictEqual(builtBy(), ['lean-a by lean-a', 'lean-b by lean-b']);
            assert.strictEqual(read('used'), 'lean-a lean-b lean-b');
            script(path.join(toolchains, 'lean-b', 'bin', 'lake'), [...lakeLines, '# a later release']);
            assert.strictEqual((await elaborate('o/t', shaT, 'Again.lean')).lean, 'lean-b');
            assert.deepStrictEqual(builtBy(), ['lean-a by lean-a', 'lean-b by lean-b', 'lean-b by lean-b']);
            assert.strictEqual(builds(), 3);
            // When elan has no Lake for the Lean a project names, the run says so: it does not go
            // on with whichever `lake` is on the PATH (elan's own stand-in, which reads the
            // project's file again). And the Lake found has to be in a Lean installation.
            for (const [repo, sha, why] of [['o/u', shaU, /^elan could not find Lake for lean-c/], ['o/v', shaV, /is not in a Lean installation/]]) {
              h5.allow(repo);
              h5.start({ repo, sha, pr: null, paths: ['Sample.lean'] });
              while (h5.status(repo, sha).state === 'pending') await tick(20);
              assert.match(h5.fileState(repo, sha, 'Sample.lean').error || '', why);
              await h5.idle();
            }
            assert.deepStrictEqual(builtBy(), ['lean-a by lean-a', 'lean-b by lean-b', 'lean-b by lean-b']);
          } finally {
            process.env.PATH = pathBefore;
            h5.shutdown();
          }
        }

        // --- Lean in a codespace. The helper here hands the run to the same helper there, shows
        // its progress and keeps its results. `gh` is played by test/fixtures/fake-gh.mjs: its
        // codespace is a folder, and the helper "in" it runs on this machine.
        if (spawnSync('bash', ['--version']).status === 0) {
          const fakeDir = path.join(root, 'fake-gh');
          fs.mkdirSync(fakeDir);
          const before = process.env.FAKE_GH_DIR;
          process.env.FAKE_GH_DIR = fakeDir;
          const fakeState = () => JSON.parse(fs.readFileSync(path.join(fakeDir, 'state.json'), 'utf8'));
          const running = (pid) => { try { process.kill(pid, 0); return true; } catch { return false; } };
          const thereHome = path.join(fakeDir, 'homes', 'fake-1');
          const therePid = () => Number(fs.readFileSync(path.join(thereHome, '.lean-lens', 'helper.pid'), 'utf8'));
          let remotePort = null;
          try {
            remotePort = await new Promise((resolve) => {
              const probe = require('net').createServer();
              probe.listen(0, '127.0.0.1', () => { const { port } = probe.address(); probe.close(() => resolve(port)); });
            });
            const here = path.join(root, 'cache-here');
            const heard = [];
            const withCodespaces = (extra) => helper.createHelper(Object.assign({
              cacheDir: here, codespaces: cs.createCodespaces, gh: path.join(__dirname, 'fixtures', 'fake-gh.mjs'), remotePort, cloneBase, pollMs: 40, log: (message) => heard.push(message),
            }, extra));
            const finish = async (made, sha) => {
              for (let i = 0; made.status('o/r', sha).state === 'pending'; i++) { assert(i < 1500, `still pending: ${heard.join(' | ')}`); await tick(20); }
              await made.idle();
            };
            const h7 = withCodespaces({});
            await h7.remote.check();
            assert.strictEqual(JSON.parse(h7.handle('GET', '/status').body).runs, 'codespaces');
            assert.strictEqual(JSON.parse(h.handle('GET', '/status').body).runs, 'here');
            // One file the codespace already has a result for, and one Lean can't process.
            const there = path.join(thereHome, '.lean-lens', 'cache', 'data', `v${DATA_FORMAT_VERSION}`, 'o', 'r', commit, 'Sample.lean.json');
            fs.mkdirSync(path.dirname(there), { recursive: true });
            fs.writeFileSync(there, JSON.stringify(data));
            const begun = h7.start({ repo: 'o/r', sha: commit, pr: 7, paths: ['A.lean', 'Sample.lean'] });
            assert.strictEqual(begun.state, 'pending', 'answered at once, before any codespace exists');
            await finish(h7, commit);
            assert.strictEqual(h7.status('o/r', commit).state, 'done', h7.status('o/r', commit).error);
            assert.strictEqual(h7.fileState('o/r', commit, 'A.lean').error, 'This file is not inside a Lake project', 'the error from the codespace');
            assert.strictEqual(h7.fileState('o/r', commit, 'Sample.lean').state, 'ready');
            assert.strictEqual(JSON.parse(h7.readData('o/r', commit, 'Sample.lean')).hovers.length, data.hovers.length, 'the result is kept here');
            let fake = fakeState();
            assert.strictEqual(fake.codespaces.length, 1);
            assert.strictEqual(fake.codespaces[0].repository, 'o/r', 'a codespace on the repository being read');
            assert.strictEqual(fake.codespaces[0].displayName, 'Lean Lens r');
            assert.strictEqual(fake.codespaces[0].machine, 'basicLinux32gb');
            assert.strictEqual(h7.config.codespaces['o/r'].name, 'fake-1', 'and remembered');
            assert.notStrictEqual(h7.config.codespaces['o/r'].token, h7.config.token, 'the helper there has a token of its own');
            assert(heard.some((message) => message.includes('Creating a codespace for o/r')), heard.join(' | '));
            assert(heard.some((message) => message.includes('Setting up Lean in the codespace fake-1')) && heard.some((message) => message.includes('Done (2 files)')), heard.join(' | '));
            assert(!fs.existsSync(path.join(here, 'repos')), 'no copy of the repository on this machine');
            const pid = therePid();
            assert(running(pid));
            // Stopping the helper stops the codespace.
            h7.shutdown();
            assert.strictEqual(fakeState().codespaces[0].state, 'Shutdown');
            for (let i = 0; running(pid) && i < 200; i++) await tick(20);
            assert(!running(pid), 'the helper there has stopped');
            // The results are here: reading them needs no codespace.
            const h8 = withCodespaces({});
            assert.strictEqual(h8.fileState('o/r', commit, 'Sample.lean').state, 'ready');
            assert.strictEqual(fakeState().codespaces[0].state, 'Shutdown', 'a hover starts nothing');
            // A new run uses the same codespace, started again.
            h8.start({ repo: 'o/r', sha: commit, pr: null, paths: ['A.lean'] });
            await finish(h8, commit);
            fake = fakeState();
            assert.strictEqual(fake.codespaces.length, 1);
            assert.strictEqual(fake.codespaces[0].state, 'Available');
            assert.strictEqual(fake.calls.filter((call) => call === 'codespace create').length, 1, 'created once');
            assert.strictEqual(h8.config.codespaces['o/r'].token, h7.config.codespaces['o/r'].token);
            // --tidy-after 0: the codespace is stopped as soon as the run is over.
            h8.shutdown();
            const h9 = withCodespaces({ tidyMinutes: 0 });
            fs.rmSync(path.join(here, 'data'), { recursive: true, force: true });
            h9.start({ repo: 'o/r', sha: commit, pr: null, paths: ['Sample.lean'] });
            await finish(h9, commit);
            assert.strictEqual(h9.fileState('o/r', commit, 'Sample.lean').state, 'ready');
            assert.strictEqual(fakeState().codespaces[0].state, 'Shutdown', 'stopped when idle');
            h9.shutdown();
            // --keep-codespaces: left running.
            const h10 = withCodespaces({ keepCodespaces: true, tidyMinutes: 0 });
            h10.start({ repo: 'o/r', sha: commit, pr: null, paths: ['A.lean'] });
            await finish(h10, commit);
            h10.shutdown();
            assert.strictEqual(fakeState().codespaces[0].state, 'Available');
            // A helper still running in the codespace is left alone when the connection is made
            // again (this machine slept, or the helper here was started anew), and its runs with it.
            const stillThere = therePid();
            assert(running(stillThere), 'left running by --keep-codespaces');
            const sshBefore = fakeState().calls.filter((call) => call === 'codespace ssh').length;
            const h11 = withCodespaces({ keepCodespaces: true, keepAliveMs: 0, retryMs: 10 });
            fs.rmSync(path.join(here, 'data'), { recursive: true, force: true });
            h11.start({ repo: 'o/r', sha: commit, pr: null, paths: ['Sample.lean'] });
            await finish(h11, commit);
            assert.strictEqual(h11.fileState('o/r', commit, 'Sample.lean').state, 'ready');
            assert.strictEqual(therePid(), stillThere, 'the same helper, not a new one');
            // The connection goes (the forwarded port closes): the next request makes it again.
            spawnSync('pkill', ['-f', `ports forward ${remotePort}:`]);
            h11.start({ repo: 'o/r', sha: commit, pr: null, paths: ['A.lean'] });
            await finish(h11, commit);
            assert.strictEqual(h11.fileState('o/r', commit, 'A.lean').error, 'This file is not inside a Lake project');
            assert.strictEqual(therePid(), stillThere);
            // While a run lasts, the helper connects over ssh now and then: GitHub stops a codespace
            // nobody has connected to for 30 minutes, whatever is running in it.
            assert(fakeState().calls.filter((call) => call === 'codespace ssh').length > sshBefore + 2, 'two connections and at least one more to keep it alive');
            h11.shutdown();
            // Its own codespaces can be listed and deleted; nothing else is touched.
            fake = fakeState();
            fake.codespaces.push({ name: 'mine', displayName: 'my own work', repository: 'o/r', state: 'Available' });
            fs.writeFileSync(path.join(fakeDir, 'state.json'), JSON.stringify(fake));
            const spaces = cs.createCodespaces({ config: h10.config, save: () => {}, run: h10.remote.run, log: () => {}, gh: path.join(__dirname, 'fixtures', 'fake-gh.mjs') });
            assert.strictEqual((await spaces.ours()).map((space) => space.name).join(), 'fake-1');
            await spaces.remove('fake-1');
            assert.strictEqual(fakeState().codespaces.map((space) => space.name).join(), 'mine');
            assert.strictEqual(h10.config.codespaces['o/r'], undefined, 'and forgotten');
            // A repository that allows only a larger machine (mathlib4 does) gets that one, and the
            // log says so. A machine asked for by name is not swapped for another.
            fake = fakeState();
            fake.machines = ['standardLinux32gb', 'premiumLinux'];
            fs.writeFileSync(path.join(fakeDir, 'state.json'), JSON.stringify(fake));
            const h12 = withCodespaces({});
            h12.start({ repo: 'o/r', sha: commit, pr: null, paths: ['A.lean'] });
            await finish(h12, commit);
            assert.strictEqual(h12.status('o/r', commit).state, 'done', h12.status('o/r', commit).error);
            assert.strictEqual(fakeState().codespaces.find((space) => space.displayName === 'Lean Lens r').machine, 'standardLinux32gb');
            assert(heard.some((message) => message.includes('needs a larger codespace than the smallest: using standardLinux32gb')), heard.join(' | '));
            h12.shutdown();
            await spaces.remove(fakeState().codespaces.find((space) => space.displayName === 'Lean Lens r').name);
            const h13 = withCodespaces({ machine: 'largeLinux' });
            h13.start({ repo: 'o/r', sha: commit, pr: null, paths: ['A.lean'] });
            await finish(h13, commit);
            assert(/no such machine for the repository: largeLinux/.test(h13.status('o/r', commit).error), h13.status('o/r', commit).error);
            h13.shutdown();
            // GitHub may take long to set a codespace up (a repository's own dev container): the
            // helper waits. If that setup failed, GitHub starts the codespace in recovery mode,
            // where Lean cannot run: the helper says so, stops it, and names the way out.
            fake = fakeState();
            delete fake.machines;
            fake.slow = 3;
            fs.writeFileSync(path.join(fakeDir, 'state.json'), JSON.stringify(fake));
            const h14 = withCodespaces({ retryMs: 10 });
            h14.start({ repo: 'o/r', sha: commit, pr: null, paths: ['A.lean'] });
            await finish(h14, commit);
            assert.strictEqual(h14.status('o/r', commit).state, 'done', h14.status('o/r', commit).error);
            assert(heard.some((message) => message.includes('Waiting for GitHub to set up the codespace')), heard.join(' | '));
            h14.shutdown();
            fs.writeFileSync(path.join(root, 'recovery-reason'), 'Error code: 1302 (UnifiedContainersErrorFatalCreatingContainer)');
            process.env.LEAN_LENS_RECOVERY_FILE = path.join(root, 'recovery-reason');
            try {
              const h15 = withCodespaces({ retryMs: 10 });
              h15.start({ repo: 'o/r', sha: commit, pr: null, paths: ['A.lean'] });
              await finish(h15, commit);
              const refusal = h15.status('o/r', commit).error;
              assert(/recovery mode/.test(refusal) && /Error code: 1302/.test(refusal) && /--here o\/r/.test(refusal), refusal);
              assert.strictEqual(fakeState().codespaces.find((space) => space.displayName === 'Lean Lens r').state, 'Shutdown', 'not left running');
              h15.shutdown();
              // --here: that repository runs on this machine, whatever its codespace is like.
              const creations = fakeState().calls.filter((call) => call === 'codespace ssh').length;
              const h16 = withCodespaces({ here: ['o/r'], keepBuilds: true });
              h16.start({ repo: 'o/r', sha: commit, pr: null, paths: ['A.lean'] });
              await finish(h16, commit);
              assert.strictEqual(h16.fileState('o/r', commit, 'A.lean').error, 'This file is not inside a Lake project');
              assert(fs.existsSync(path.join(here, 'repos', 'o', 'r', 'A.lean')), 'its copy is on this machine');
              assert.strictEqual(fakeState().calls.filter((call) => call === 'codespace ssh').length, creations, 'and no codespace was touched');
              h16.shutdown();
              fs.rmSync(path.join(here, 'repos'), { recursive: true, force: true });
            } finally {
              delete process.env.LEAN_LENS_RECOVERY_FILE;
            }
            // Without the scope, it says what to run.
            fake = fakeState();
            fake.scope = false;
            fs.writeFileSync(path.join(fakeDir, 'state.json'), JSON.stringify(fake));
            await assert.rejects(withCodespaces({}).remote.check(), /gh auth refresh -h github\.com -s codespace/);
            await assert.rejects(withCodespaces({ gh: path.join(root, 'no-such-gh') }).remote.check(), /not installed/);
            assert.throws(() => withCodespaces({ machine: 'big; rm -rf' }), /Not a codespace machine name/);
          } finally {
            // Whatever happened above, no helper is left running "in a codespace", and no forwarding.
            if (typeof remotePort === 'number') spawnSync('pkill', ['-f', `ports forward ${remotePort}:`]);
            for (const name of fs.existsSync(path.join(fakeDir, 'homes')) ? fs.readdirSync(path.join(fakeDir, 'homes')) : []) {
              try { process.kill(Number(fs.readFileSync(path.join(fakeDir, 'homes', name, '.lean-lens', 'helper.pid'), 'utf8')), 'SIGKILL'); } catch { /* it has stopped */ }
            }
            if (before === undefined) delete process.env.FAKE_GH_DIR; else process.env.FAKE_GH_DIR = before;
          }
        }
      }
    } finally {
      fs.rmSync(root, { recursive: true, force: true });
    }

    // --- The worker: asks the helper, keeps a file's data once Lean has run.
    const send = (message) => new Promise((resolve) => workerListeners[0](message, {}, resolve));
    const calls = [];
    let fileAnswer = { state: 'missing' };
    context.URL = URL;
    context.AbortController = AbortController;
    context.fetch = async (url, init = {}) => {
      const u = new URL(url);
      if (u.host !== '127.0.0.1:5326') return { ok: false, status: 404, json: async () => null, text: async () => '' };
      const body = init.body ? JSON.parse(init.body) : null;
      calls.push({ path: u.pathname, body });
      if ((init.headers || {})['X-Lean-Lens-Token'] !== 'tok') return { ok: false, status: 401, json: async () => ({ error: 'no' }) };
      const answers = {
        '/file': body && body.path === 'Old.lean' ? { state: 'ready', data: { version: 1 } } : fileAnswer,
        '/run': { state: 'pending', phase: 'queued', message: 'Waiting for the previous run', done: 0, total: 2 },
        '/allow': { ok: true, allow: ['o/r'] },
        '/status': { ok: true, allow: ['o/r'] }
      };
      return { ok: true, status: 200, json: async () => answers[u.pathname] };
    };
    const settingsWith = (extra) => send({ action: 'SET_SETTINGS', settings: Object.assign({ enableHelper: true, helperUrl: 'http://127.0.0.1:5326', helperToken: 'tok' }, extra) });
    const fileRef = { owner: 'o', repo: 'r', pr: '7', sha: 'a'.repeat(40), side: 'right', path: 'Sample.lean', line: 4 };
    const hover = (extra = {}) => send(Object.assign({ action: 'EXACT_HOVER', fileRef, column: col(4, 'double', 1), columnEnd: col(4, 'double', 1) + 6, caret: col(4, 'double', 1) + 2 }, extra));
    try {
      await settingsWith({});
      let res = await hover();
      assert.strictEqual(res.state, 'missing');
      assert.strictEqual(res.repo, 'o/r');
      assert.strictEqual(res.sha, 'a'.repeat(40));
      assert.strictEqual(JSON.stringify(calls[0].body), JSON.stringify({ repo: 'o/r', sha: 'a'.repeat(40), path: 'Sample.lean' }));
      const run = await send({ action: 'HELPER_RUN', owner: 'o', repo: 'r', pr: '7', sha: 'a'.repeat(40), paths: ['Sample.lean', 'Other.lean'] });
      assert.strictEqual(run.state, 'pending');
      assert.strictEqual(JSON.stringify(calls[calls.length - 1]), JSON.stringify({ path: '/run', body: { repo: 'o/r', sha: 'a'.repeat(40), pr: 7, paths: ['Sample.lean', 'Other.lean'] } }));
      const allowed = await send({ action: 'HELPER_RUN', owner: 'o', repo: 'r', sha: 'a'.repeat(40), paths: ['Sample.lean'], allow: true });
      assert.strictEqual(allowed.state, 'pending');
      assert.strictEqual(calls[calls.length - 2].path, '/allow', 'allowing comes first');
      fileAnswer = { state: 'ready', data };
      res = await hover();
      assert.strictEqual(res.state, 'ready', 'asked again after a run was started');
      assert.strictEqual(res.token.typeSignature, 'double (n : Nat) : Nat');
      const before = calls.length;
      fileAnswer = { state: 'missing' };
      res = await hover({ fileRef: Object.assign({}, fileRef, { line: 5 }), column: col(5, 'unfold'), columnEnd: col(5, 'unfold') + 6, caret: col(5, 'unfold') });
      assert.strictEqual(res.goals.tactic, 'unfold double');
      assert.strictEqual(calls.length, before, 'a commit\'s file is fetched once');
      res = await hover({ fileRef: Object.assign({}, fileRef, { path: 'Old.lean' }) });
      assert.strictEqual(res.state, 'error', 'data in another format is not used');
      assert.strictEqual((await send({ action: 'TEST_HELPER', url: 'http://127.0.0.1:5326', token: 'tok' })).success, true);
      assert.strictEqual((await send({ action: 'TEST_HELPER', url: 'http://127.0.0.1:5326', token: 'bad' })).state, 'unauthorized');
      // Switched off: the helper is not contacted.
      await settingsWith({ enableHelper: false });
      const quiet = calls.length;
      assert.strictEqual((await hover()).state, 'off');
      assert.strictEqual(calls.length, quiet);
    } finally {
      delete context.fetch;
      await send({ action: 'SET_SETTINGS', settings: {} });
    }

    // --- The page: Lean's hover when it has one; its goals added to any hover; a run only on a click.
    const shown = [];
    const sentMessages = [];
    let exactAnswer = null;
    const pctx = {
      console, setTimeout, clearTimeout, location: { pathname: '/o/r/pull/7/changes' },
      document: { addEventListener: () => {}, getElementById: () => null, querySelectorAll: () => [], body: {} },
      Node: { ELEMENT_NODE: 1, TEXT_NODE: 3 }, MutationObserver: function () { this.observe = () => {}; },
      chrome: { runtime: { onMessage: { addListener: () => {} }, lastError: null, sendMessage: (message, cb) => {
        sentMessages.push(message);
        if (message.action === 'GET_SETTINGS') cb({ settings: { enableHelper: true } });
        else if (message.action === 'EXACT_HOVER') cb(exactAnswer && JSON.parse(JSON.stringify(exactAnswer)));
        else if (message.action === 'HELPER_RUN') cb({ state: 'pending', phase: 'queued', message: 'Waiting for the previous run' });
        else cb(null);
      } }, storage: { local: { get: (k, cb) => cb({}), set: () => {} } } }
    };
    pctx.window = pctx; pctx.self = pctx; pctx.addEventListener = () => {};
    pctx.VersoTooltipView = {
      isPinned: false, isVisible: () => true, clearHideTimer: () => {}, scheduleHide: () => {}, showLoading: () => {},
      show: (card, rect, shade, extras) => shown.push({ card, extras }),
      hide: () => shown.push({ hidden: true }),
      setExtras: (extras) => shown.push({ update: extras })
    };
    vm.createContext(pctx);
    for (const f of ['content/builtins_db.js', 'content/lean_tokenizer.js', 'content/lean_terms.js', 'content/binder_context.js', 'content/term_hover.js', 'content/pr_scanner.js', 'content/content.js']) {
      vm.runInContext(fs.readFileSync(path.join(__dirname, '..', f), 'utf8'), pctx);
    }
    const PI = pctx.VersoContentInternals;
    pctx.VersoBinderContext.fileRefFromDom = () => ({ owner: 'o', repo: 'r', pr: '7', sha: 'a'.repeat(40), side: 'right', path: 'Sample.lean', line: 5 });
    pctx.VersoBinderContext.contextFromDom = () => 'theorem double_eq (n : Nat) : double n = 2 * n := by\n  unfold double';
    const hoverToken = async (token, extra = {}) => {
      shown.length = 0;
      sentMessages.length = 0;
      PI.hovering(token);
      PI.triggerHoverLookup(Object.assign({ token, subToken: token, chainUpToCursor: token, fullChain: token, linePrefix: '  ', lineSuffix: '',
        boundingRect: {}, shade: [], textNode: {}, column: 2, columnEnd: 2 + token.length, caret: 3 }, extra));
      await tick(5);
      return shown[shown.length - 1];
    };
    const afterUnfold = { at: false, tactic: 'unfold double', goals: ['n : Nat\n⊢ n + n = 2 * n'] };
    // Lean has a hover for the token: that is the card, with the proof state under it.
    exactAnswer = { state: 'ready', repo: 'o/r', sha: 'a'.repeat(40), lean: 'leanprover/lean4:v4.35.0', messages: [], goals: afterUnfold,
      token: { name: 'double', kind: 'const', typeSignature: 'double (n : Nat) : Nat', docstring: 'Doubles a number.', definedHere: false } };
    let last = await hoverToken('double');
    assert.strictEqual(last.card.source, 'lean');
    assert.strictEqual(last.card.typeSignature, 'double (n : Nat) : Nat');
    assert(last.card.sourceUrl.endsWith('find/?pattern=double#doc'), last.card.sourceUrl);
    assert.strictEqual(last.extras.goals.tactic, 'unfold double');
    assert.strictEqual(sentMessages.filter((m) => m.action === 'EXACT_HOVER').length, 1);
    assert.strictEqual(sentMessages.find((m) => m.action === 'EXACT_HOVER').column, 2);
    assert.strictEqual(sentMessages.find((m) => m.action === 'EXACT_HOVER').chain, 'double', 'the dotted name goes along');
    assert(!sentMessages.some((m) => m.action === 'LOOKUP_TOKEN'), 'no estimate is looked up');
    // A field shown in its place: the card is titled by the chain.
    exactAnswer = Object.assign({}, exactAnswer, { token: { name: 'Iff.mp', display: 'h.mp', kind: 'const', typeSignature: 'h.mp : p → q', docstring: 'd' } });
    last = await hoverToken('mp', { chainUpToCursor: 'h.mp', chainColumn: 2, column: 4, columnEnd: 6, caret: 5 });
    assert.strictEqual(last.card.name, 'h.mp');
    assert(last.card.sourceUrl.endsWith('find/?pattern=Iff.mp#doc'), last.card.sourceUrl);
    assert.strictEqual(JSON.stringify([sentMessages[0].chain, sentMessages[0].chainColumn]), JSON.stringify(['h.mp', 2]));
    // A keyword Lean has no docs for: the proof state alone; with no state either, nothing.
    exactAnswer = Object.assign({}, exactAnswer, { token: null, goals: { at: true, tactic: 'by', goals: ['n : Nat\n⊢ double n = 2 * n'] } });
    last = await hoverToken('by', { isKeyword: true });
    assert.strictEqual(last.card, null, 'the goals-only card');
    assert.strictEqual(last.extras.goals.at, true);
    exactAnswer = Object.assign({}, exactAnswer, { goals: null });
    assert.strictEqual((await hoverToken('by', { isKeyword: true })).hidden, true);
    // On an operator Lean's data has documentation only: the estimate (the term and its type) is
    // kept, with Lean's proof state added.
    exactAnswer = { state: 'ready', repo: 'o/r', sha: 'a'.repeat(40), lean: 'leanprover/lean4:v4.35.0', messages: [], goals: afterUnfold,
      token: { name: '+', kind: 'syntax', typeSignature: '', docstring: '`a + b` computes the sum of `a` and `b`.' } };
    pctx.VersoBinderContext.termTypeOf = async () => 'ℕ';
    pctx.VersoBinderContext.termDisplay = () => 'n + n';
    last = await hoverToken('⟪term⟫ n + n', { kind: 'term', termText: 'n + n', termNode: {}, termSource: 'n + n' });
    assert.strictEqual(last.card.source, 'term', 'the estimated term hover');
    assert.strictEqual(last.card.typeSignature, 'n + n : ℕ');
    assert.strictEqual(last.extras.goals.tactic, 'unfold double');
    assert.strictEqual(last.extras.helper.state, 'ready');
    // A later answer for an earlier hover of a token with the same text is dropped.
    exactAnswer = { state: 'ready', repo: 'o/r', sha: 'a'.repeat(40), lean: 'l', messages: [], goals: null,
      token: { name: 'hx', kind: 'variable', typeSignature: 'hx : 0 < x', docstring: '' } };
    const answers = [];
    const realSend = pctx.chrome.runtime.sendMessage;
    pctx.chrome.runtime.sendMessage = (message, cb) => { if (message.action === 'EXACT_HOVER') answers.push(cb); else realSend(message, cb); };
    shown.length = 0;
    PI.hovering('hx');
    const hoverAgain = (column) => PI.triggerHoverLookup({ token: 'hx', subToken: 'hx', chainUpToCursor: 'hx', fullChain: 'hx', linePrefix: '  ', lineSuffix: '',
      boundingRect: {}, shade: [], textNode: {}, column, columnEnd: column + 2, caret: column });
    hoverAgain(2);
    hoverAgain(20);
    answers[1]({ state: 'ready', lean: 'l', messages: [], goals: null, token: { name: 'hx', kind: 'variable', typeSignature: 'hx : second', docstring: '' } });
    answers[0]({ state: 'ready', lean: 'l', messages: [], goals: null, token: { name: 'hx', kind: 'variable', typeSignature: 'hx : first', docstring: '' } });
    await tick(5);
    assert.strictEqual(shown.map((x) => x.card.typeSignature).join('|'), 'hx : second', 'only the hover in progress is shown');
    pctx.chrome.runtime.sendMessage = realSend;
    // Lean has not run: the estimate, with a button. Lean starts only when it is pressed.
    exactAnswer = { state: 'missing', repo: 'o/r', sha: 'a'.repeat(40) };
    last = await hoverToken('simp');
    assert.strictEqual(last.card.source, 'builtin');
    assert.strictEqual(last.extras.helper.state, 'missing');
    assert(!sentMessages.some((m) => m.action === 'HELPER_RUN'), 'hovering never starts Lean');
    last.extras.helper.run();
    await tick(5);
    const runMessage = sentMessages.find((m) => m.action === 'HELPER_RUN');
    assert.strictEqual(JSON.stringify([runMessage.owner, runMessage.repo, runMessage.pr, runMessage.sha, runMessage.paths, runMessage.allow]),
      JSON.stringify(['o', 'r', '7', 'a'.repeat(40), ['Sample.lean'], false]));
    assert.strictEqual(shown[shown.length - 1].update.helper.state, 'pending', 'the open hover shows the run');
    // A repository the helper may not run yet: the button allows it, then runs.
    exactAnswer = { state: 'not_allowed', repo: 'o/r', sha: 'a'.repeat(40) };
    last = await hoverToken('simp');
    last.extras.helper.run();
    await tick(5);
    assert.strictEqual(sentMessages.find((m) => m.action === 'HELPER_RUN').allow, true);
    // The helper switched off: nothing is asked of it.
    PI.setSettings({ enableHelper: false });
    last = await hoverToken('simp');
    assert.strictEqual(last.card.source, 'builtin');
    assert.strictEqual(last.extras, null);
    assert(!sentMessages.some((m) => m.action === 'EXACT_HOVER'));
    PI.hovering(null);

    // --- The tooltip: the proof state, Lean's messages and the helper's status row.
    const parts = {};
    const part = () => ({ innerHTML: '', textContent: '', href: '', className: '', addEventListener: () => {},
      classList: { names: new Set(), add(n) { this.names.add(n); }, remove(n) { this.names.delete(n); }, toggle(n, on) { if (on) this.names.add(n); else this.names.delete(n); }, contains(n) { return this.names.has(n); } } });
    const view = tooltipView;
    view.container = Object.assign(part(), { querySelector: (selector) => {
      if (!parts[selector]) parts[selector] = Object.assign(part(), { parentElement: part(), querySelector: () => part() });
      return parts[selector];
    } });
    view.show(null, null, null, { lean: 'leanprover/lean4:v4.35.0', goals: afterUnfold, messages: [{ severity: 'error', text: 'unsolved <goals>' }], helper: { state: 'ready' } });
    assert.strictEqual(parts['#verso-kind'].textContent, 'goal');
    assert(parts['#verso-goals-title'].innerHTML.includes('After <code class="verso-inline-code">unfold double</code>'), parts['#verso-goals-title'].innerHTML);
    assert(parts['#verso-goals-body'].innerHTML.includes('n + n'), parts['#verso-goals-body'].innerHTML);
    assert(parts['#verso-messages'].innerHTML.includes('verso-message-error') && parts['#verso-messages'].innerHTML.includes('unsolved &lt;goals&gt;'));
    assert.strictEqual(parts['#verso-footer-source'].textContent, 'Lean 4.35.0 · run on this machine');
    assert(parts['#verso-helper-bar'].classList.contains('verso-hidden'), 'no status row on Lean\'s own card');
    // A definition with a proof state is two columns (the state on the left); a proof state
    // alone, or a definition alone, is one.
    assert(!view.container.classList.contains('verso-two-col'), 'a proof state alone');
    view.show({ name: 'double', kind: 'const', source: 'lean', typeSignature: 'double (n : Nat) : Nat', docstring: 'Doubles a number.' }, null, null,
      { goals: afterUnfold, messages: [], helper: { state: 'ready' } });
    assert(view.container.classList.contains('verso-two-col'), 'a definition with a proof state');
    view.show({ name: 'simp', kind: 'tactic', source: 'builtin', typeSignature: 'simp', docstring: 'd' }, null, null,
      { goals: null, messages: [], helper: { state: 'missing', run: () => {} } });
    assert.strictEqual(parts['#verso-helper-text'].textContent, 'Estimated. Lean has not run on this file.');
    assert.strictEqual(parts['#verso-helper-btn'].textContent, 'Run Lean');
    assert(!parts['#verso-helper-btn'].classList.contains('verso-hidden'));
    assert(parts['#verso-goals'].classList.contains('verso-hidden'));
    assert(!view.container.classList.contains('verso-two-col'), 'a definition alone');
    view.setExtras({ goals: { at: false, tactic: 'omega', goals: [] }, messages: [], helper: { state: 'pending', phase: 'elaborating', message: 'Elaborating 3 files', done: 1, total: 3 } });
    assert.strictEqual(parts['#verso-helper-text'].textContent, 'Lean is running: Elaborating 3 files (1/3)');
    assert(parts['#verso-helper-btn'].classList.contains('verso-hidden'));
    assert(parts['#verso-goals-body'].innerHTML.includes('No goals'));
    assert.strictEqual(view.helperStatus({ state: 'ready' }, true).text, "Estimated: Lean's data has no hover for this spot.");
    // Lean's docstrings are hard-wrapped Markdown: line ends are spaces, also inside a list item.
    const wrapped = view.renderMarkdown('The `simp` tactic uses lemmas\nto simplify. Variants:\n- `simp` simplifies using\n  tagged lemmas.\n- `simp [h]` uses `h`\n  too.\n\nMore.', { softWrap: true });
    assert.strictEqual(wrapped, '<p>The <code class="verso-inline-code">simp</code> tactic uses lemmas to simplify. Variants:</p>' +
      '<ul><li><code class="verso-inline-code">simp</code> simplifies using tagged lemmas.</li><li><code class="verso-inline-code">simp [h]</code> uses <code class="verso-inline-code">h</code> too.</li></ul><p>More.</p>');
    assert(view.renderMarkdown('one\ntwo').includes('one<br>two'), 'other docstrings keep their line breaks');
    assert.strictEqual(view.helperStatus({ state: 'ready' }, false), null);
    assert.strictEqual(view.helperStatus({ state: 'not_allowed', repo: 'o/r' }, true).button, 'Allow and run');
    assert.strictEqual(view.helperStatus({ state: 'off' }, true), null);
  })());
}
console.log("   ✓ Real Lean data verified (asynchronous checks follow).\n");

// Firefox: the background runs as an event page from `background.scripts`, with no importScripts.
asyncChecks.push(import('../scripts/build-firefox.mjs').then(({ firefoxManifest }) => {
  const chromeManifest = JSON.parse(fs.readFileSync(path.join(__dirname, '..', 'manifest.json'), 'utf8'));
  const ff = firefoxManifest(chromeManifest);
  assert(!ff.background.service_worker && ff.browser_specific_settings.gecko.id, 'Firefox manifest uses an event page and has an id');
  assert.strictEqual(chromeManifest.background.service_worker, 'background/service_worker.js', 'the Chrome manifest is left as it is');
  // The event page loads what the service worker imports, then the worker itself.
  const imported = [...workerSrc.matchAll(/importScripts\(([^)]*)\)/g)]
    .flatMap(m => [...m[1].matchAll(/'([^']+)'/g)].map(s => path.posix.join('background', s[1])));
  assert.deepStrictEqual(ff.background.scripts, [...imported, 'background/service_worker.js'], 'Firefox background scripts match importScripts');
  const listeners = [];
  const fctx = {
    console, setTimeout, clearTimeout, setInterval, clearInterval, fetch: () => Promise.reject(new Error('offline')),
    AbortController, URL, URLSearchParams, TextEncoder, TextDecoder,
    chrome: { runtime: { onMessage: { addListener: (fn) => listeners.push(fn) } }, storage: { local: { get: (k, cb) => cb({}), set: (v, cb) => cb && cb(), remove: (k, cb) => cb && cb() } } }
  };
  fctx.window = fctx; fctx.self = fctx; fctx.globalThis = fctx;
  vm.createContext(fctx);
  for (const f of ff.background.scripts) vm.runInContext(fs.readFileSync(path.join(__dirname, '..', f), 'utf8'), fctx, { filename: f });
  assert(fctx.VersoBinderContext && fctx.LeanPRScanner, 'shared scripts are reachable from the event page');
  assert.strictEqual(listeners.length, 1, 'the event page listens for messages');
  console.log("   ✓ Firefox build verified.\n");
}));

// 23. A file's outline, `#where` at a declaration, and where a declaration might belong.
console.log("23. Testing the file outline, #where and placement hints...");
{
  loadScript('content/lean_outline.js');
  const O = context.LeanOutline;
  const same = (a, b, m) => assert.strictEqual(JSON.stringify(a), JSON.stringify(b), m);
  const src = fs.readFileSync(path.join(__dirname, 'fixtures', 'Outline.lean'), 'utf8');
  const entries = O.outline(src);
  same(entries.map((e) => `${e.line}:${e.kind}${e.declKind ? ' ' + e.declKind : ''}${e.name ? ' ' + e.name : ''}`), [
    '1:import', '6:open', '8:namespace TopologicalSpace', '10:variable', '13:section Open', '15:variable', '16:include',
    '20:decl theorem isOpen_foo', "22:decl theorem isOpen_foo'", '25:end Open', '28:decl theorem isClosed_bar',
    '31:decl lemma card_eq', '33:decl def f', '37:end TopologicalSpace', '39:decl theorem _root_.foo_bar'],
  'commands and declarations, not what is in comments');
  const byLine = (l) => entries.find((e) => e.line === l);
  same([byLine(20).fullName, byLine(39).fullName], ['TopologicalSpace.isOpen_foo', 'foo_bar'], 'names with their namespaces');
  same([byLine(20).startLine, byLine(22).endLine, byLine(33).endLine], [19, 23, 35], 'attributes, indented proofs and match arms belong to the declaration');
  same(byLine(28).prefixes, ['open Topology'], '`open … in` applies to the next declaration alone');
  same(byLine(31).prefixes, ['omit [TopologicalSpace X]']);
  same([byLine(15).depth, byLine(20).depth, byLine(25).depth, byLine(39).depth], [2, 2, 1, 0], 'depth in namespaces and sections');
  assert.strictEqual(byLine(10).text, 'variable {X : Type*} [TopologicalSpace X]\n  {s t : Set X}', 'a command\'s continuation lines');

  // What is in force at a line, like `#where`.
  const at20 = O.contextAt(src, 20, entries);
  assert.strictEqual(at20.namespace, 'TopologicalSpace');
  assert.strictEqual(at20.decl.name, 'isOpen_foo');
  same(at20.commands.map((c) => c.kind), ['open', 'variable', 'variable', 'include']);
  assert.strictEqual(O.whereText(at20), [
    'open Set Filter  -- line 6',
    'namespace TopologicalSpace  -- line 8',
    '  variable {X : Type*} [TopologicalSpace X]  -- line 10',
    '    {s t : Set X}',
    '  section Open  -- line 13',
    '    variable (hs : IsOpen s)  -- line 15',
    '    include hs  -- line 16'].join('\n'));
  // After `end Open`, the section's `variable` and `include` are gone; `open … in` shows.
  same(O.contextAt(src, 28, entries).commands.map((c) => c.line), [6, 10]);
  assert(O.whereText(O.contextAt(src, 28, entries)).endsWith('open Topology in  -- line 27'));
  assert.strictEqual(O.whereText(O.contextAt(src, 39, entries)), 'open Set Filter  -- line 6', 'after the namespace closes');
  assert.strictEqual(O.contextAt(src, 3, entries).decl, null, 'not in a declaration');

  // Mathlib's module system: `module` and `public import` lines are the header; a section's
  // `#where` line is written as in the file.
  const moduleSrc = ['module', '', 'public import Mathlib.A', 'public meta import Mathlib.B', 'import Mathlib.C', '',
    '@[expose] public section', '', 'noncomputable section', '', 'namespace Real -- the reals', '',
    'theorem t : True := trivial', '', 'end Real', ''].join('\n');
  const modEntries = O.outline(moduleSrc);
  same(modEntries.filter((e) => e.kind === 'import').map((e) => e.line), [1, 3, 4, 5]);
  assert.strictEqual(O.whereText(O.contextAt(moduleSrc, 13, modEntries)),
    '@[expose] public section  -- line 7\n  noncomputable section  -- line 9\n    namespace Real  -- line 11');
  // Where a declaration belongs: next to those most like it.
  const words = O.nameWords("Set.isOpen_iff'");
  same(words, ['set', 'is', 'open', 'iff']);
  const pr = [
    'theorem isOpen_iff_nhds : A := x',
    'theorem mul_comm_aux : B := y',
    'theorem foo_le : C := z',
    'theorem card_pos : D := w',
    "theorem foo_le' : C := z",
    'theorem continuous_add : E := x',
    'theorem isClosed_iff_nhds : A := x', ''].join('\n');
  const hints = O.placementHints(pr, new Set([2, 4, 7]));
  same(hints.map((h) => h.hints.map((x) => x.kind)), [[], ['split'], ['far']]);
  assert(hints[1].hints[0].text.includes('`foo_le` (line 3) from `foo_le\'` (line 5)'), hints[1].hints[0].text);
  assert(hints[2].hints[0].text.startsWith('Most like `isOpen_iff_nhds` at line 1'), '`isClosed` and `isOpen` are alike: ' + hints[2].hints[0].text);
  const together = pr.replace('theorem card_pos : D := w\n', '');
  same(O.placementHints(together, new Set([3]))[0].hints, [], '`foo_le` next to `foo_le\'` is where it belongs');
  same(O.placementHints(together, new Set([3]))[0].similar.map((x) => x.name), ["foo_le'"]);
  // The lines a pull request adds.
  same([...O.addedLines('a\nb\nc', 'a\nx\nb\nc\ny')], [2, 5]);
  same([...O.addedLines(null, 'a\nb')], [1, 2], 'a new file is all new');
  same([...O.addedLines('a\nb', 'a\nb')], []);

  // Through the worker: `#where` and the hints for a declaration the pull request adds.
  // (In a worker of its own, whose files are these two texts.)
  const base = pr.split('\n').filter((l, i) => ![1, 3, 6].includes(i)).join('\n');
  const wctx = {
    console, setTimeout, clearTimeout, AbortController, URL, fetch: () => Promise.reject(new Error('offline')),
    chrome: { runtime: { onMessage: { addListener: () => {} } }, storage: { local: { get: (k, cb) => cb({}), set: (v, cb) => cb && cb(), remove: (k, cb) => cb && cb() } } }
  };
  wctx.self = wctx; wctx.window = wctx; wctx.globalThis = wctx;
  vm.createContext(wctx);
  for (const f of ['content/lean_terms.js', 'content/binder_context.js', 'content/pr_scanner.js', 'content/lean_outline.js', 'background/exact_data.js', 'background/service_worker.js']) {
    vm.runInContext(fs.readFileSync(path.join(__dirname, '..', f), 'utf8'), wctx, { filename: f });
  }
  wctx.getFileText = (ref) => Promise.resolve(ref.side === 'left' ? base : pr);
  asyncChecks.push((async () => {
    const ref = { owner: 'o', repo: 'r', pr: '1', sha: 'h', baseSha: 'b', side: 'right', path: 'A.lean' };
    const where = await wctx.declWhere(Object.assign({}, ref, { line: 4 }));
    assert.strictEqual(where.decl.name, 'card_pos');
    assert.strictEqual(where.isNew, true);
    same(where.hints.map((h) => h.kind), ['split']);
    const old = await wctx.declWhere(Object.assign({}, ref, { line: 3 }));
    assert.strictEqual(old.isNew, false);
    same(old.hints, [], 'no hints for what was there before');
    const file = await wctx.fileOutline(ref);
    same(file.added, [2, 4, 7]);
    same(file.hints.map((h) => h.line), [4, 7]);
  })());
}
console.log("   ✓ Outline, #where and placement hints verified.\n");

Promise.all(asyncChecks).then(() => {
  console.log("   ✓ Rewrite replay verified.\n");
  console.log("==================================================");
  console.log("  ALL TESTS PASSED SUCCESSFULLY (100% OK)");
  console.log("==================================================");
}, (err) => {
  console.error(err);
  process.exit(1);
});
