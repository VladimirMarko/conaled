# FDSA-XL01 — Shared logarithm bounds: frozen source scope

Recorded 2026-11-03, before source edits. This supplements the full governing
REQUEST.md and existing book inventories; it does not replace or narrow them.
The whole book, all27 chapters and Appendices A–C remain required. This scope
is a genuine shared dependency of splay and pairing analyses, not activation
or acceptance of either chapter.

## Original base, input reports and validation boundary

Original source/review base:
`07e480f6ec9958d4975bb90151005b84f2907614` (repaired Chapter1 candidate).
Proposed local branch: work/fdsa-logarithm-bounds.
Proposed isolated source checkout: conaled-logarithm-bounds.
The base is unaccepted; C1 attempt3 remains the sole compiler/checker.
Do not touch its sources, outputs, guards, toolchain or dependencies.

Read the complete stopped source/API/case reports and root assessment:

- research/logarithm-bounds-source-preflight.md: 30,310 bytes /427 lines,
  SHA-256 f7891e3ccbe07e56499f36c52d2024246758ff6a127cdf9b576f7445e5e4ae73.
- research/logarithm-bounds-api-preflight.md: 32,941 bytes /322 lines,
  SHA-256 d013d148aea4b7949f7e8c66a7fed3ef32456565073453d1d3cabdf8fa357a5c.
- research/logarithm-bounds-case-preflight.md: 32,523 bytes /536 lines,
  SHA-256 c46b9bba5a4d1d38b1ec03fa2ce55ca41b254be47950c693c577d9d6de9aa270.
- reviews/logarithm-bounds-preflight-assessment.md.

Preserve the initial report snapshots, citation corrections and all earlier
source/validation findings. Source-level proof routes are not compiled terms.
The selected source scope has exactly five paths:

1. New Applications/Arithmetic/LogarithmBounds.lean.
2. New Examples/LogarithmBounds.lean.
3. New docs/research/fdsa-logarithm-bounds.md.
4. Additive section in docs/research/fdsa-reconstruction-map.md.
5. Appended `import Examples.LogarithmBounds` in SquareApplications.lean.

All other paths, prior map content and prior public imports remain unchanged.
No source file is selected merely because a support theory imports it. No
new carrier, logarithm definition, rank type, typeclass, resource executor,
generic tree fold, potential cache or accounting framework is selected.

## Core public arithmetic claims

Use namespace Arithmetic.LogarithmBounds and the pinned ordinary `Real.logb`.
The two public statements are:

```lean
theorem logb_two_sum_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.logb 2 x + Real.logb 2 y + 2 ≤ 2 * Real.logb 2 (x + y)

theorem logb_two_sum_strict {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1 + Real.logb 2 x + Real.logb 2 y < 2 * Real.logb 2 (x + y)
```

The first is Lemmas_log.ld_sum_inequality / C23-046; the second is
ld_ld_1_less / C21-074. Derive the second from the first. Inputs may be any
positive Reals, including values below1. Do not add >=1, distinctness, Nat,
tree, payload or order premises. Do not weaken positivity, change either
constant, make the sharp inequality strict, or silently generalize its base.

Use existing Mathlib multiplication/power/monotonicity laws and ordinary
arithmetic. A direct certificate is `(x-y)^2 >= 0`, hence
`4*x*y <= (x+y)^2`. Explicitly discharge positive/nonzero log arguments.
The core may have small private proof support; do not export wrappers for
existing log identities, casts, positivity, monotonicity or nonnegativity.
No Jensen, weighted-mean or finite-probability framework is required.

Normal autoImplicit/warning discipline and kernel-safe proofs apply. No new
axiom, admission, unsafe or partial definition, native_decide or skipped
kernel checking is allowed. A missing elaboration result must be reported as
unvalidated; do not invent a compiler failure or weaken a statement to fit
an uncompiled proof guess.

## Connected cases and independently fixed expectations

Develop cases alongside the two public results, using the existing EDD
workflow. A successful bound case must actually consume the intended public
result; independent value equalities and false-overclaim witnesses have their
own role and need not call a theorem whose hypotheses they violate. Do not
claim EDD green before compilation/full gates. Retain these selected cases:

1. **Canonical external-leaf observations.** For arbitrary
   `l : BinaryTree α` and `r : BinaryTree β` in independent universes,
   instantiate both public results at their Real-cast `numLeaves`. Use pinned
   Mathlib.Data.Tree.Basic positivity/count laws; no shared-tree draft import
   is needed. When labels agree and a root label is supplied, relate the sum
   to the existing node's leaf count. No balance, cache, search order,
   inhabitance or decidable payload equality is assumed. Retain nil over
   Empty and the pair of singleton children: leaf counts1,1 give sharp2=2
   and strict1<2; counts2,2 give sharp4=4 and strict3<4. These are scalar
   substitutions, not full splay branches. In particular nil,nil does not
   satisfy every nonempty premise of the source zig-zig branch.

2. **Pairing first-pass substitution and cancellation.** For arbitrary
   natural child sizes n1,n2 and suffix size m, cast before Real arithmetic
   and apply the sharp result at `(n1+n2+1,m+1)`. The exact target uses
   `n1+n2+m+2`. Also check the source's scalar intermediate cancellation:
   `L(n1+n2+1)-L(n2+m+1)+2*L(m+1)-k+2` is at most
   `2*L(n1+n2+m+2)-L(n2+m+1)+L(m+1)-k`, then at most
   `2*L(n1+n2+m+2)-k`; k is a Real scalar standing for the already-cast
   suffix length. Here L z denotes Real.logb 2 z only in this explanatory text.
   At n1=n2=m=0, the sharp step is2<=2; the printed +1 replacement would
   assert2<=0. Preserve that checked counterexample and the corrected step
   as the existing C23-052 disposition. The final Lemma23.2 target is
   unchanged. No heap, forest, pass operation or cost theorem is invented.

3. **Sharpness and positive values below1.** Connect both public results
   at x=y=1 and x=y=1/4. Use exact power/inverse identities, not numerical
   approximations. At the quarter pair the sharp expression is -2=-2 and
   the strict expression -3<-2. The unit pair witnesses failure of strict
   +2 or any uniformly larger additive constant. At x=0,y=1/4 the sharp
   nonnegative-input overclaim is0<=-4; at x=0,y=1 the sharp and strict
   overclaims are2<=0 and1<0. Keep a compact checked counterexample rather
   than introducing a total-log domain framework.

4. **Direct existing-library reuse, without core aliases.** Include a
   bounded example of the skew weaker inequality for arbitrary b>1 and
   positive Real inputs, proved from the two existing monotonicity calls.
   Apply that proof route to canonical leaf counts and the positive shifted
   sum `ell1+ell2-1`; show the three-log scalar combination bounded by three
   times the sum log. It is the arithmetic component of C22-056/057, not
   the actual merge/spine/Int-cost proof. Include the empty-tree scalar
   boundary. For the binary pairing child-size substitution, use arbitrary
   natural child counts (including zero), prove the stronger product bound
   without +1 directly from existing APIs, and retain the source's weaker
   +1 conclusion. Neither example changes any operation tariff or advertised
   algorithm constant. Do not add source-name wrappers to the core.

5. **Arithmetic domain distinctions.** Retain a compact exact check of
   Nat subtraction versus Real subtraction at zero and explain the actual
   non-underflow condition used by positive leaf counts. A base4/unit-input
   witness distinguishes the fixed sharp constant2 from general bases; a
   base1/2 witness distinguishes increasing-log use from decreasing bases.
   These are counterexamples to overclaims, not new generalized core APIs.

The full independent case report remains review evidence. Its other optional
calculations do not automatically become exports or additional implementations.
In particular the weighted singleton and boundary-credit calculation explain
future premises; they do not select a weighted tree or import XP01 here.

## Documentation, provenance and preserved chapter work

The new note must state the exact public laws, all selected independent
expected values, their actual public-law connections, the pinned APIs and
current uncompiled status. Identify the primary book/companion statements
and actual live consumer sites. Keep source facts separate from proposed
Lean API choices and from mathematical/compilation evidence.

Pin the July27,2026 book digest and the supporting dated archive
`https://isa-afp.org/release/afp-Amortized_Complexity-2026-10-26.tar.gz`
(31,633 bytes, SHA-256
d853a2fbf5644b5515847398dda6f9b65b203532ae608ad99d28b8f7a571442a).
Include the exact Lemmas_log identity and relevant inspected companion
identities/consumer locations from the final source report. Do not identify
this later supporting archive as the manuscript's generating revision or
reuse the unrelated Isabelle tree-theory revision. Include the complete
1842-byte AFP-LICENSE notice (SHA-256
9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd)
verbatim, with accurate authorship and no manuscript redistribution. Link
this provenance from the new Lean module. Preserve distinct Mathlib licensing.

Account explicitly for all four Lemmas_log statements and the skew helper:
the two core laws, direct shifted-product/skew reuse, and the exact
`x,y>=2` shifted-minus-one source helper without a demonstrated named
consumer. Do not claim its hypotheses are individually minimal or that it
has been formalized by this scope. Keep all original book obligations.

Explain the actual splay external-leaf, binary pairing node-count and
list/forest sibling-suffix potential offsets, and the unweighted meaning of
Splay_Tree_Analysis_Optimal. Explain why positive arguments alone do not give
nonnegative potential. The separate weighted/static-optimality claims,
source-specific cost models, signed accounting and initial/final credits,
multiple-input histories, all algorithms, exercises and conjecture statements
remain with their chapters. Existing XP01 is later reusable infrastructure,
not a dependency accepted by these scalar proofs.

The map addition must name C21-074, C23-046 and the scalar C23-052 connection
without marking whole rows or chapters accepted. Record direct-reuse support
for the relevant C22 arithmetic and binary-pairing child estimate, and all
remaining algorithm obligations. Append a public example import. Preserve
all old map bytes/imports, C1 findings and prior validation history.

## Ownership, source release and eventual acceptance

Root owns the exact baseline capture, requirements, public import, tracker,
source readback/commit and durability checkpoints. Tentative source ownership:
architecture owns the new core, rotation_cases owns the new example file,
book_inventory owns the new note and additive map section. Authors first read
this complete freeze, confirm readiness or report a concrete obstruction,
and stop. No source edit is released by this requirements file alone.

After successful exposed/saved pre-code checkpoint and root's immediate exact
baseline recheck, a separate release may permit only those disjoint source
writes. No compiler/checker/project hash helper, active build output access,
cache/performance action, ref/index/worktree change or final-review dispatch
is part of author release. Keep existing source snapshots and findings.

After repaired C1 is accepted and this unit is actually selected for
integration, an immutable integrated candidate must pass applicable focused
builds, full ordinary guarded candidate verification (or fresh if a concrete
unchanged policy trigger applies), both integrity phases, complete import
coverage and exhaustive transitive axiom audit. Both independent Standards
and Spec reviews must cover the full original five-path scope and frozen
requirements, with all findings retained. Root must immediately verify the
matching approved candidate before acceptance and expose/save its checkpoint.

The same idle isolated normal-cache review checkout may be used as already
specified by the shared integration plan; no new cold checkout or cache
transplant is authorized. A draft, source assessment, focused pass, commit,
checkpoint or dependency ancestry is not acceptance. Chapter1 stays active;
the exact initial C2 prefix remains c80eec92f5458eccfd1c34c8314d666c2a1e3847
after repaired C1 acceptance. No chapter, appendix or shared unit is accepted.
