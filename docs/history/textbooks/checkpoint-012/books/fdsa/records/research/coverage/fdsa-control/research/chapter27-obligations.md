# Chapter 27: Alpha-Beta Pruning — source obligations and reuse limits

Research date: 2026-11-02. Local ticket: `FDSA-027`.

**State: queued; source preparation only.** This inventory changes no Lean
code, build, ticket state, acceptance decision or remote resource. A row is
a future checked obligation or an explicitly classified source item, not
evidence that the chapter has been formalized. Sequential chapter order
remains the parent's responsibility.

## Sources and inspected pins

| Source | Inspected identity |
|---|---|
| Book | Tobias Nipkow, Chapter27, printed pp.319–340, PDF pages325–346, July27,2026 version. Official PDF <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. |
| Direct chapter link | <https://isa-afp.org/browser_info/current/AFP/Alpha_Beta_Pruning/Alpha_Beta_Lattice.html>. The current browser URL is mutable. Entry <https://isa-afp.org/entries/Alpha_Beta_Pruning.html>, Tobias Nipkow, published June13,2024. |
| Dated companion | <https://isa-afp.org/release/afp-Alpha_Beta_Pruning-2026-10-26.tar.gz>, 38,328 bytes, SHA-256 `e7fb06e7a801d06323171a90741e7a65a86ef9f59c5bf7f9a130e4ccdf1fc092`. |
| Linear-order theory | `Alpha_Beta_Pruning/Alpha_Beta_Linear.thy`, 135,397 bytes, SHA-256 `4e7709b140d8e1023033cf381d1c2b34c269e4f8e2195e8667de903df0e9164d`. |
| Lattice theory | `Alpha_Beta_Pruning/Alpha_Beta_Lattice.thy`, 35,102 bytes, SHA-256 `a60fc92197216cf8f266f440219081b3f034968a15025b6ad8d4864628dcbace`. |
| Overview | `Alpha_Beta_Overview.thy`, 9,538 bytes, SHA-256 `c3353ba6bfc8d12717c2652339ba91aeaa057ce9f4eeb6c92934757b43d578c0`. Its introduction expressly limits the AFP analysis to functional correctness; it provides no Pearl average-query proof. |
| Additional application | `TicTacToe.thy`, 3,176 bytes, SHA-256 `955f59e938886d1a770af9d6a2c2e6f346bbd46aab040c112ae0b7571e55ee05`. An additional general board generator and evaluations, not a substitute for Chapter27's algorithms or an automatic whole-file coverage requirement. |
| Presentation support | `LaTeXsugar2.thy`, 7,798 bytes, SHA-256 `567beedb1b539f1509a4de6a6de313a52f43ae921802dd3cedf614bd9e790554`; no algorithmic obligation arises from Isabelle typesetting support. |
| Formal-source license | Entry advertises BSD; shared <https://isa-afp.org/LICENSE>, SHA-256 `9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`. Retain attribution/notices in adaptations. |
| Pearl1982 | *The Solution for the Branching Factor of the Alpha-Beta Pruning Algorithm and its Optimality*, CACM25(8),559–564; DOI <https://doi.org/10.1145/358589.358616>. Author-hosted reading copy <https://ftp.cs.ucla.edu/pub/stat_ser/solution-branching-factor.pdf>, 531,815 bytes, SHA-256 `3855dbefe8d33e8fa4349cee5a110189738f933317d945bcb1d96fb4d0db8e4d`. |
| Pearl1980 | *Asymptotic Properties of Minimax Trees and Game-Searching Procedures*, Artificial Intelligence14(2),113–138; DOI <https://doi.org/10.1016/0004-3702(80)90037-5>. Author-hosted reading copy <https://ftp.cs.ucla.edu/pub/stat_ser/r21.pdf>, 1,722,203 bytes, SHA-256 `cb9599e31f788193bf53b705ffdf33290d0f1efe043a2dbb774ceb98ff2f2363`. This copy is image based; ordinary text extraction is not a complete reading. The precise later optimality statement below was checked in Pearl1982 and Tarsi1983. |
| Tarsi1983, required lower-bound reference | *Optimal Search on Some Game Trees*, JACM30(3),389–396; DOI <https://doi.org/10.1145/2402.322383>. Public reading copy <https://iuuk.mff.cuni.cz/~sgall/vyuka/PALG/Tarsi-GameTrees.pdf>, 327,049 bytes, SHA-256 `b263014098ad5681a7f171f976f10cfb98698cd39c0c6a4456ad1c904b9bbc66`. Pearl1982 cites the earlier technical-report version. |
| Li et al.2022, required graph/cache construction | *Generalisation of Alpha-Beta Search for AND-OR Graphs With Partially Ordered Values*, IJCAI2022,4769–4775; DOI <https://doi.org/10.24963/ijcai.2022/661>. Official PDF <https://www.ijcai.org/proceedings/2022/0661.pdf>, 428,891 bytes, SHA-256 `40b74489ad38e56e0893eeef1818a692d40eb5f4aef0a985324c616436b8c8d5`. Relevant Algorithm2/Defs4–5 are p4772; Props2–3/Cor2 p4773. |
| Li et al. long proofs and access limit | Official JIAF/PFIA2022 proceedings <https://ci.mines-stetienne.fr/pfia2022/conferences/jiaf/actes/actes_jiaf_2022.pdf>, article pp101–111, relevant proofs106–108; proceedings SHA-256 `18642d76394aea5264da7194d57f2ced0da8577fcd57bd5fd044493be839fa3a`. Footnoted HAL report metadata pins `hal-03656224v2`, but its PDF returned403. The JIAF article is a separately identified primary long version, not claimed identical to HALv2. Full provenance, rights, exact recurrence and proof corrections are in `chapter27-cache-source-recovery.md`. No source-code repository/license was identified. |
| Project/dependencies | conaled baseline `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; inspected HEAD `1aabd512284fe86254278ac631eda061d311050b`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`; Lean4.35.0. Inspection is not acceptance of local candidates. Relevant library files are Apache-2.0. |

The dated archive postdates the pinned PDF and is not claimed to be the
revision that generated it. Manuscript, paper PDFs, renderings and external
theories remain reading inputs in `book-source/`; this original coverage
and provenance note is the deliverable. The papers retain their respective
publisher notices; they are not BSD merely because the AFP entry is BSD.

This chapter has **eight numbered results** (Theorems27.1–27.5,
Lemma27.6, Theorem27.7, Corollary27.8), **thirteen numbered equations**
(27.1–27.13, including the explicitly rejected27.12), and **eleven numbered
exercises**. The unnumbered collapsed-order exercise on p326 and the
clamped-negamax extension on p333 are retained. Dual minimum statements
are in scope by the explicit p324 convention. The final random-tree
optimality assertion is a mathematical obligation, not bibliography-only
discussion. No open conjecture is stated in the book chapter.

## Shared representations, relations and execution boundaries

Use the source rose-tree carrier `Tree α = Lf α | Nd (List (Tree α))`.
`Nd []` is an internal node with no successors, distinct from every `Lf x`.
It must not disappear in a binary-tree encoding or be identified with a
leaf carrying bottom. Evaluation alternates a maximum and a minimum:
`V = maxmin`, `W = minmax`; `V (Nd [])=⊥`, `W (Nd [])=⊤`.
The leaf order and multiplicity remain observable to pruning.

Write `Hmax/Hmaxs/Hmin/Hmins` for the printed fail-hard `ab_` functions,
`Smax/Smaxs/Smin/Smins` for the primed fail-soft functions, and `HT`/`ST`
for their corresponding `abt_` searched-tree observers. The list helpers
of the soft algorithm take a separate accumulated value `m`.

For a linear order define the strong relation, with **result first**:

```
R(a,b,r,v) :=
  (r ≤ a → v ≤ r) ∧
  (a < r ∧ r < b → r = v) ∧
  (b ≤ r → r ≤ v).
```

It is the book's `r ≤ v (mod a,b)`. The Isabelle abbreviation
`fishburn a b v r` places the actual value before the approximation, so
the argument order must be bridged explicitly. Exercise27.4 instead uses
the weaker, initially asymmetric-looking relation

```
K(a,b,x,y) :=
  (y ≤ a → x ≤ a) ∧
  (a < y ∧ y < b → y = x) ∧
  (b ≤ y → b ≤ x).
```

The cases inspect `y`. Under `a<b`, `K` is symmetric and corresponds to
equality after clamping. These statements do not turn `R` into a symmetric
relation.

For lattices use `C(a,b,x)=a⊔(x⊓b)` and

```
E(a,b,x,y) := C(a,b,x)=C(a,b,y)
Q(a,b,r,v) := b⊓v ≤ r ∧ r ≤ a⊔v.
```

`Q` is the book's `r ⊑ v (mod a,b)`; source `bounded a b v r` again
reverses the last two arguments. Neither lattice relation requires
`a≤b`. Theorem27.7 and Exercises27.8–27.10 really hold for arbitrary
windows. The clamped algorithms in Exercises27.6/27.11 use `a≤b`.

All executable branches need decidable comparisons, and the clamped
variants need decidable equality, supplied by the concrete ordered
carrier where appropriate. Abstract real-valued mathematics is not a
claim that arbitrary real comparisons are computable. A new global
`Inhabited` payload assumption is unnecessary; bounded values already
have bounds, and Exercise27.1 explicitly handles the nonempty domain.

### Preserve the actual traversal

The original helpers evaluate the first child **before** checking the
updated cutoff. They do not return immediately merely because the input
window is already closed. For example, on `Fin 3`,
`Hmax 1 1 (Nd [Lf 2])=2`; an entry-guard variant returns1. This is a real
raw behavior difference even if subsequent correctness is restricted to
proper windows. The clamped leaf variant is a third, separately specified
algorithm.

Hard and soft traces agree under the printed premises, but equal returned
values alone do not imply equal traces. For instance, with full `Fin 3`
window `(0,2)`, `Nd [Lf 2,Lf 0]` visits one leaf, and its reversal visits
two, although both have value2. A whole-list fold that suppresses later
recursive evaluations still consumes later list cells; it is not an
unqualified recurrence-preserving replacement for an early return.

The printed trace functions separately call a trace recursion and a value
recursion on the same child. They are mathematical observations of the
value algorithm. Running that observer literally can duplicate work.
If a resource theorem uses traces, instrument the real search to return
value and trace together and prove both projections, or prove an exact
branch-count recurrence independently. Pearl counts **terminal leaf
queries**, whereas the chapter's searched tree contains internal nodes
too; neither count is automatically function calls, comparisons, memory,
or elapsed time. Sets and product lattices do not acquire constant-time
comparison operations from their lattice laws.

## Existing reuse and actual gaps

| Existing component | Reuse and boundary |
|---|---|
| conaled search applications | No inspected alpha-beta implementation or exact rose-tree minimax/trace contract was found. Dijkstra, heuristic search, keyed priority frontiers and binary bracketing trees do not supply these recurrences. |
| Mathlib/core ordered lists | `List.foldr_max_of_ne_nil`, dual minima, `maximum_cons`, `maximum_append`, `Perm.maximum_eq`, and core proof-bounded `List.max`/`min` and optional extrema support fold/valid-domain bridges. The source fold is right-associated with an explicit empty bound; an optimized or left-associated implementation requires the appropriate value and resource correspondence. |
| Mathlib `Data/List/Basic` and `Forall₂` APIs | `List.map_congr_left` matches Eq27.11. Standard list prefix requires equal children; the source hereditary tree prefix instead allows each child to be recursively shortened. Build its small relation over the source carrier, using list relational machinery as useful. |
| Mathlib `Order/Interval/Set/ProjIcc.lean` | `Set.projIcc`, `coe_projIcc`, `projIcc_of_le_left`, `projIcc_of_right_le`, `projIcc_of_mem`, `projIcc_eq_left/right` and `monotone_projIcc` cover the linear clamp. The API takes `a≤b`; it cannot replace unconditional lattice squash equations on unordered windows. |
| Existing order hierarchy | `LinearOrder`, `Lattice`, `DistribLattice`, `BoundedOrder`, product and set instances, distributivity, absorption and `OrderDual` already provide the algebra. `sup_inf_assoc_of_le` covers the ordered-bound rearrangement. Avoid parallel custom copies of these structures. |
| Collapsed bounded order | `subsingleton_of_bot_eq_top` and `subsingleton_iff_bot_eq_top` support the p326 corner case. Do not add an unnecessary `Nontrivial` assumption to full-window correctness. |
| De Morgan structure | An order isomorphism to the order dual plus an explicit involution law supplies the needed negation. `OrderIso.map_inf/map_sup/map_bot/map_top` and ordinary duality are reusable. An arbitrary order-reversing isomorphism is not automatically involutive. A Boolean complement axiom is too strong. |
| Concrete De Morgan witnesses | Extended reals support the motivating numeric example; `Fin.revOrderIso` and `Fin.rev_rev` give a finite executable witness. On `Fin 3`, reflection fixes1, so `1⊔neg 1=1≠2`; De Morgan involution does not imply Boolean complementation. |
| `Applications/Resources/Measured.lean`, `CallCount.lean` | Reuse measured observations and value erasure once the actual search is instrumented. Their existence does not prove the leaf-query model, equal hard/soft operation costs, or any average-case rate. |
| Mathlib probability/asymptotics | `Measure.uniformOfFinset` and `iIndepFun` support finite ranking and independence models; general measure/expectation/limit foundations are available. No inspected Pearl/Tarsi theorem or oracle decision-tree lower bound was found. The pinned uniform API has moved away from deprecated `PMF.uniformOfFintype` aliases; inspect actual signatures before use. |

The algebra suggests a common generic lattice algorithm with checked
linear-order specializations, and a shared order-dual implementation for
minimum cases. This is a reuse direction, not a commitment to replace the
source recurrences or the exercise's expressly requested direct proofs.
Source-oriented aliases belong with reusable domain concepts, not a new
chapter-by-chapter clone of the library hierarchy.

| Inspected file | SHA-256 |
|---|---|
| conaled `Applications/Resources/Measured.lean` | `feb5f2f3096b327d8cf636343f33fcc7be08d1324f3dc7ff6f168bf68a203f46` |
| conaled `Applications/Resources/CallCount.lean` | `5bb2d9e1e43dde11fdcee3c492c44662351c72e9a27af385b79de53e8e76b2a8` |
| Mathlib `Data/List/MinMax.lean` | `7f83e6fb67ff2def7aa99d6a81a06eda1707ef003c437013c54a1b6bae2ea496` |
| Mathlib `Order/Interval/Set/ProjIcc.lean` | `a900ed1d295b12300cf443bd993794439972cb7835853251920f90354156babd` |
| Mathlib `Order/ModularLattice.lean` | `1d579977cdc0f16a69e5e1443f2bb524ac7ef24942a0f2c43e24a656b543d922` |
| Mathlib `Probability/Distributions/Uniform.lean` | `19b53a1140fb5a29373ddecd3550a07020da16b6f1f9118827ea85a67c752f20` |

## Source defects, missing premises and source-only experiments

### D27-1 — Figure27.3 mixes fail-soft labels with fail-hard code

The eight-leaf tree of Figures27.2/27.3 is

```
Nd [Nd [Nd [Lf 2,Lf 3], Nd [Lf 5,Lf 9]],
    Nd [Nd [Lf 0,Lf 1], Nd [Lf 7,Lf 5]]].
```

Its root value is3. Both algorithms visit the leaves `2,3,5,0,1`, pruning
`9` and the whole final `Nd [Lf 7,Lf 5]`. On the right max node, however,
`Hmax 3 ⊤ (Nd [Lf 0,Lf 1])=3`; its min parent also returns3. The figure
labels both nodes1, and p323 describes its labels as the returned values
of the printed algorithm. Those two labels match the later fail-soft
version, whose returned values are1. Retain the figure's correct search
shape and separately checked hard/soft labels. This discrepancy was
confirmed by rendering p322 and independently evaluating the recurrences;
these discovery calculations are not Lean evidence.

### D27-2 — The p326 strict-value explanation needs premises

The explanation claims that all child `Hmin a b t<a` imply
`V(Nd ts)<a`. With `ts=[]`, `a=⊥`, `b=⊤` in a nontrivial bounded order,
the premise is vacuous and the conclusion is `⊥<⊥`. With an invalid
window, even nonempty lists fail: use integer-valued leaves,
`a=2,b=1,ts=[Nd [Lf 3,Lf 4]]`; the child `Hmin` returns1, but its true
minimum is3. A sufficient corrected statement is `a<b`, `⊥<a`, and all
child results `<a`; alternatively a proper window and nonempty `ts`
derive the necessary strict bottom bound. The claim that the hard helper
returns `a` under all-child-results-`<a` is a separate computational fact.
Retain both counterexamples and the corrected strict theorem.

### D27-3 — The cache lemma's abstract hypothesis cannot be instantiated globally

The p328 lemma and source `ab_twice_lb/ub` assume
`∀ a b, R(a,b,abf a b t,V t)`. This is a valid conditional lemma, but the
suggestion `abf=Smax` does not meet that hypothesis for arbitrary windows.
For `a=2,b=0,t=Nd [Lf 1,Lf 3]`, `Smax` returns1 while `V t=3`;
the clause `1≤2 → 3≤1` is false. Use only valid old and new windows when
instantiating the concrete algorithm, and prove the derived narrowing
lemma with these premises explicit. Preserve the original abstract lemma
as a conditional statement instead of asserting its hypothesis as an axiom.

### D27-4 — Wrong set in the second p336 counterexample

With `a=∅`, `b={True}`, `t=Nd [Lf {False}]`, both the true value and the
returned `ab_sup` value are `{False}`. The book prints the returned set
as `{True}`, which would make `b≤ab` true and defeat its intended
nontrichotomy example. The pinned `Alpha_Beta_Lattice.thy` lines256–259
correctly uses `{False}`. Formalize that corrected evaluation and the
failure of all three comparisons `ab≤a`, `a<ab<b`, `b≤ab`; do not silently
copy the incorrect value.

### D27-5 — Theorem27.7's printed proof contains mixed cases

The p337 proof announces the `ab_infs` case and defines
`abt=ab_sup a b t`, `abts=ab_infs a (b⊓abt) ts`, `vt=supinf t`,
`vts=infsup (Nd ts)`. Its goal and parts of its first calculation then
switch to `ab_sups`/`supinf`; a line contains an undefined `v`; the second
branch assumes `¬b≤a⊔abt` instead of the actual complementary guard
`¬(b⊓abt≤a)`. The theorem is not disproved by these transcription errors.
The pinned readable `eq_mod_ab_val` proof, lines178–244, consistently uses
`ab_infs`/`infsup`, the correct guard, and `vt` in the calculation.
Use that corrected simultaneous proof, recording the correction.

### D27-6 — The nonempty exercise and closed-window clamps require care

Exercise27.1 removes the need for bottom/top on valid trees. The source
`maxmin1/minmax1` signatures retain `bounded_linorder`, although their
bodies only call the nonempty extrema helpers; the latter leave empty
lists unspecified in HOL. A Lean solution should genuinely need only a
linear order on its explicit valid domain, with a bounded-order context
only for correspondence to `maxmin/minmax`. Do not hide the missing-domain
behavior behind an arbitrary global default.

For Exercises27.6/27.11, the minimum leaf is the literal dual
`min b (max x a)` / `b⊓(x⊔a)`, not necessarily the maximum leaf clamp on
an invalid window. At `a=2,b=0,x=1` on `Fin 3`, the two are2 and0.
The exercise correctness premises permit `a=b`. The AFP clamped-negamax
theorem is stated only for `a<b`; the unnumbered instruction to carry
Exercise27.6 over to negative values retains its closed-window case as
an additional proof obligation, not an excuse to weaken the exercise.

### D27-7 — Discharged proofs versus abandoned companion experiments

A comment-aware scan found no active `sorry`, `axiomatization` or `axioms`
command in the five inspected theories. It found eight active `oops`
commands in `Alpha_Beta_Linear.thy` at lines410,414,421,425,429,444,447,450,
mostly following deliberately refuted relation/exactness tests, and three
in `Alpha_Beta_Lattice.thy` at lines417,584,783. `oops` abandons a theorem;
it does not certify it or introduce an admitted result. The latter three
concern delayed-test equivalence and hard/soft comparison conjectures.
They are source-only experiments, not printed book obligations. Preserve
their identity if reused, but do not promise a proof or mark them covered
by the source. No Isabelle build was run for this inventory.

The companion additionally includes right-to-left algorithms, multiple
delayed-test versions, generalized accumulator schemes, soft negamax,
and a general tic-tac-toe application. These are useful references when
they supply a required bridge; their mere presence does not turn this
book task into a port of every experiment in the AFP entry.

## Precise scope of the final random-game-tree optimality assertion

The p340 assertion is affirmative, not open. The cited primary work
supports the following precise scope. Fix a branching degree `n≥2`, use
a complete ordered `n`-ary tree of depth `d`, and give its terminal leaves
independent values from one continuous/atomless real distribution. Search
must determine the **exact** root minimax value. Charge one unit per
revealed terminal value, with the tree structure available and arithmetic
or bookkeeping outside this query tariff. Let `N(n,d)` be alpha-beta's
expected number of revealed leaves. The asymptotic parameter is depth,
with `n` fixed.

There is a unique `ξ∈(0,1)` satisfying `ξ^n+ξ=1`. Put
`B(n)=ξ/(1−ξ)`. Pearl1982 Theorem2, p563, proves

```
lim (d → ∞) N(n,d)^(1/d) = B(n).
```

This is an exponential growth rate. It does not assert that alpha-beta
minimizes every finite expected count, visits a minimum leaf set on each
input, or minimizes time on an arbitrary real game graph. Pearl explicitly
discusses nondirectional SSS* inspecting fewer nodes without improving
the asymptotic branching factor. His `n^(3/4)` approximation is a
moderate-degree fit, not the exact theorem and not the large-`n`
asymptotic definition. The book does not separately demand reproducing
that fit or all the papers' numerical analyses.

The necessary lower bound is narrower than a whole Tarsi port:

1. On a uniform Boolean tree with **NAND at every internal node**, give
   leaves independent `Bernoulli(ξ)` values. Tarsi's finite balanced-tree
   theorem, p391, implies directional `SOLVE` is optimal even against
   adaptive nondirectional exact query algorithms. Only its uniform
   critical-distribution specialization is needed here.
2. NAND preserves this marginal because `1−ξ^n=ξ`. Its left-to-right
   short-circuit solver has `E₀=1` and
   `E_(d+1)=E_d ∑_(j<n) ξ^j = B(n) E_d`, hence `E_d=B(n)^d`.
   Every correct competing Boolean algorithm therefore costs at least
   `B(n)^d` in expectation at every finite depth.
3. Translating NAND to a fixed MAX root with alternating OR/AND requires
   complementing values at odd distances from the root. Leaf probability
   of1 is `ξ` for even depth and `1−ξ` for odd depth. This is a model
   bridge, not a flaw in Tarsi. With binary OR at depth1 and probability
   `ξ₂` instead, expected short-circuit queries are `2−ξ₂<B(2)`; that
   simple counterexample prevents an incorrect parity-free translation.
4. The primary formulation compares deterministic adaptive algorithms.
   Independent zero-error randomization inherits the finite Boolean
   lower bound by fixing the random seed and averaging. For almost-sure
   per-input correctness, the Boolean input set is finite, so intersect
   the full-measure correct-seed events first. Do not include bounded-error
   algorithms in this conclusion.
5. For continuous values choose the parity-appropriate quantile and use
   monotone thresholding, which commutes with min/max. A continuous-value
   exact query algorithm can be simulated using Boolean threshold
   answers and independent conditional samples on the corresponding
   sides of the quantile. Prove the joint law and query-count
   correspondence; the simulation can be randomized even if the
   original algorithm is deterministic. This supplies the continuous
   finite-depth lower bound used in Pearl1982 pp563–564 and Tarsi p395.
6. Thus an arbitrary family of correct competing algorithms satisfies
   `liminf_d E[queries]^(1/d)≥B(n)`. If its branching-factor limit exists,
   the limit is at least `B(n)`. No convergence assumption is needed for
   the liminf version. Alpha-beta's own limit is the separate upper and
   lower growth theorem above.

Alpha-beta's expected count depends only on the relative order of
distinct leaf values. Equidistribution of rankings under iid atomless
samples can bridge its count to a uniform random permutation of the
`n^d` ranks. That bridge can simplify alpha-beta analysis; it does not
automatically transfer an **all-algorithm** lower bound to an unrelated
comparison-only or fixed-rank model. Preserve the oracle model in the
lower-bound proof. Handling odd as well as even depths is part of the
growth-limit obligation, even where a source calculation concentrates
on `d=2h`.

All probability, lower-bound and quantitative claims above remain
unimplemented obligations. They cannot be discharged by citing the
papers, by proving only functional correctness, or by defining cost to
equal the desired asymptotic expression.

## Original coverage checklist

Every row below remains queued. `Linear` and `Lattice` refer to the pinned
theories above. Exact algorithms, mathematical claims, illustrative
evaluations and expressly requested proof methods are distinguished from
historical or methodological commentary.

| ID | Source location | Required content, exact assumptions and reuse boundary |
|---|---|---|
| C27-001 | §27.1 p320; Linear85 | Exact rose-tree carrier with labelled leaves and ordered finite child lists; retain `Nd []`, repetitions, arbitrary finite branching and no position labels. Binary full-tree carriers are not exact replacements. |
| C27-002 | §27.1 p320 | Nested tree induction: the `Nd ts` case receives the property for every child in `ts`. Supply the structural recursion/size facts needed for total mutual tree/list algorithms without artificial fuel cutoffs. |
| C27-003 | §27.1 p320 | Bounded linear-order assumptions and bottom/top laws, including the possible one-element carrier. Numeric operations are not required until an explicit negation structure is introduced. |
| C27-004 | §27.1 p321; Linear89 | `maxs []=⊥`, `maxs(x::xs)=max x (maxs xs)`; bridge reusable list extrema while preserving this right-fold specification. |
| C27-005 | §27.1 p321; Linear93 | Exact dual `mins` with empty value `⊤`; its order dual correspondence is part of reuse. |
| C27-006 | §27.1 p320; Linear97 | `V(Lf x)=x`, `V(Nd ts)=maxs(map W ts)`; executable evaluation specification, not an opaque chosen game value. |
| C27-007 | §27.1 p320; Linear100 | `W(Lf x)=x`, `W(Nd ts)=mins(map V ts)` and mutual totality. |
| C27-008 | §§27.1–27.2 pp320–327 | Checked empty-node evaluations `V(Nd [])=⊥`, `W(Nd [])=⊤`, distinct from leaves; retain this case in every later correctness theorem. |
| C27-009 | Figure27.1 p319 | Checked small tic-tac-toe illustration: root rows `OOX / .X. / OX.`, X to move; six terminal paths have outcomes draw, X win, O win, X win, O win, draw in displayed order. Validate the displayed legal moves/wins or an exact board-to-value-tree bridge. The general `TicTacToe.thy` application is optional reuse, not required wholesale. |
| C27-010 | §27.1 pp320–321 | Retain the game-value interpretation where every internal game position has a nonempty move list: maximizing/minimizing choices attain the relevant finite extrema and guarantee the recursive value against opposing choices. State the valid-game domain; `Nd []` has a formal bound value but no legal outgoing move to select. No chess-position generator is requested by the source. |
| C27-011 | Figure27.2 p321 | Exact eight-leaf example from D27-1 has value3, intermediate max values3,9,1,7, and min values3,1. Check its stated maximizing guarantee or instantiate C27-010. |
| C27-012 | §27.2.1 p322 | Local pruning justification: an already attained outer bound dominates a child once the opponent can force an inferior or equal value; formulate through min/max absorption and preserve the equality-cutoff case. |
| C27-013 | §27.2.1 pp322–323 | Deep pruning is not restricted to a parent's immediate bound. Retain a checked example with a strict ancestor's bound; e.g. a min root `Nd [Lf 3, Nd [Nd [Nd [Lf 5,u]]]]` prunes arbitrary `u` in its innermost max node and has value3. Do not substitute a shallow-only algorithm. |
| C27-014 | §27.2.2 p323; Linear461 | `Hmax` returns a leaf's raw value and delegates `Nd ts` to `Hmaxs`; leaves are not clamped. |
| C27-015 | §27.2.2 p323 | `Hmaxs a b []=a`; cons computes `r=Hmin a b t`, `a'=max a r`, then returns `a'` if `b≤a'`, otherwise recurses on `ts` with `(a',b)`. Preserve branch order and tail skipping. |
| C27-016 | §27.2.2 p323 | Exact dual tree function `Hmin`, raw leaves and delegation to its helper. |
| C27-017 | §27.2.2 p323 | `Hmins a b []=b`; cons computes `b'=min b (Hmax a b t)`, cuts when `b'≤a`, otherwise recurses with `(a,b')`. |
| C27-018 | §27.2.2 p323; actual recurrence | Mutual termination and equations for arbitrary raw windows; no entry cutoff may be inserted without a separate refinement. Check `Hmax 1 1 (Nd [Lf 2])=2` on `Fin 3` against an entry-guard result1. |
| C27-019 | Eq27.1 p324; Linear474 | `a≤Hmaxs a b ts` with no proper-window premise. |
| C27-020 | p324 dual convention; Linear478 | `Hmins a b ts≤b`, also for arbitrary windows. |
| C27-021 | Figure27.3 pp322–323 | Full-window hard evaluation of the eight-leaf tree is3. Record the intermediate bound windows used by the printed recursion. |
| C27-022 | Figure27.3 p322 | Exact visited subtree is `Nd [Nd [Nd [Lf 2,Lf 3],Nd [Lf 5]], Nd [Nd [Lf 0,Lf 1]]]`; visited terminal sequence is `[2,3,5,0,1]`. This is a trace obligation, not only root-value equality. |
| C27-023 | Figure27.3; D27-1 | Checked correction: right max and min nodes return3 for hard search but1 for soft search under `(3,⊤)`. Preserve the figure's valid pruning shape and identify the two wrong hard-return labels. |
| C27-024 | Eq27.6 p324 | Define `R(a,b,r,v)` with all three implications and exact result/value argument direction; relate it to source `fishburn a b v r`. Do not replace it by a mere interval-membership property. |
| C27-025 | Eqs27.3–27.5 p324 | Retain all three correctness clauses, with the proper-window hypothesis supplied by Theorem27.1. State which bound is obtained below/above the window and when equality follows. |
| C27-026 | Theorem27.1/Eq27.7 p325 | `a<b → R(a,b,Hmax a b t,V t)`. |
| C27-027 | Theorem27.1 p325 | `a<b → R(a,b,Hmaxs a b ts,V(Nd ts))`; the helper specification contains the entire remaining-list value, not the accumulated maximum. |
| C27-028 | Theorem27.1 p325 | Dual `a<b → R(a,b,Hmin a b t,W t)`. |
| C27-029 | Theorem27.1 p325 | Dual helper `a<b → R(a,b,Hmins a b ts,W(Nd ts))`. |
| C27-030 | Theorem27.1 proof pp325–326 | Preserve a transparent simultaneous computation-induction proof or a checked generic derivation that gives its four cases. In the non-cut maximum case use the conditional IH at updated `a'`; do not assume the recursive premise after a cutoff. The detailed middle-window equality subcases remain explained in the source map. |
| C27-031 | p326 | `R(⊥,⊤,y,x)→x=y` in a bounded linear order, including endpoints. |
| C27-032 | Unnumbered exercise p326 | `¬(⊥<⊤)→∀x y,x=y`; reuse bounded-order subsingleton lemmas. This is a formal exercise, not only explanatory text. |
| C27-033 | Eq27.2 pp324,326 | `Hmax ⊥ ⊤ t=V t` and dual `Hmin ⊥ ⊤ t=W t`, without a global nontrivial-order hypothesis. |
| C27-034 | §27.2.4 p326 | If each child `Hmin a b t<a`, the hard maximum helper returns `a`; retain as a computational lemma with its exact raw behavior, separate from the strict true-value conclusion. |
| C27-035 | §27.2.4 p326; D27-2 | Corrected strict-value theorem under proper window and strict bottom bound, plus the empty-list `a=⊥` and closed-window nonempty counterexamples. The informal implication must not be copied unqualified. |
| C27-036 | §27.2.4 p326; Linear942 | Soft maximum: raw leaf, `Smax a b (Nd ts)=Smaxs a b ⊥ ts`. |
| C27-037 | §27.2.4 p326 | `Smaxs a b m []=m`; cons uses child window `(max m a,b)`, updates `m'=max m childResult`, cuts at `b≤m'`, else recurses keeping original `a,b` and new `m'`. |
| C27-038 | p324 dual convention; Linear951 | Soft minimum: raw leaf and helper initialized with `⊤`. |
| C27-039 | Linear954–955; dual of p326 | Soft minimum helper: child window `(a,min m b)`, `m'=min m childResult`, cut at `m'≤a`, otherwise recurse with original bounds and updated accumulator. |
| C27-040 | Theorem27.2 discussion p327; Linear957–964 | All-window accumulator bounds `m≤Smaxs a b m ts` and `Smins a b m ts≤m`; do not confuse them with `a≤...` or `...≤b`. |
| C27-041 | Theorem27.2 p327 | `a<b → R(a,b,Smax a b t,V t)`. |
| C27-042 | Theorem27.2 p327 | `max m a<b → R(max m a,b,Smaxs a b m ts,V(Nd ts))`; effective lower window is the maximum, not the original `a`. |
| C27-043 | Theorem27.2 dual; Linear977 | `a<b → R(a,b,Smin a b t,W t)`. |
| C27-044 | Theorem27.2 dual; Linear978 | `a<min m b → R(a,min m b,Smins a b m ts,W(Nd ts))`. |
| C27-045 | §27.2.4 p327 correctness consequence | Full-window soft maximum/minimum correctness, retaining the collapsed-order case. |
| C27-046 | Theorem27.3 p327 | `a<b → R(a,b,Hmax a b t,Smax a b t)`; hard result approximates the soft result, not conversely. |
| C27-047 | Theorem27.3 p327 | `max m a<b → R(a,b,Hmaxs (max m a) b ts,Smaxs a b m ts)`; relation window here is the original `(a,b)`, unlike C27-042. |
| C27-048 | Theorem27.3 dual; Linear994 | `a<b → R(a,b,Hmin a b t,Smin a b t)`. |
| C27-049 | Theorem27.3 dual; Linear995 | `a<min m b → R(a,b,Hmins a (min m b) ts,Smins a b m ts)`. The source additionally writes `a<m`, already implied by the first premise; preserve the actual mathematical domain without treating the redundant premise as a new restriction. |
| C27-050 | Strict-improvement example p327; Linear1016 | With numeric `⊥<0<1`, `Smax 0 1 (Nd [])=V(Nd [])=⊥`, while `Hmax 0 1 (Nd [])=0`. An executable finite-order analogue is acceptable with an explicit embedding/renaming of values. |
| C27-051 | Precision interpretation pp324,327 | Retain the exact order-theoretic meaning of stronger/weaker bounds, including transitivity of `R` where used. No numerical distance metric is assumed on an arbitrary ordered carrier. |
| C27-052 | §27.2.4 p327; Linear1050 | Hard trace tree functions preserve leaves and replace the child list by their trace helpers; define maximum and minimum variants. |
| C27-053 | §27.2.4 p327 | Hard trace helper keeps the current traced child, uses the actual hard value to update the bound, then emits an empty tail after cutoff or recurses on the remaining list. Both dual cases and empty trace lists are required. |
| C27-054 | §27.2.4 p327; Linear1067 | Soft trace tree functions initialize maximum/minimum trace helpers with `⊥`/`⊤`; preserve raw leaf labels. |
| C27-055 | §27.2.4 p327 | Soft trace helpers use the effective accumulator window for both child observer and value, keep that child, and branch using the updated accumulator. The tree/list signatures and dual recursion are distinct from hard traces. |
| C27-056 | Theorem27.4 p328 | `a<b → STmax a b t=HTmax a b t`. |
| C27-057 | Theorem27.4 p328 | `max m a<b → STmaxs a b m ts=HTmaxs (max m a) b ts`. |
| C27-058 | Theorem27.4 dual; Linear1087–1088 | Both minimum trace equalities, using `a<min m b` for the helper. Derive through the corresponding hard/soft result relation, not root correctness alone. |
| C27-059 | Meaning of searched-tree observers p327 | Checked correspondence to an actual value-plus-trace search or actual recursive branch events. Do not charge literal duplicate observer evaluation as the underlying alpha-beta search cost. |
| C27-060 | Same-search assertion pp327–328 | Equality of visited leaf/node observations follows from trace equality under its premises. This does not automatically equate comparisons or total work of hard/soft algorithms. |
| C27-061 | §27.2.5 p328; Linear1305 | Abstract lower-bound reuse: given `∀a b,R(a,b,abf a b t,V t)`, old `b≤r`, and `max a' r<b'`, prove the new call at `(max a' r,b')` satisfies `R` for the original new window `(a',b')`. |
| C27-062 | §27.2.5 p328; Linear1310 | Exact dual upper-bound reuse, old `r≤a`, new `a'<min b' r`, call at `(a',min b' r)`, conclusion for `(a',b')`. |
| C27-063 | §27.2.5 concrete use; D27-3 | Derive usable hard/soft cache lemmas assuming correctness only on proper windows, with explicit validity of the old call and narrowed new call. The global abstract hypothesis is not an established property of the concrete functions. |
| C27-064 | D27-3 | Checked counterexample `a=2,b=0,t=Nd [Lf 1,Lf 3]`: soft result1, true value3, failure of `R`; retain a bounded finite carrier containing0–3 if desired. |
| C27-065 | §27.2.5 p328 | An old result strictly inside its valid window is exact and can be reused immediately; retain the equality rather than an unverified cache flag. |
| C27-066 | §27.2.5 p328 no-new-call case | If a known lower bound `r≤V t` satisfies `b'≤r` for a proper new window, returning `r` is a valid lower-bound answer without searching; prove the upper-bound dual. Distinguish an exact cached value from a merely one-sided one. |
| C27-067 | §27.2.5 p328 graph/symmetry discussion | Cache reuse must concern the same value problem: same position up to a proved value-preserving symmetry and same evaluation/depth policy. Preserve the mathematical bound-reuse result; it does not by itself establish correctness of a cached graph algorithm. C27-180–185 retain p340's separate extension, now recovered as Li et al.'s AlphaBetaDuo on a fixed finite AND-OR DAG with exact node keys and cached lower/upper pairs. The source has no depth parameter or symmetry/hash quotient; such adapters require their own value-preservation bridge. No automatic correctness of arbitrary cyclic recurrence follows. |
| C27-068 | §27.2.5 p329; Linear1318 | Exact hereditary `prefix` on trees: same labelled leaf, recursive child-list prefix for nodes, false for mixed shapes. |
| C27-069 | §27.2.5 p329 | `prefixs [] us=True`, paired heads satisfy recursive prefix and tails satisfy prefixs, nonempty left against empty right is false. Plain `List.IsPrefix` with child equality is insufficient. |
| C27-070 | Meaning of search-space decrease p328 | Reflexivity/transitivity and monotonic visited-node/leaf counts for hereditary prefix, as needed to express the stated reduction in searched space. Do not infer pointwise bound-value monotonicity that the source does not assert. |
| C27-071 | Theorem27.5 p329 | `a<b ∧ a'≤a ∧ b≤b' → prefix (STmax a b t) (STmax a' b' t)`. |
| C27-072 | Theorem27.5 p329 | Helper prefix with `max m a<b`, `a'≤a`, `b≤b'`, `m'≤m`; left accumulator is `m`, right is `m'`. |
| C27-073 | Theorem27.5 dual; Linear1414–1415 | Minimum tree version and helper with `a<min m b`, `a'≤a`, `b≤b'`, **`m≤m'`**. The accumulator direction reverses under order duality. |
| C27-074 | Lemma27.6 p329 | `a<b ∧ a'≤a ∧ b≤b' → R(a,b,Smax a b t,Smax a' b' t)`. Narrower search yields a less precise bound in this relation. |
| C27-075 | Lemma27.6 p329 | Helper relation with `max m a<b`, outer-window inclusion and `m'≤m`, measured modulo `(max m a,b)`, not `(a,b)`. |
| C27-076 | Lemma27.6 dual; Linear1376–1377 | Both minimum result/window comparisons, including effective upper bound `min m b` and reversed accumulator inequality. |
| C27-077 | §27.2.5 strict improvement; Linear1407 | Checked strict search reduction: on `Nd [Lf 1,Lf 0]`, soft window `(0,1)` retains only the first child, while `(0,2)` retains both. Use a carrier with those proper bounds. |
| C27-078 | Exercise27.1 p329; Linear108 | Recursive `invar`: every `Nd` has a nonempty child list and every child satisfies the same condition. Checking only the root is insufficient. |
| C27-079 | Exercise27.1; Linear112–118 | Define bound-free `maxs1/mins1` on explicit nonempty domains or with visible failure; singleton and longer-list equations must match the source. |
| C27-080 | Exercise27.1; Linear120 | Define bound-free `maxmin1/minmax1`, recurse only through the proved valid domain, and avoid artificial defaults or a global `Inhabited α`. |
| C27-081 | Exercise27.1; Linear127–141 | Nonempty extrema equal bounded folds where both are available, and `invar t→maxmin1 t=V t`, plus the dual theorem. |
| C27-082 | Exercise27.1 source typing; D27-6 | The new executable mathematical API genuinely needs only a linear order and its nonempty-domain evidence. The Isabelle signature's retained bounded class is not a requirement of the exercise's mathematics. |
| C27-083 | Exercise27.2 p329; Linear145–164 | A single suitably parameterized evaluation plays both max and min roles; ordering reversal or a role flag is permitted. Prove correspondence to both `V` and `W`, including empty children. |
| C27-084 | Exercise27.2; Linear745–782 | Uniform tree and list alpha-beta functions play both roles and preserve argument/bound transformations. A documented choice of one valid parameterization answers the open design choice; every source variant need not be ported. |
| C27-085 | Exercise27.2 | Prove all corresponding function identities for arbitrary raw windows. The exercise does not impose `a<b`; restricting only to proper windows would omit part of the requested identities. |
| C27-086 | Exercise27.3 p330; Linear387 | `a<b → (R(a,b,r,v) ↔ min v b≤r ∧ r≤max v a)`. Preserve the strict-window premise of this equivalence. |
| C27-087 | Exercise27.4 p330; Linear292 | Exact weaker relation `K` defined above, including which argument determines the cases. |
| C27-088 | Exercise27.4 p330; Linear300 | `K(⊥,⊤,x,y)→x=y`, also for the collapsed carrier. |
| C27-089 | Exercise27.4 p330; Linear605 | **Direct** simultaneous proof `a<b → K(a,b,V t,Hmax a b t)` with helper/dual statements, following Theorem27.1. The exercise forbids discharging this proof solely by strong correctness plus `R→K`. |
| C27-090 | Exercise27.4 stated implication; Linear390 | Separately retain `R(a,b,y,x)→K(a,b,x,y)` with its correct argument reversal; it is a fact but not a replacement for C27-089. |
| C27-091 | Exercise27.5 p330 | For `a≤b`, `max a (min x b)` lies in `[a,b]`, sends values below/above to the appropriate endpoint, and fixes values in the interval. Reuse `Set.projIcc` with a checked coercion formula. |
| C27-092 | Exercise27.5; Linear278 | Under `a≤b`, `max a (min x b)=min b (max x a)`. The raw expressions need not agree on an invalid window. |
| C27-093 | Exercise27.5; Linear305–370 | Under `a<b`, `K(a,b,x,y)` iff equality of the two clamped values. The strictness cannot simply be weakened to `a≤b`. |
| C27-094 | Exercise27.5; Linear372 | `a<b → (K(a,b,x,y)↔K(a,b,y,x))`. This symmetry belongs to `K`, not strong `R`. |
| C27-095 | Exercise27.6 p330; Linear830 | Clamped maximum tree/helper: leaf `max a (min x b)`; helper base `a`; cons takes the minimum child's result directly, cuts at equality to `b`, otherwise uses that result as new `a`. No outer maximum remains in the cons clause. |
| C27-096 | Exercise27.6 literal dual | Clamped minimum leaf `min b (max x a)`, helper base `b`, direct maximum child result as new `b`, equality cutoff against `a`. Retain the raw distinction outside ordered windows. |
| C27-097 | Exercise27.6 stated interval claim | All four clamped functions return a member of `[a,b]` under `a≤b`; include `a=b`. |
| C27-098 | Exercise27.6; Linear843 | Under `a≤b`, maximum tree/helper equal the clamp of `V t`/`V(Nd ts)`; dual minimum statements use `W`. Prove the mutual recurrence, not only a final post-processing of `V`. |
| C27-099 | Exercise27.6; Linear856 | Full-window clamped maximum/minimum correctness without an unnecessary nontriviality restriction. |
| C27-100 | D27-6 operational boundary | Checked `Fin 3` counterexample `a=2,b=0,x=1`: maximum/minimum leaf clamps differ2 versus0. Document why common-clamp reuse requires its domain theorem. |
| C27-101 | §27.3/Eq27.8 p331; Linear29 | De Morgan order: bounded linear order plus involution `neg(neg x)=x` and `neg(min x y)=max(neg x)(neg y)`. Use an appropriate existing order-dual interface with the involution law explicit. |
| C27-102 | §27.3 p331; Linear34–60 | Derive the dual De Morgan identity, endpoint exchange, injectivity, reversed weak/strict inequalities and negation/bound reorder laws used in proofs. None requires additive-group structure. |
| C27-103 | §27.3 motivating models; interface checks | Retain an extended-real interpretation or checked embedding for numeric figures, and a finite executable De Morgan witness such as `Fin 3` reflection. Check the middle fixed point to prevent silently strengthening the interface to a Boolean algebra. |
| C27-104 | §27.3.1 p331; Linear168 | `negmax(Lf x)=x`; node evaluates `maxs(map (neg ∘ negmax) ts)`. It alternates perspective through negation, not by treating all leaves as root-perspective values unchanged. |
| C27-105 | §27.3.1 p332; Linear177 | `negate b` conditionally negates leaf values, flips the Boolean role at every `Nd`, and preserves the tree shape/list order. |
| C27-106 | p338 later use; Linear181 | `negate f (negate f t)=t` with arbitrary depth and empty nodes; this is needed for both directions of later translations. |
| C27-107 | Eq27.9 p332; Linear184 | `V t=negmax(negate False t)`, with the nested simultaneous induction or a checked reusable tree-map proof. |
| C27-108 | Eq27.10 p332 | `W t=neg(negmax(negate True t))`; include the empty-node case using negation of bounds. |
| C27-109 | Eq27.11 p332 | Pointwise equality on members of `xs` implies equal mapped lists; reuse `List.map_congr_left` rather than duplicate foundational map theory. Retain its use with the nested child induction hypotheses. |
| C27-110 | p332 list De Morgan formula | `neg(mins(map f xs))=maxs(map (neg ∘ f) xs)`, including empty `xs`; retain the dual if used. |
| C27-111 | Figure27.4 pp331–332 | On the eight-leaf example, negate precisely the odd-depth leaves: terminal sequence `[-2,-3,-5,-9,0,-1,-7,-5]`. Check displayed node values and root3 under negamax, related to C27-011 through `negate False`. |
| C27-112 | §27.3.2 p333; Linear1943 | Hard negamax tree: raw leaf, node delegates to its helper. |
| C27-113 | §27.3.2 p333 | Helper base `a`; cons computes `a'=max a (neg (ab_negmax (neg b) (neg a) t))`, cuts at `b≤a'`, else recurses with updated lower bound. The recursive window reverses and negates both endpoints. |
| C27-114 | §27.3.2 p333; Linear1984 | All-window `a≤ab_negmaxs a b ts`. |
| C27-115 | §27.3.2 p333; Linear1988 | Proper-window strong correctness for both tree and helper relative to `negmax t` / `negmax(Nd ts)`. Retain a direct computation-induction proof as presented; the exercise supplies a separate translation proof. |
| C27-116 | §27.3 correctness consequence; Linear2086 | Full-window negamax alpha-beta returns `negmax`; handle the collapsed bounded order. |
| C27-117 | Exercise27.7 p333; Linear2001 | Tree identities for arbitrary windows: `Hmax a b t=ab_negmax a b (negate False t)` and `Hmin a b t=neg(ab_negmax (neg b) (neg a) (negate True t))`. |
| C27-118 | Exercise27.7 additional simultaneous equations | Helpers correspond to negamaxs on `map (negate True) ts` for maximum and on `map (negate False) ts` with negated/reversed bounds and negated result for minimum. Prove all four identities simultaneously, with no added proper-window premise. |
| C27-119 | Unnumbered extension after Exercise27.7; Linear2176 | Define clamped negamax tree/helper: leaf `max a(min x b)`; helper base `a`; cons takes `a'=neg(child at (neg b,neg a))` directly and cuts when `a'=b`. Preserve this executable variant. |
| C27-120 | Unnumbered extension p333; Linear2183 | `a≤b → ab_negmax2 a b t=max a(min(negmax t)b)`, helper analogue and full-window correctness. The source's `a<b` theorem leaves a closed-window extension to prove; retain it because Exercise27.6 includes equality. |
| C27-121 | §27.4.1 p334 | Partial order plus greatest lower/least upper bound laws for `⊓`/`⊔`; reuse standard lattice interfaces and the six stated inequalities/universal properties. |
| C27-122 | §27.4.1 p334 | Associativity, commutativity, idempotence and the two absorption laws, with the correct operator precedence `x⊔y⊓z=x⊔(y⊓z)`. Existing lattice lemmas discharge these facts. |
| C27-123 | §27.4.1 p334 | Both distributivity laws. Generic correctness is for distributive lattices, not arbitrary lattices with an unjustified simplifier assumption. |
| C27-124 | §27.4.1 p334 | Linear orders instantiate distributive lattices with inf/min and sup/max; provide the checked specializations needed to relate source algorithms. |
| C27-125 | §27.4.1 p334 | Sets with inclusion, intersection and union give a distributive lattice that need not be linearly ordered; singleton sets of two distinct elements witness incomparability. |
| C27-126 | §27.4 p333 and §27.4.1 p334 | Cartesian products of distributive lattices have coordinatewise lattice operations; retain the mathematical multiple-evaluation-component example without inventing a scalar ranking. |
| C27-127 | §27.4.1 p334 | Bounded-lattice endpoint identities for inf/sup; no nontriviality assumption. |
| C27-128 | Figure27.5 p335; Lattice18–24 | Exact list `sups`/`infs` right folds with bottom/top bases. |
| C27-129 | Figure27.5 p335; Lattice26–32 | `supinf`/`infsup` mutual evaluation, raw leaves and alternating list sup/inf. Algebraic evaluation can use the weakest appropriate lattice structure; the subsequent theorem requires distributivity. |
| C27-130 | Figure27.5 p335; Lattice141 | Lattice hard tree functions return raw leaves and delegate nodes to their helpers; retain both sup and inf roles. |
| C27-131 | Figure27.5 p335 | Sup helper base `a`, update `a⊔ab_inf`, cutoff `b≤updated`; inf helper base `b`, update `b⊓ab_sup`, cutoff `updated≤a`. Preserve the conditional recursive tail and all-window monotone helper bounds. |
| C27-132 | §27.4.2 p334 analogy | Checked linear-order specialization of folds, evaluation and raw hard/soft recurrences. Equality of final full-window values alone is insufficient as a source-code bridge. |
| C27-133 | Eq27.12/first counterexample p336; Lattice250 | Formal refutation of the naive strong linear relation on lattices: `a={False}`, `b={False,True}`, `t=Nd [Lf {True}]`; true value `{True}`, returned union, proper `a<b`, but cutoff result is not ≤ true value. Eq27.12 is expressly rejected, not a theorem to prove. |
| C27-134 | Second counterexample p336; D27-4 | Correct returned set `{False}` for `a=∅,b={True},t=Nd [Lf {False}]`; prove all three linear-style comparisons false and document the printed `{True}` typo. The naive implication conjunction can become vacuous on incomparable values. |
| C27-135 | §27.4.3 p336; Lattice44 | Define unconditional squash equality `E(a,b,x,y)` using `a⊔(x⊓b)`, preserving parentheses and source notation correspondence. |
| C27-136 | §27.4.3 p336 | Under `a≤b`, `a≤C(a,b,x)≤b`; if also `a≤x≤b`, the squash fixes `x`. No use of a linear trichotomy is permitted. |
| C27-137 | §27.4.3 p336; Lattice36 | `a≤b → a⊔(x⊓b)=(a⊔x)⊓b`; reuse the modular/distributive lattice lemma with its exact orientation. |
| C27-138 | §27.4.3 p336; Lattice40 | For arbitrary `a,b`, equality of `a⊔(x⊓b)` and `a⊔(y⊓b)` iff equality of `(a⊔x)⊓b` and `(a⊔y)⊓b`. Do not infer equality of the two clamp expressions themselves without `a≤b`. |
| C27-139 | Theorem27.7 p337; Lattice178 | `E(a,b,ab_sup a b t,supinf t)` for **all** windows. |
| C27-140 | Theorem27.7 p337 | Sup-helper squash correctness relative to `supinf(Nd ts)` for all windows. |
| C27-141 | Theorem27.7 p337 | Inf-tree squash correctness relative to `infsup t` for all windows. |
| C27-142 | Theorem27.7 p337 | Inf-helper squash correctness relative to `infsup(Nd ts)` for all windows. |
| C27-143 | Theorem27.7 proof p337; D27-5 | Correct the mixed-case names, undefined variable and non-cut guard using the readable formal companion proof. Retain source discrepancy and checked valid calculation; do not add a premise simply to justify a misprinted line. |
| C27-144 | Corollary27.8/Eq27.13 p337; Lattice246 | `ab_sup ⊥ ⊤ t=supinf t`, dual minimum result, and the full-window squash-to-equality lemma, including trivial bounded lattices. |
| C27-145 | §27.4.4 p338; Lattice592 | De Morgan algebra: bounded distributive lattice, involution and `neg(x⊓y)=neg x⊔neg y`. No Boolean complement equations or numeric addition are assumed. |
| C27-146 | §27.4.4 analogy; Lattice598–623 | Derived dual De Morgan law, reversed inequalities, injectivity and endpoint exchange reused for lattice negamax. Include sets with complement as one valid instance, without limiting the abstract interface to sets. |
| C27-147 | §27.4.4 p338; Lattice655–661 | `negsup` is raw leaf / sup of negated recursive children; `negate` flips parity at each node on the same rose-tree shape. |
| C27-148 | §27.4.4 p338; Lattice663–675 | Negation-map involution and `negsup t=supinf(negate False t)`; retain the dual evaluation identity/list De Morgan lemma needed for proof. |
| C27-149 | §27.4.4 p338; Lattice680 | Lattice `ab_negsup` and helper exact recursion: join current lower bound with negated recursive result at reversed/negated bounds, then use the original updated-value cutoff. |
| C27-150 | §27.4.4/Exercise27.10; Lattice691 | `a≤ab_negsups a b ts` for arbitrary windows. |
| C27-151 | §27.4.4 p338; Lattice707 | Four ordinary/negated alpha-beta identities, including both tree roles and both list helpers with their parity flips and bound transformations, without window-order assumptions. |
| C27-152 | §27.4.4 p338; Lattice717 | `ab_negsup ⊥ ⊤ t=negsup t` via the stated translation and involution, or an equivalent checked derivation. |
| C27-153 | Exercise27.8 p339; Lattice53 | Strong lattice relation `Q(a,b,r,v) := b⊓v≤r ∧ r≤a⊔v`, no order requirement on endpoints. Bridge to source `bounded` argument order. |
| C27-154 | Exercise27.8; Lattice282 | Detailed correctness proof `Q(a,b,ab_sup a b t,supinf t)` and the helper/dual simultaneous statements needed by the computation. This is stronger than Theorem27.7. |
| C27-155 | Exercise27.8; Lattice59 | Strong-relation full-window equality and the displayed full-window alpha-beta consequence. |
| C27-156 | Exercise27.8; Lattice67 | `Q(a,b,r,v)→E(a,b,r,v)` in a distributive lattice, without `a≤b`. Supply the detailed algebraic proof requested. |
| C27-157 | Exercise27.8 counterexample; Lattice92 | Checked failure of the reverse implication. Finite witness `Fin 3`, `a=1,b=2,r=0,v=1` has equal squashes1 but fails `1≤0`; alternatively adapt the companion's upper-bound witness. Keep a proper window to establish strictness convincingly. |
| C27-158 | Exercise27.9 p339; Lattice492 | Exact soft lattice tree functions with raw leaves and bottom/top accumulator initialization. |
| C27-159 | Exercise27.9 | Soft sup helper uses child window `(m⊔a,b)`, updated `m'=m⊔child`, cutoff `b≤m'`, and unchanged outer `a,b`; dual inf helper uses `(a,m⊓b)` and cutoff `m'≤a`. Empty helpers return `m`. |
| C27-160 | Exercise27.9 proof support; Lattice508 | Accumulator monotonicity `m≤ab_sups' a b m ts` and `ab_infs' a b m ts≤m`, all windows. |
| C27-161 | Exercise27.9; Lattice518 | Strong `Q` correctness for soft sup and inf tree functions with original `(a,b)`; no `a<b` or `a≤b` restriction may be added. |
| C27-162 | Exercise27.9; Lattice520–522 | Helper `Q` correctness uses effective `(a⊔m,b)` for sup and `(a,b⊓m)` for inf; no separate accumulator-order premise. |
| C27-163 | Exercise27.9 correctness consequence; Lattice535–544 | Full-window soft lattice equality and squash correctness as consequences of strong correctness. These do not supply the abandoned source hard-versus-soft comparison conjecture. |
| C27-164 | Exercise27.10 p339; Lattice695 | **Direct** proofs `Q(a,b,ab_negsup a b t,negsup t)` and helper analogue for arbitrary windows, using the negamax recurrence and bound lemma. The exercise forbids reducing the proof solely to nonnegative relatives. |
| C27-165 | Exercise27.11 p339; Lattice343 | Clamped sup-tree/helper exact implementation: leaf `a⊔(x⊓b)`; helper base `a`; direct inf-child result as new lower bound and equality cutoff against `b`. |
| C27-166 | Exercise27.11 literal dual | Clamped inf leaf `(a⊔x)⊓b=b⊓(x⊔a)`, helper base `b`, direct sup-child result and equality cutoff against `a`. Do not conflate raw leaf expressions outside `a≤b`. |
| C27-167 | Exercise27.11; Lattice356 | Under `a≤b`, all four clamped lattice functions equal the appropriate squash of `supinf`/`infsup`; include the closed-window case. |
| C27-168 | Exercise27.11 consequence; Lattice371 | Interval membership under ordered bounds and full-window correctness for clamped lattice search, including the dual and degenerate bounded lattice. |
| C27-169 | Companion-only experiments; D27-7 | Preserve the provenance/status of abandoned delayed-test and hard/soft comparison statements if consulted. They are not proven library facts or promised book theorems. Source-only right-to-left/generalized variants are not coverage substitutes for the printed algorithms. |
| C27-170 | Chapter Notes p340; Pearl1982 pp559–563 | Formal probability model: fixed `n≥2`, complete depth-`d` tree, iid continuous/atomless real terminal values, exact root minimax, one cost per exposed terminal value. Recover this precise assertion rather than claiming optimality for arbitrary random graphs or distributions with ties. |
| C27-171 | Chapter Notes p340; Pearl query model | Instrument the actual printed full-window hard/soft traversal and bridge its leaf count to the alpha-beta query algorithm in the rate proof. Internal-node counts, duplicated observer execution, arbitrary compiler time and comparisons are distinct observations. |
| C27-172 | Pearl1982 §2.2 p562, scoped support | Prove the ranking-invariance/equidistribution bridge when using a finite random-permutation model for alpha-beta expectation. All distinct rankings occur with equal probability under iid atomless samples; preserve independence and the appropriate measurable/counting model. This bridge alone is not an all-query-algorithm lower bound. |
| C27-173 | Pearl1982 Eq9/Theorem2 pp562–563 | For `n≥2`, existence and uniqueness of `ξ∈(0,1)` with `ξ^n+ξ=1`; define positive `B(n)=ξ/(1−ξ)` and establish denominator/domain facts needed by the growth theorem. |
| C27-174 | p340 assertion; Pearl1982 Theorem2 | Prove `lim_d N(n,d)^(1/d)=B(n)` for alpha-beta's actual expected leaf queries, including the odd-depth bridge if the main analysis uses even depths. A worst-case pruning example or functional-correctness theorem does not discharge this obligation. |
| C27-175 | Pearl1982 lower bound; Tarsi pp389–395 | Required specialization of Tarsi: uniform degree `n`, NAND at every node, independent `Bernoulli(ξ)` leaves, exact adaptive query algorithms including nondirectional ones; `SOLVE` has expectation `B(n)^d` and minimizes it. Prove the finite-depth lower bound. A port of all balanced-tree results is unnecessary if this specialization has a complete proof. |
| C27-176 | Model bridge for C27-175 | Checked NAND/alternating-minimax leaf-parity translation; separate zero-error randomization averaging lemma; monotone-threshold/conditional-sampling reduction from iid continuous values with exact query-count/law correspondence. Retain the depth1 binary-OR counterexample to an incorrect parity-free translation. |
| C27-177 | Chapter Notes p340 optimality conclusion | For every correct competing deterministic query family, continuous expected cost is at least `B(n)^d`; hence its liminf growth is ≥`B(n)`. If its limit exists, its branching factor cannot beat alpha-beta's. State algorithm/law/termination/correctness premises explicitly; bounded-error competitors are outside this assertion. |
| C27-178 | Meaning of “optimal”; scope boundary | Checked distinction from pointwise minimal work: on full `Fin 3` window, source order `Nd [Lf 0,Lf 2]` visits two leaves, while an exact reverse-order search visits one on that input. Do not strengthen the asymptotic expected-rate theorem to per-input or arbitrary finite-depth optimality. |
| C27-179 | Chapter Notes p340 | Historical attribution, judgments such as “definitive,” and bibliography without a further asserted mathematical result are analysis. The shallow/deep-pruning distinction and hard/soft/lattice tree correctness claims map to the retained recurrences and relations above. The affirmative Li et al. graph/cache extension is separately retained in C27-180–185, with exact primary construction/proofs recovered in `chapter27-cache-source-recovery.md`; it must not be discarded as bibliography. These obligations do not require porting every external program or whole paper. |

## Handoff and completion evidence

Implementation should use the exact public contracts above, reuse the
standard order/lattice/list machinery, and prove source recurrence
bridges for any unified implementation. The read-only inventory found
substantial algebraic reuse but no existing implementation or quantitative
optimality certificate that makes the chapter complete automatically.

Checked specializations should include a collapsed order; a finite
nontrivial linear order; the eight-leaf value/trace example; strict
soft-bound and window-prefix examples; invalid-window counterexamples;
the two finite-set lattice examples; a non-Boolean De Morgan involution;
all requested exercise algorithms and direct-proof variants; and the
NAND/AND-OR parity witness. Tie/equality cutoff and empty internal nodes
are essential branch cases, not optional edge-case polish.

Before Chapter27 can be accepted, replace every mathematical obligation
with a checked declaration, correspondence or documented corrected
statement and counterexample as applicable, then obtain the project's
applicable validation and independent reviews on one immutable candidate.
The Pearl/Tarsi assertions remain genuine formal coverage gaps until
their probability/query/lower-bound and growth proofs are checked.
This inventory, discovery calculations, source `by eval` examples and
external citations are preparation, not acceptance evidence.

## Retained lattice graph/cache extension: scope reconciliation 2026-11-02

CSA-04 in `coverage-scope-audit.md` identified a mathematical assertion in the
p.340 paragraph citing Li et al. (2022): fail-soft alpha-beta in distributive
lattices extends to a game graph with a cache, with correctness stated through
squashing. This is separate from the earlier ordered cache-bound observation
and from the tree/lattice theorem. The original note is preserved under
`../reviews/source-inventories-before-scope-repair/`; exact old/new hashes are
recorded in `scope-reconciliation.md`.

The book paragraph supplies no complete graph/cache recurrence or exact
termination/cache contract. Bounded primary-source recovery on 2026-11-02
has now identified and inspected Li et al.'s **Algorithm2 AlphaBetaDuo**,
Definitions4–5, Propositions2–3 and Corollary2 in the official IJCAI paper
and its accessible JIAF long version. The exact footnoted HALv2 PDF remains
inaccessible (HTTP403); no equality with the JIAF version is assumed.
Complete source pins, original recurrence/contract restatements and
proof repairs are in `chapter27-cache-source-recovery.md`.

The pre-recovery 185-row inventory is preserved at
`../reviews/source-inventories-before-cache-recovery/chapter27-obligations.md`,
SHA-256 `4a7c5a4675822ac7ed0dad125be33b4eb637410ed04beaf8cc07da4672b22ea3`.
The following clarifies those same obligations; it changes no acceptance
state and does not supply a Lean implementation.

| ID | Required mathematical/construction obligation | Domain, evidence and remaining work |
|---|---|---|
| C27-180 | Retain a source-to-construction/theorem correspondence for the minimal p340 extension: IJCAI2022 Algorithm2, Defs4–5, Props2–3 and Cor2; JIAF2022 supplies the complete relevant proofs. | Primary recovery is available with exact URLs/content hashes, HALv2 metadata/access limit and rights observations in `chapter27-cache-source-recovery.md` §§1,8. No program source or code license was identified. The executable Lean witness and correctness proof remain queued; no whole-paper port is required. |
| C27-181 | Define the independent graph value on a fixed finite rooted acyclic graph with arbitrary AND/OR labels, a complete duplicate-free finite child enumeration, leaf evaluation and bounded distributive values. Prove termination via decreasing child rank, value uniqueness, enumeration invariance and finite-unfolding value correspondence. | The paper explicitly permits nonalternation and has no depth parameter. Its unrestricted DAG wording omits a needed finite-computation premise: retain D27C-1's rooted infinite chain, nonunique Boolean value equations and nonterminating full-window run as a checked counterexample, together with the corrected finite-DAG theorem. A more general well-founded presentation must also retain finite child enumeration. |
| C27-182 | Implement the actual paired stateful recurrence `duo(n,a,b,σ)=((l,u),σ')`: exact node keys, hit interval or admissible window-independent initializer, immediate equal-pair return, narrowed window, role-specific paired accumulators, pre-child cutoff/restoration, recursive state threading, final intersection and store. | Preserve every branch in recovery §4, including no store on an exact miss, no extra cutoff after the final child, OR lower/AND upper window updates and both initial accumulators equal to the appropriate extremum. Decidable concrete operations and graph progress are explicit. Returning precomputed true value, an unconnected map oracle or a scalar bound flag is not this implementation. |
| C27-183 | Prove admissible initialization and coherent-cache correctness: every returned pair brackets the true value, refines any old entry, and preserves cache coherence. Coherent leaf entries and leaf initializers must be exact. For all windows, prove `S(a,b,l)=S(a,b,value n)=S(a,b,u)`, where `S(a,b,x)=b inf (a sup x)`. Derive enclosing-window value recovery and `l=u=value n` for the full window. | Props2–3/Cor2 require no `a≤b` or total order. Retain global old-entry refinement/domain preservation and the book bridge: equality under S is equivalent to equality under `C(a,b,x)=a sup (x inf b)`. The paired relation does not make either raw endpoint satisfy the book's stronger scalar Q relation. Preserve recovery §3's weakened-leaf/cache-state counterexamples and §5's nonexact enclosing-window example. |
| C27-184 | Prove sound cache reuse under arbitrary new windows for the same fixed graph/evaluator, including cache-hit correctness, global refinement and unchanged untouched keys. Connect graph unfolding with the book's tree/lattice value semantics under explicitly matched role/empty-node conventions. | Root-node/window arguments alone do not determine the returned pair: initial cache state is an input. Alternating inputs have a direct tree-value bridge; general role labels need a proved value-preserving encoding, with no unproved trace/cost equality. The paper treats childless nodes as evaluated leaves; the book's Nd[] requires a separate bridge. Depth/symmetry/hash adapters retain C27-067's value-identity requirements. |
| C27-185 | Complete executable/source equations, corrected proof obligations and checked boundary witnesses for this bounded extension through the existing value/resource architecture. Retain D27C-2's pre-/post-child window-index correction and D27C-3's exact internal-node early-return proof case, plus the finite-domain correction in C27-181. | Recovery §§6–7 records algebraic repairs and examples; they are future Lean obligations, not current validation evidence. No `O(V+E)` bound, arbitrary cyclic-game theorem, one-visit property, universal cache speedup or entire external framework is promised. Mathematical source recovery is complete to the stated bounded scope; the formal implementation/proof/integration gap remains. |

All C27-001–179 obligations remain; C27-180–185 add the previously missing
asserted extension. The chapter still contains no explicit open conjecture
whose proof is promised. All 185 IDs remain queued, and bibliography alone
continues not to create a whole-paper goal.
