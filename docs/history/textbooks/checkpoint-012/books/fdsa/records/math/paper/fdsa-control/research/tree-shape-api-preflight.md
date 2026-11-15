# Shared tree-shape bounds: pinned API and reuse preflight

Status: read-only preparation after XT01 draft `64c6b777d828ecfe83234fc2aed94600a1f24297` and checkpoint 0028. This note freezes no scope, changes no chapter status, and reports no compilation or final review. The active Chapter 1 gate is untouched. Only this new control note was written.

## Recommendation

A small structural unit is justified across Chapters 4, 11, and 15: one minimum external-leaf-height observation over the existing `BinaryTree`, the book's complete/almost-complete predicates, and their power and logarithm laws. Reuse the saved XT01 ordinary fold and map/shape observations. Do not introduce another carrier, a generic tree class, a logarithm definition, leaf-depth sets, an algorithm executor, or a priority-queue replacement.

Keep natural-number mathematics separate from the real-analysis bridge. A possible placement is `Applications/Trees/Shape.lean` importing `Applications.Trees.Observations` and `Mathlib.Data.Nat.Log`, with real source corollaries in a small `Applications/Trees/ShapeLog.lean` importing the former and `Mathlib.Analysis.SpecialFunctions.Log.Base`. These paths and all new names below are proposals, not requirements or code. One can keep the first core entirely elementary until logarithm corollaries; there is no mathematical need for real analysis in its induction proofs or optimality theorem.

The leftist application already has `rank_paths`, `rank_size`, and `rank_log`. Preserve those declarations, their independent payload/priority universes, and the existing queue algorithms. The universal BinaryTree result fills the Chapter 4 gap and serves future Braun proofs; it is not a reason to redo the existing leftist bound. Any future representation bridge must be checked separately.

## Evidence and pin

Inspected repository: `/workspace/scratch/845aa1048b05/conaled-tree-cache`, at the root-reported saved XT01 draft above, based on `a14977b9e316cc484ffad8a470d26b15615956c0`. The Mathlib dependency is pinned at `56a005855ea17e0b0958f73ec801ae140b0a1679` (Lean 4.35). No Git command or compiler was run for this note.

Primary local API sources:

- `Applications/Trees/Observations.lean`, `Applications/Trees/Cached.lean` (saved, unvalidated XT01 draft).
- `Applications/Search/LeftistQueue.lean` (pre-existing queue).
- `Applications/Sequences/RandomAccess/Basic.lean` (carrier distinction only).
- `.lake/packages/mathlib/Mathlib/Data/Tree/Basic.lean`.
- `.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/Catalan/Tree.lean` (enumeration only; no needed structural-bound API).
- `.lake/packages/mathlib/Mathlib/Data/Nat/Log.lean`.
- `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Base.lean`.

Pinned source correspondence uses `book-source/Tree.thy` and `Tree_Real.thy`, the July 27, 2026 book, and the existing Chapter 4/11/15 obligation notes. The previously recorded Isabelle revision is `f86f290225eebcc52c1ae7dba2e098f405f51c21`; source hashes are `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9` for `Tree.thy` and `e9a87ce2a0f0aee3f7747f9f662848f65bbb94921942611c12cca0d163e526c6` for `Tree_Real.thy`. This note does not replace the independently owned source/proof assessment.

The design follows the already read AGENTS-linked architectural/domain guidance: use ordinary carriers and operations, expose precisely needed laws, keep observation from execution cost, and avoid stronger type assumptions merely for a proof technique.

## 1. Exact carrier and existing observations

Mathlib's `BinaryTree.{u} (α : Type u) : Type u` has `nil` and `node (value : α) (left right : BinaryTree α)`. Nil is an external leaf with no payload. At the pin:

| Existing declaration | Exact relevant statement |
|---|---|
| `BinaryTree.numNodes` | nil gives 0; node gives `l.numNodes + r.numNodes + 1`. |
| `BinaryTree.numLeaves` | nil gives 1; node gives `l.numLeaves + r.numLeaves`. |
| `BinaryTree.height` | nil gives 0; node gives `max l.height r.height + 1`. |
| `BinaryTree.numLeaves_eq_numNodes_succ (t)` | `t.numLeaves = t.numNodes + 1`. |
| `BinaryTree.numLeaves_pos (t)` | `0 < t.numLeaves`. |
| `BinaryTree.height_le_numNodes (t)` | `t.height ≤ t.numNodes`. |
| `BinaryTree.map` | Arbitrary label map; no injectivity, equality, order, or inhabitant hypothesis. |
| XT01 `Trees.fold` | Explicit base and ternary combine; independent payload and summary universes. |
| XT01 `Trees.fold_map`, `Trees.fold_fusion` | Value transport/fusion; no algebraic typeclass on combine. |
| XT01 `Trees.numNodes_map`, `numLeaves_map`, `height_map` | Shape preservation under arbitrary label maps. |

The scoped Mathlib tree files and its Catalan tree module do not expose minimum height, complete/almost-complete predicates, or the requested power bounds. Catalan enumeration is not needed for an induction proof or for checking these statements.

The existing `RandomAccess.Tree` is leaf-labelled, has no nil constructor, and stores cached sizes on forks. Its `Perfect rank t`, `size_eq_pow`, and `fromT_length` describe complete leaf-labelled blocks, with a payload at the rank-zero leaf. Those are useful analogies but not the same carrier, empty case, or node-count convention. No theorem should transfer to BinaryTree without an explicit representation bridge. The ordinary node-labelled carrier also remains distinct from `Bracketing.Tree`.

## 2. Minimal new definitions and assumptions

For arbitrary `α : Type u`, a proposed `Trees.minHeight` can be the existing fold with base 0 and node algebra `fun l (_ : α) r => min l r + 1`. Its constructor equations are exactly:

```
minHeight nil = 0
minHeight (node a l r) = min (minHeight l) (minHeight r) + 1
```

No finite-set minimum, `Option`, default label, or nonempty-tree assumption is needed: nil is an actual external leaf at depth zero.

Choose one ordinary complete predicate, not two rival definitions. The most direct source presentation is recursive Prop-valued `Complete`: true at nil, and at a node require equal child maximum heights and both children complete. Prove its equivalent observation formula `Complete t ↔ minHeight t = t.height`. A Boolean checker is not needed for these structural theorems; the later chapter may expose one if an executable source client requires it. It can be structurally decidable without `DecidableEq α`.

A proposed `AlmostComplete t := t.height ≤ minHeight t + 1` avoids unnecessary truncated subtraction in proofs. Prove its exact source equivalence with `t.height - minHeight t ≤ 1`; the already proved `minHeight t ≤ t.height` also records the intended nonnegative depth spread. The book's complete tree is often called perfect elsewhere. Almost complete means the external leaves occupy at most two adjacent depths; it does not mean that the last level is packed to the left.

All statements hold for arbitrary payloads, including `α = Empty`. Under `BinaryTree Empty` only nil is possible. An `Inhabited (BinaryTree α)` instance, where needed externally, chooses nil and does not require `Inhabited α`. There is no payload order or equality requirement anywhere in this structural unit.

For the height-optimality comparison preserve distinct types and universes:

```
(s : BinaryTree α) (t : BinaryTree β)
AlmostComplete s → s.numNodes ≤ t.numNodes → s.height ≤ t.height
```

Do not replace the count comparison by equality, nor force α and β to have the same universe.

## 3. Proposed structural theorem sequence

Write `m = minHeight t`, `h = t.height`, and `L = t.numLeaves`. The genuinely missing results are the following semantic statements, not fresh numeric primitives:

1. `m ≤ h`, minimum-height map invariance, and constructor equations.
2. Universal bounds `2^m ≤ L` and `L ≤ 2^h`.
3. `Complete t ↔ m = h`.
4. `Complete t → L = 2^h`, hence also `L = 2^m`.
5. Both strict bounds under `¬ Complete t`: `2^m < L` and `L < 2^h`.
6. Both equality characterizations: `Complete t ↔ L = 2^h` and `Complete t ↔ L = 2^m`. Strict-bound iff forms are immediate from the universal bounds and these equalities; do not multiply public names solely for all logical orientations.
7. `Complete t → AlmostComplete t`; almost-completeness of each child follows directly from the min/max equations. A general subtree relation is outside this small unit.
8. Universal rounded bounds `m ≤ Nat.log 2 L` and `Nat.clog 2 L ≤ h`.
9. Under `AlmostComplete t`, exact formulas `m = Nat.log 2 L` and `h = Nat.clog 2 L`.
10. The cross-type height optimum above.

Map invariance of Complete/AlmostComplete follows from the new minimum-height map law and existing maximum-height map law. It therefore applies to noninjective maps and annotation erasure. This is useful connected reuse of XT01, not an invariant on cached values.

A source-compatible `AlmostComplete (node a l r)` characterization involving only AlmostComplete/Complete/height remains the Chapter 4 exercise obligation. It is small arithmetic but need not automatically enlarge the proposed core. Its correct candidate is:

```
AlmostComplete l ∧ AlmostComplete r ∧
  (l.height = r.height ∨
   (l.height = r.height + 1 ∧ Complete r) ∨
   (r.height = l.height + 1 ∧ Complete l))
```

If child heights differ by one, the shorter child must be complete. The simpler AVL-style local height-difference condition is insufficient.

### Feasible induction proof route

The basic bounds use structural induction. At a node, lower-bound both child leaf counts by the power at the smaller child minimum height; upper-bound each by the power at the larger child maximum height. `Nat.pow_succ` converts two copies of `2^k` to `2^(k+1)`. The existing source uses the same argument.

The pinned `Nat.Log` proofs themselves use `Nat.pow_le_pow_right` with a positive base, `Nat.pow_lt_pow_right` with base greater than one, and `Nat.pow_le_pow_iff_right` for base greater than one. For base 2 all these numeric premises are closed facts. These are the power interfaces to reuse, rather than introducing a local monotonicity framework.

For `Complete ↔ m = h`, combine the inductive equivalences with `m_l ≤ h_l` and `m_r ≤ h_r`. Equality of the parent's min and max forces the child extrema to agree; no leaf-depth enumeration is required.

For the strict upper bound, split the child maximum heights. Unequal heights give a strict inequality in one power contribution; equal heights plus an incomplete parent means at least one incomplete child, to which the induction hypothesis applies. For the strict lower bound split the child minimum heights instead. If those are equal and both children were complete, their maximum heights would also agree, contradicting incompleteness. This is the concrete proof route in `Tree.thy` and avoids a large general equality-in-sums abstraction. The converse equality statements then follow immediately.

An alternative private proof can characterize equality by saturation of both summands; it is mathematically sound but there is no reason to publish its arithmetic helper.

## 4. Exact pinned Nat logarithm interfaces

All declarations below are in `Mathlib.Data.Nat.Log`; these signatures were inspected, not recalled from a different release. In this table `{...}` arguments remain implicit.

| Declaration and argument order | Statement / domain |
|---|---|
| `Nat.le_log_iff_pow_le (hb : 1 < b) (hy : y ≠ 0)` | `x ≤ Nat.log b y ↔ b^x ≤ y`. |
| `Nat.le_log_of_pow_le (hb : 1 < b) (h : b^x ≤ y)` | `x ≤ Nat.log b y`; the nonzero argument is derived internally. |
| `Nat.log_lt_iff_lt_pow (hb : 1 < b) (hy : y ≠ 0)` | `Nat.log b y < x ↔ y < b^x`. |
| `Nat.log_eq_of_pow_le_of_lt_pow (h₁ : b^m ≤ n) (h₂ : n < b^(m+1))` | `Nat.log b n = m`; this declaration has no separate base or nonzero premise. |
| `Nat.log_pow (hb : 1 < b) (x : Nat)` | `Nat.log b (b^x) = x`. |
| `Nat.pow_log_le_self (b : Nat) (hx : x ≠ 0)` | `b^(Nat.log b x) ≤ x`. |
| `Nat.lt_pow_succ_log_self (hb : 1 < b) (x : Nat)` | `x < b^(Nat.log b x).succ`. |
| `Nat.log_mono_right (h : n ≤ m)` | `Nat.log b n ≤ Nat.log b m`; base b is implicit. |
| `Nat.clog_le_iff_le_pow (hb : 1 < b)` | `Nat.clog b x ≤ y ↔ x ≤ b^y`; no nonzero argument premise. |
| `Nat.clog_le_of_le_pow (h : x ≤ b^y)` | `Nat.clog b x ≤ y`; no base premise in this implication. |
| `Nat.lt_clog_iff_pow_lt (hb : 1 < b)` | `y < Nat.clog b x ↔ b^y < x`. |
| `Nat.clog_pow (b x : Nat) (hb : 1 < b)` | `Nat.clog b (b^x) = x`. Its explicit argument order differs from `log_pow`. |
| `Nat.le_pow_clog (hb : 1 < b) (x : Nat)` | `x ≤ b^(Nat.clog b x)`. |
| `Nat.pow_pred_clog_lt_self (hb : 1 < b) (hx : 1 < x)` | `b^(Nat.clog b x).pred < x`; the `1 < x` premise is essential at L=1. |
| `Nat.clog_mono_right (b : Nat) (h : n ≤ m)` | `Nat.clog b n ≤ Nat.clog b m`; base is explicit. |
| `Nat.log_le_clog (b n : Nat)` | `Nat.log b n ≤ Nat.clog b n`. |
| `Nat.log_one_right b`, `Nat.clog_one_right b` | Both are zero; they cover the empty tree's leaf count. |
| `Nat.log2_eq_log_two {n : Nat}` | `Nat.log2 n = Nat.log 2 n`; n is implicit. |

The general `Nat.log_eq_iff` also exists, but its premise is `m ≠ 0 ∨ 1 < b ∧ n ≠ 0`; the specialized two-power-bound theorem above avoids exposing that disjunction to tree clients.

No new rounding recurrence is necessary. `Nat.clog_of_one_lt` and `clog_of_two_le` already give `clog b n = clog b ((n+b-1)/b)+1` under base greater than one and n greater than one / at least two. Those may serve later balancer/Braun algorithm proofs but are not needed for the structural induction.

### Almost-complete proof without real analysis

First obtain the universal rounded inequalities from the two power bounds, using `le_log_of_pow_le` and `clog_le_of_le_pow`.

For a complete tree, `L=2^h` and `m=h`; `log_pow` and `clog_pow` give both equalities, including nil.

For an incomplete almost-complete tree, `m≤h`, `m≠h`, and `h≤m+1` give `h=m+1`. The strict bounds give

```
2^m < L < 2^(m+1).
```

Use the lower strict bound weakened to ≤ and `log_eq_of_pow_le_of_lt_pow` for `log 2 L=m`. For the ceiling, `lt_clog_iff_pow_lt` gives `m < clog 2 L`, hence `m+1≤clog 2 L`, while the universal upper bound gives `clog 2 L≤h`. This avoids subtraction and the false application of `pow_pred_clog_lt_self` at L=1.

For optimality, convert `s.numNodes≤t.numNodes` to `s.numLeaves≤t.numLeaves` using the existing successor identity, then chain:

```
s.height = Nat.clog 2 s.numLeaves
         ≤ Nat.clog 2 t.numLeaves
         ≤ t.height.
```

Only s is almost complete. Alternatively, the source's direct power proof works before any logarithm import. Both preserve the cross-type, ≤-size statement.

## 5. Real logarithm correspondence

The pinned file `Mathlib.Analysis.SpecialFunctions.Log.Base` exposes the following exact declarations:

```
Real.natFloor_logb_natCast (b n : Nat) :
  ⌊Real.logb b n⌋₊ = Nat.log b n
Real.natCeil_logb_natCast (b n : Nat) :
  ⌈Real.logb b n⌉₊ = Nat.clog b n
Real.natLog_le_logb (a b : Nat) :
  (Nat.log b a : Real) ≤ Real.logb b a
Real.log2_le_logb (n : Nat) :
  (Nat.log2 n : Real) ≤ Real.logb 2 n
Real.logb_pow (b x : Real) (k : Nat) :
  Real.logb b (x^k) = k * Real.logb b x
Real.logb_self_eq_one (hb : 1 < b) : Real.logb b b = 1
```

The first four declarations have no extra positivity premise. Their total-function conventions cover exceptional numeric inputs internally; this is not permission to omit a source-domain argument when applying an analytic logarithm equivalence. Here every tree has L≥1, so the intended positive source domain is automatic, even at nil. Note the input-then-base order of `natLog_le_logb`, unlike the floor/ceiling bridges.

Under `AlmostComplete t`, the natural results therefore rewrite directly to the book's `m = ⌊logb 2 L⌋₊` and `h = ⌈logb 2 L⌉₊`. Source `nat(floor ...)` / `nat(ceiling ...)` is nonnegative here; do not silently conflate a Nat floor with an Int-valued floor in theorem statements.

For a complete tree the actual real equality follows from `L=2^h`, casts of natural powers, `logb_pow`, and `logb_self_eq_one`. For the real sandwich or its strict incomplete version, the exact analytic interfaces are:

```
Real.logb_le_iff_le_rpow (hb : 1 < b) (hx : 0 < x) :
  Real.logb b x ≤ y ↔ x ≤ b^y
Real.logb_lt_iff_lt_rpow (hb : 1 < b) (hx : 0 < x) :
  Real.logb b x < y ↔ x < b^y
Real.le_logb_iff_rpow_le (hb : 1 < b) (hy : 0 < y) :
  x ≤ Real.logb b y ↔ b^x ≤ y
Real.lt_logb_iff_rpow_lt (hb : 1 < b) (hy : 0 < y) :
  x < Real.logb b y ↔ b^x < y
```

Use base 2, `BinaryTree.numLeaves_pos`, and the standard natural-cast/rpow bridge. There is no need to reprove an abstract logarithm theory or import real analysis into cached constructors.

## 6. Existing leftist and future Braun consumers

### Leftist queue: reuse, not replacement

Before any priority-order assumptions, `Search.LeftistQueue` has independent `α : Type u` and `π : Type v`, and:

```
rank_paths (q) (hq : Ranked q) :
  rank q = shortPath q ∧ rank q = rightPath q
rank_size (q) (hq : Ranked q) :
  2^(rank q) ≤ size q + 1
rank_log (q) (hq : Ranked q) :
  rank q ≤ Nat.log2 (size q + 1)
```

`shortPath` is already the nil-zero / min-children-plus-one structural recurrence on this different queue carrier. `Ranked` requires recursively valid children, the right cached rank no larger than the left, and root cache equal to right rank plus one. These declarations do not require heap order or a `LinearOrder π`.

For the book's real lower-height bound, cast `rank_log` to Real and compose with `Real.log2_le_logb (size q+1)`. `Nat.log2_eq_log_two` gives the Nat.log spelling if a later client uses it. Do not re-prove this consequence from a new queue or change the existing public theorem signatures.

A later explicit shape map into BinaryTree could connect `shortPath` to the universal minimum-height theorem. Its proof must establish node count and minimum height; if it retains cache/payload information, those observations need their own exact bridges. Such an adapter is not required to prove the shared BinaryTree law and is not silently included in this proposal. It does not establish merge cost merely by preserving values or shape.

Malformed cached rank is an essential boundary: a singleton queue whose stored rank is 100 has size 1 and structural shortPath 1, but its rank violates `2^rank≤size+1`. `Ranked` cannot be omitted. Also a left-only chain can be Ranked with cached rank/rightPath/shortPath 1 while its maximum shape height grows with its length. A logarithmic minimum-height/right-spine bound is not a logarithmic maximum-height theorem.

### Braun arrays: exact predicate bridge remains later

Chapter 11 will prove its own Braun invariant and then `Braun t → AlmostComplete t`; it can consume the shared `height=clog 2 (numNodes+1)`, `minHeight=log 2 (numNodes+1)`, and height optimality immediately. This avoids redefining the logarithm or transplanting the leaf-labelled random-access representation.

The key source constructor step assumes almost-complete children and a node-count difference of one. The common log formulas and monotonicity already reduce that step to the powers surrounding the smaller positive leaf count. Specifically, if `2^i≤L<2^(i+1)`, then `2^i<L+1≤2^(i+1)`, which is precisely the floor/ceiling boundary. Equal-child-size and swapped one-larger cases remain required. Proving this finite arithmetic bridge later is smaller than including Braun operations in a structural unit now.

Actual lookup/update/merge invocation bounds still require their own recursive execution proofs. No logarithmic runtime follows solely from the resulting shape theorem, and no physical storage/sharing bound follows from expanded node count.

## 7. Meaningful connected cases and nonconverses

No enumeration campaign was run for this note. These values follow directly from the displayed constructor recurrences; future code should check them through the shared theorems where appropriate.

| Ordinary shape | Nodes / leaves | minHeight / height | What it checks |
|---|---:|---:|---|
| nil, also the only BinaryTree Empty | 0 / 1 | 0 / 0 | Both powers and both rounded logarithms are exact; Complete and AlmostComplete hold. No nonempty payload or tree premise. |
| one node | 1 / 2 | 1 / 1 | First nonempty complete case and power-of-two boundary. |
| complete three-node tree | 3 / 4 | 2 / 2 | Both complete equality characterizations; floor and ceiling coincide. |
| two-node chain | 2 / 3 | 1 / 2 | Incomplete but almost complete: strict powers 2<3<4, yet Nat.log2 3=1 and Nat.clog 2 3=2. Rounded strictness is false. |
| XT01 asymmetric sample | 4 / 5 | 2 / 3 | Reuse saved size/height/inorder fixture, recover both rounding laws for a noncomplete almost-complete tree. |
| three-node chain | 3 / 4 | 1 / 3 | Arbitrary power-of-two leaf count does not imply completeness. It has the same node/leaf counts as the complete three-node tree. |
| root with empty left and a complete three-node right child | 4 / 5 | 1 / 3 | Height equals clog 2 5 and is minimal, but AlmostComplete is false. Height optimality and the ceiling formula alone have no almost-complete converse. |

An especially useful composition client annotates the XT01 sample (or any input) with its existing size/height pair, or maps all its labels to Unit. New minimum-height/Complete/AlmostComplete map laws should show that the shape properties and log bounds are unchanged. The `Cached.erase_annotate` and shape-erasure laws connect this to actual saved annotation, without relying on annotation validity for the shape itself.

A minimum-height cache specialization can also reuse the existing `Cached.read_eq_fold` with the min algebra, if later cache clients justify it. It must keep the callback/reader tariff distinct; the present structural proposal adds no resource model or whole-fold executor.

## 8. Scope, risks, and stopping point

The genuine new work is a modest induction development over an already existing carrier. The source's strict lower and upper completeness bounds are the main proof content; logarithm APIs already supply the rounding and real correspondence. No concrete API blocker was found.

Potential mechanical risks for future compilation are limited and explicit: min/max case splits; ordering of cast/power rewrites in Real corollaries; different explicit argument orders of `log_pow` versus `clog_pow` and their monotonicity lemmas; and preserving independent label universes in optimality and map laws. Do not “solve” those by stronger public hypotheses. Use natural numeric bounds first and keep exponent monotonicity facts explicit before arithmetic automation.

No tree algorithms, queue replacement/refactor, balance implementation, tree enumeration, generic subtree framework, logarithmic cost transfer, or shape-execution observation is included. Chapters remain queued/unaccepted; XT01 remains an unvalidated saved dependency, and any future implementation/integration still needs its own frozen scope and the existing matching immutable gates and review workflow after Chapter 1's prerequisite is met.
