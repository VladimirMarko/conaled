# Floor-left top-down mergesort: concrete Lean proof plan

Prepared 2026-11-02. **Read-only preparation; Chapter 1 remains the sequential
prerequisite.** This plan changes no Lean source, runs no build, accepts no
chapter, and starts no implementation/review loop. Proposed names below are
design placeholders, not claims that declarations already exist.

## 1. Exact obligation and evidence

The primary source metric is **element comparisons**, not total recursive calls.
FDSA §2.4.2, printed pp. 18–19, explicitly assigns zero cost to an empty-side
merge and to sorting a list of length at most one. It excludes length, take,
drop, constructors and sort-entry charges. Parent confirmed that this is the
primary target; a full call-count extension is optional and unnecessary for
accepting Lemma 2.4. This distinction prevents Appendix B.1's charged list
traversals from changing the theorem being formalized.

Evidence inspected:

- Book: July 27, 2026 PDF, SHA-256
  `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`,
  <https://fdsa-book.net/functional_data_structures_algorithms.pdf>.
- Isabelle `src/HOL/Data_Structures/Sorting.thy`, mirror commit
  `f86f290225eebcc52c1ae7dba2e098f405f51c21`, SHA-256
  `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`.
  Actual definitions and proofs inspected: `merge`, `msort`, `C_merge`,
  `C_merge_ub`, `C_msort`, `length_merge`, `length_msort`, `C_msort_le`,
  `C_msort_log`. The source proof of the power-of-two result inducts on the
  exponent; the stronger all-length route below can derive that result.
- Existing conaled sorting interfaces at
  `1aabd512284fe86254278ac631eda061d311050b`: `Applications/Sorting/`
  `{Stable,Merge,SourceMerge,Sort}.lean` and the resource primitives.
- Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`:
  `Data/Nat/Log.lean`, SHA-256
  `66bb65d1a1cabeb2ee3d8c88c55fd3cf6e48e910ea40322173d79e5ed66a0c3e`;
  `Analysis/SpecialFunctions/Log/Base.lean`, SHA-256
  `85a4b68a9ec0f6cf2fbb706f42a9136d23c4b11f1092b2e88c820c9e26421bbf`;
  and `Algebra/Order/Floor/Ring.lean` for ceiling casts. Actual theorem
  statements and the relevant proofs were read.
- Lean 4.35.0 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`,
  `Init/Data/List/Sort/{Basic,Lemmas}.lean`; reading-copy hashes are retained in
  `chapter02-reuse-plan.md`. Their exact split and merge declarations were
  checked again here.
- FDSA-XB01 draft candidate
  `df116c2f6d834eeb952157505b5c93a9ab5497e8`,
  `Applications/Resources/ListCalls.lean`, SHA-256
  `fba668d88d4c929543a4d5337314761f74f9958cbbd8fc16cf41ca71da5a7e64`.
  This is separately gated, unaccepted foundation work, not integrated
  coverage. Its source was read without running or judging its build.

The primary chapter obligations are C02-025–039, plus the applicable keyed
stability exercise C02-107. This plan does not replace the full Chapter 2
inventory or require an extra asymptotic theorem beyond its scope.

## 2. Preserve the actual source algorithm

Write `n=xs.length`, `a=n/2`, `ys=xs.take a`, `zs=xs.drop a`. The source value
recurrence is:

```text
M xs = xs                                  if n ≤ 1
M xs = merge (M ys) (M zs)                  if 2 ≤ n
```

Merge takes the left head on equality. Its source comparison recurrence is:

```text
CM [] ys = 0
CM xs [] = 0
CM (x::xs) (y::ys)
  = 1 + if cmp x y then CM xs (y::ys) else CM (x::xs) ys

CS xs = 0                                  if n ≤ 1
CS xs = CS ys + CS zs + CM (M ys) (M zs)    if 2 ≤ n
```

Here `cmp : α → α → Bool` is an arbitrary supplied comparison in the generic
execution. The source specialization is `decide (x≤y)`; the keyed version is
`decide (key x≤key y)`. A comparison invocation is one observation regardless
of its internal implementation. This is not a bound on the runtime of an
arbitrarily expensive comparator.

**Std's source recurrence is different.** Pinned
`List.MergeSort.Internal.splitInTwo_fst` and `splitInTwo_snd` use `(n+1)/2`
on the left. `List.mergeSort_append l₁ l₂ h₁ h₂` requires
`h₁ : l₂.length≤l₁.length` and `h₂ : l₁.length≤l₂.length+1`; the book's odd
split has the larger half on the right. Consequently neither that theorem nor
sorted-output uniqueness gives the book's comparison recurrence. Section 10
below exhibits unequal counts at length three even under ordinary natural
order, where the final outputs agree.

## 3. Exact existing reuse and module boundaries

| Existing declaration | Applicable statement and assumptions |
|---|---|
| `List.nil_merge`, `List.merge_right` | Empty-left and empty-right value equations. The pinned empty-right theorem is named `merge_right`. |
| `List.cons_merge_cons cmp x y xs ys` | Exact conditional head merge equation for an arbitrary Boolean comparator. |
| `List.merge_perm_append cmp` | Merge output permutes `xs++ys`; no comparison laws. |
| `List.length_merge cmp xs ys` | Merge length equals the sum of lengths; no comparison laws. |
| `List.mem_merge` | Membership is membership in either input. |
| `Applications.Sorting.sourceMerge_eq_merge`, `mergeBy_source` | Already checked source/standard/keyed merge value correspondences. |
| `Applications.Sorting.mergeBy_perm` | Keyed merge permutes concatenation under only `LE` and its decision procedure. |
| `Applications.Sorting.merge_sorted_compatible_on` | Under `Std.IsPreorder κ`, sorted inputs and comparator compatibility on actual left/right members give key-sorted output. No global comparator law is required. |
| `Applications.Sorting.mergeBy_sorted` | `LE`, `DecidableLE`, `Std.IsLinearPreorder` on keys, with sorted input blocks. |
| `Applications.Sorting.mergeBy_filter` | Exact concatenation of equal-key subsequences, given sorted blocks, `Std.IsPreorder` and `DecidableEq` on keys. |
| `Applications.Sorting.mergeBy_spec` | Existing `StableSort` contract for merging two key-sorted blocks; linear-preorder and decidable-key assumptions. |
| `Applications.Sorting.StableSort.unique` | Equal stable-sort specifications imply equal outputs, using `Std.IsPartialOrder` on keys and `DecidableEq` keys. |
| `Applications.Sorting.sortOn_spec` | Independent standard-sort specification; useful after the new floor-left sorter has its own contract. |
| `Resources.Measured`, `bind`, `pure`, `bind_erases`, `erasureSquare` | Existing value/observation representation and sequencing, with no new resource framework. |

Place the genuinely new floor-left value recurrence in
`Applications/Sorting/TopDown.lean`, reusing standard `List.merge`. Put its
measured comparison companion and measured merge in
`Applications/Resources/MergeSort.lean`. A possible naming family is
`sortFloorBy`, `mergeComparisonRun`, `sortFloorComparisonRun`; final names belong
to implementation. Keep the existing `KeySorted`, `Stable`, and `StableSort`
contracts and arbitrary-universe payloads.

The resource module imports the value interface. A value algorithm defined as
the projection of a resource implementation would reverse that intended
dependency. Conversely, a pair assembled from an independently computed
standard result and an unrelated counter would not itself demonstrate the
source execution. The measured recurrence should thread actual recursive
results into the actual merge and prove erasure to the floor-left value
algorithm.

For comparison increments, make the unit explicit at the nonempty merge
branch. `CallCount.tick` is documented as a recursive-entry tariff; applying
it indiscriminately to sort and merge entries would give the wrong metric.
Empty-side merge and both sort base cases must have observation zero.

## 4. Termination and floor/ceiling sizes

For `2≤n`, put `a=n/2` and `q=n-a`. Prove the following small arithmetic facts
locally or in a shared split lemma actually used by both value and resource
recurrences:

```text
a ≤ n
1 ≤ a, 1 ≤ q
a + q = n
a ≤ q ≤ a+1
q = (n+1)/2 = (n+2-1)/2
a < n, q < n
```

`Nat.div_le_self n 2` supplies the first fact. Constant-division arithmetic
and truncated subtraction can discharge the remaining facts with `omega`.
For the ceiling-half decrease, the inspected standard theorem is:

```lean
Nat.add_pred_div_lt {b n : Nat} (hb : 1 < b) (hn : 2 ≤ n) :
  (n + b - 1) / b < n
```

`List.length_take` yields `min a n=a`; `List.length_drop` yields `q`;
`List.take_append_drop a xs` gives exact ordered reconstruction. These standard
facts suffice for `termination_by xs.length` for each floor-left sorter.
Measure merge by `xs.length+ys.length`, since either selected branch removes
one head. No order properties are used for either termination proof.

The `2≤n` premise matters: at `n=1`, the right half would have length 1 and
would not decrease; at `n=0`, neither child is strictly smaller. The base guard
must prevent these recursive calls. Equal halves occur for even lengths only;
never rewrite both child lengths to `n/2` for arbitrary input.

Expose one-step recurrence lemmas and rewrite targeted calls. The Isabelle
source deliberately removes unrestricted `msort.simps`/`C_msort.simps` from
automatic simplification to avoid recursive unfolding. The Lean proof should
likewise avoid a global simplification rule that expands every recursive
sorter call; ordinary empty/singleton simp lemmas are safe.

## 5. Value observations before cost arithmetic

Prove floor-left permutation for arbitrary `cmp` by well-founded induction on
length. In the recursive case, compose:

1. `List.merge_perm_append cmp` on the two sorted child values;
2. the append of their recursive permutation proofs;
3. `List.Perm.of_eq (List.take_append_drop a xs)`.

This proves `M xs ~ xs` and yields `(M xs).length=xs.length` by
`List.Perm.length_eq`. These two facts need neither totality nor transitivity,
and they are the only value properties needed for the comparison bound.

For sortedness, adapt the existing
`sortBy_sorted_compatible_on` proof structure, replacing only its Std split
with the source floor split. Its substantive step is reusable
`merge_sorted_compatible_on`. Child permutation transfers membership back
through the sorted child; `List.mem_of_mem_take` and `mem_of_mem_drop` transfer
it to the original input. This retains input-local comparison assumptions.

For keyed stability, recursively obtain sortedness and the equal-key filter
identities for each child. `mergeBy_filter` gives the merged equal-key
subsequence as left filtered child followed by right filtered child. Apply the
two recursive identities, `List.filter_append`, and ordered split
reconstruction. Contiguous halves and left-tie merging preserve occurrences
across the split. A permutation-only or underlying-set argument cannot prove
this property.

Package the existing `StableSort` contract. Under the appropriate additional
key antisymmetry, use `StableSort.unique` with `sortOn_spec` to conclude value
agreement with standard `sortOn`. The familiar existing API assumption
`[Std.IsLinearOrder κ]` is sufficient; no order or decidable equality on payload
records is needed. The weaker correctness and comparison theorems retain their
weaker assumptions. This equality transports value observations only.

Chapter 2 also requires the converse of merge sortedness (C02-031). The forward
API already exists. A useful missing generic fact is that each input is a
sublist of `List.merge` for arbitrary `cmp`, proved by the same merge recursion.
Then exact standard `List.Pairwise.sublist` gives the converse. This is a
separate chapter obligation, not a prerequisite for the comparison bound.

## 6. Measured merge and the exact sort recurrence

The measured merge returns `(remainingList,0)` when either input is empty.
On two nonempty inputs it evaluates the same `cmp`, recursively processes the
selected tail pair, prepends the selected original head, and adds exactly 1
comparison. Prove its value projection equals `List.merge xs ys cmp` using
`nil_merge`, `merge_right`, and `cons_merge_cons` with the same branch decision.

Prove the source bound

```text
(mergeComparisonRun cmp xs ys).2 ≤ xs.length + ys.length
```

by induction on the measured merge recursion. Base cost zero is immediate;
each step's recursive length sum is one smaller, cancelling the added unit.
Natural arithmetic suffices. Sortedness, distinctness, linear order, and
nonempty-input hypotheses are unnecessary. A stronger bound by total length
minus one is not required to reproduce (2.15); do not add that proof merely
to sharpen a deliberately loose source estimate.

The measured sorter returns `(xs,0)` in the base case. In its recursive case,
use `bind` for left recursive sorting, right recursive sorting, and measured
merging of those **returned values**, without an additional sort-entry unit.
Prove erasure to `M` independently. Only then rewrite the cost projection to
the exact displayed `CS ys+CS zs+CM (M ys) (M zs)` recurrence. This step
connects the count to the actual algorithm rather than postulating a scalar
recurrence on lengths.

Combining measured-merge erasure, its count bound and child length preservation
gives the crucial step inequality:

```text
CS xs ≤ CS ys + CS zs + a + q = CS ys + CS zs + n.
```

This is the only algorithm-specific estimate used by the logarithmic proof.

## 7. Ceiling-logarithm height: exact API, no new logarithm

The following declarations are present in the pinned `Mathlib.Data.Nat.Log`:

```lean
Nat.clog_of_right_le_one {n : Nat} (hn : n ≤ 1) (b : Nat) :
  Nat.clog b n = 0

Nat.clog_of_two_le {b n : Nat} (hb : 1 < b) (hn : 2 ≤ n) :
  Nat.clog b n = Nat.clog b ((n + b - 1) / b) + 1

Nat.clog_mono_right (b : Nat) {n m : Nat} (h : n ≤ m) :
  Nat.clog b n ≤ Nat.clog b m

Nat.clog_pow (b k : Nat) (hb : 1 < b) :
  Nat.clog b (b ^ k) = k
```

`clog_zero_right`, `clog_one_right`, `clog_pos`, `clog_le_iff_le_pow` and
`le_pow_clog` are also available. The inspected proof of `clog_of_one_lt`, from
which `clog_of_two_le` follows, uses the standard logarithm/power Galois
connection. There is no reason to reconstruct that arithmetic foundation.

For `2≤n`, specialize base 2, rewrite the ceiling half using Section 4, and
obtain

```text
Nat.clog 2 n = Nat.clog 2 q + 1
Nat.clog 2 a ≤ Nat.clog 2 q.
```

The second statement uses `clog_mono_right 2` and `a≤q`. In particular,

```text
max (Nat.clog 2 a) (Nat.clog 2 q) + 1 = Nat.clog 2 n.
```

This is the exact balanced-recursion height relation, taking the height of a
length-zero/one base case as zero. It counts splitting/merge levels, not base
function invocations. The upper logarithm decreases on both recursive children.
There is no need for a new logarithm definition, a wrapper merely renaming
`clog`, or a separate call-tree datatype just to prove the bound.

## 8. Main induction: all lengths first, book corollary second

A useful stronger theorem is

```text
CS xs ≤ xs.length * Nat.clog 2 xs.length.
```

Prove it by the sorter's computation induction or by well-founded induction
on list length. For `n≤1`, both sides are zero by the cost base equation and
`clog_of_right_le_one`. For `2≤n`, let `h=Nat.clog 2 q`. The two induction
hypotheses, merge estimate, and ceiling-half facts give the complete arithmetic
chain:

\[
\begin{aligned}
CS(xs)
&\le CS(ys)+CS(zs)+n\\
&\le a\,\operatorname{clog}_2(a)+q\,\operatorname{clog}_2(q)+n\\
&\le a h+q h+n\\
&=(a+q)h+n\\
&=n(h+1)\\
&=n\,\operatorname{clog}_2(n).
\end{aligned}
\]

The only monotonic multiplication step is
`Nat.mul_le_mul_left a (Nat.clog_mono_right 2 ha_le_q)`. Combine it with
addition monotonicity. Normalize the final equalities with distributivity
(`Nat.add_mul`, `Nat.mul_add`, `Nat.mul_one`) and `a+q=n`; `omega` alone is
not the tool for identities involving products of two symbolic variables.
No real arithmetic or nonlinear bound solver is needed.

For the exact printed Lemma 2.4, assume `xs.length=2^k`, rewrite the stronger
bound with that equality and `Nat.clog_pow 2 k (by decide)`, then commute
multiplication to obtain `CS xs≤k*2^k`. This premise includes `k=0`
(singleton) and excludes empty input. The stronger theorem already covers
empty input separately and avoids duplicating the exponent induction.

The all-length theorem is additional useful support, not a claim that the book
states Lemma 2.4 without its power-of-two premise. It is reusable for later
arbitrary run-count merge bounds, which use the same ceiling-halving pattern.

## 9. Real logarithms and integer ceilings: boundary adapters only

The exact pinned bridge is:

```lean
Real.natCeil_logb_natCast (b n : Nat) :
  ⌈Real.logb b n⌉₊ = Nat.clog b n
```

It has **no positivity hypothesis**: the inspected proof explicitly handles
zero and degenerate bases with Mathlib's totalized logarithm. Specializing to
base 2 rewrites the all-length natural bound into the natural-ceiling form
directly. Casting the natural inequality then gives its real-valued counterpart.

For the book's integer ceiling, distinguish the casts rather than equating
`Nat.ceil` and `Int.ceil` by notation. The exact supporting declarations are
`Int.natCast_ceil_eq_ceil (ha : 0≤r)` and global
`natCast_ceil_eq_intCast_ceil ha`. For `1≤n`, `Real.logb_nonneg` uses base
`1<(2:ℝ)` and `1≤(n:ℝ)` to supply `ha`; handle `n=0` separately by the
totalized `Real.logb_zero`/ceiling-zero equations. This is a proof boundary,
not a new logarithm API.

The source support theorem `C_msort_log` has **no ceiling** and retains
`n=2^k`. Prove `Real.logb 2 (n:ℝ)=(k:ℝ)` with `Nat.cast_pow`,
`Real.logb_pow (2:ℝ) 2 k`, and `Real.logb_self_eq_one` under `1<(2:ℝ)`.
Cast `CS xs≤k*2^k` and rewrite. The all-length `n*clog` theorem alone does
not imply an unrounded `n*log` theorem by removing its ceiling.

Keep `Mathlib.Analysis.SpecialFunctions.Log.Base` in a boundary module or
client where this real presentation is required. The main measured algorithm
and natural bound need only the sorting interfaces, measured vocabulary,
standard list arithmetic, and `Mathlib.Data.Nat.Log`.

## 10. Worked boundary and split cases

These counts follow directly from the displayed recurrences; they are proposed
checked clients, not claims of a Lean verification performed by this plan.

| Input | Source split and work | Source comparisons | `n*clog 2 n` |
|---|---|---:|---:|
| `[]` | Base case; output empty; no comparator invocation | 0 | 0 |
| `[x]` | Base case; output `[x]`; do not recurse on lengths `0,1` | 0 | 0 |
| `[0,1,2]` under `≤` | Left `[0]`, right `[1,2]`; right child uses 1 comparison, root merge uses 1 | 2 | 6 |
| `[2,1,0]` under `≤` | Left `[2]`, right `[1,0]`; right child uses 1 comparison, root merge with `[0,1]` uses 2 | 3 | 6 |

At length three, `a=1`, `q=2`, child logarithms are `0,1`, and parent logarithm
is 2. Neither three-element case satisfies the power-of-two premise. The
uniform `n*clog` bound is deliberately loose; it need not be attained.

For contrast within the required source-correspondence check, Std's ceil-left
split has left/right lengths `2,1`: it uses 3 comparisons on `[0,1,2]` and 2
on `[2,1,0]`. Both algorithms return `[0,1,2]`. This independently isolates
the cost mismatch from correctness or stability.

A useful keyed client puts equal keys across the source split, e.g.
`[(1,"first"),(0,"middle"),(1,"last")]`. The stable result retains the
two key-1 records in their original order. Derive that observation from the
new `StableSort` witness, with no order assumption on String payloads. It
checks the existing contract rather than duplicating the implementation in a
test oracle.

## 11. Precise place of XB01

The separately gated draft supplies these exact statements:

| Witness | Result |
|---|---|
| `Resources.SymmetricCosts.lengthRun_exact xs` | `(xs.length,xs.length+1)` |
| `Resources.ListCalls.takeRun_exact a xs` | `(xs.take a,min a xs.length+1)` |
| `Resources.ListCalls.dropRun_exact a xs` | `(xs.drop a,min a xs.length+1)` |
| `Resources.ListCalls.take_drop_separate a xs` | Two separately executed calls produce the fused split's value and pay twice `SymmetricCosts.splitRun`'s count. |

For `a=n/2`, each separate take/drop has cost `a+1`, while length costs `n+1`.
These facts are ready for any **separately named full call-count model** that
actually sequences those operations. They contribute zero to the chapter's
comparison-only observation and therefore must not be composed as charged
steps into `CS`. Standard `List.length_take/drop` are sufficient for the
comparison proof; XB01 need not become its additional implementation dependency.

If a later client needs full calls, instrument the source value definition:
it evaluates length before the base guard and take/drop only in the recursive
branch. Do not infer evaluation order from the comparison definition's
harmless hoisted value bindings. Preserve separate calls to take and drop
rather than substituting a fused traversal at the same tariff. Prove that new
recurrence and its relation to comparison counts independently. No such
extension or additional bound is required by this plan.

## 12. Truly missing work and bounded implementation order

1. **Source floor-left value realization and split facts.** The actual
   algorithm, its one-step source equation, termination, generic permutation
   and length theorem are new. List arithmetic and merge are standard reuse.
2. **Measured comparison merge.** Exact erasure, zero base counts, selected
   comparison recurrence and the source length-sum upper bound are new.
3. **Measured floor-left sort.** Exact erasure, base counts and cost recurrence
   on actual sorted child outputs are new. Existing standard-sort correctness
   is not its cost witness.
4. **The one inductive bound.** Establish `CS xs≤n*Nat.clog 2 n` using the
   already proved ceiling-half recurrence, then derive the printed
   power-of-two and real-log forms. Only small local half arithmetic is
   missing; no logarithm operation or general divide-and-conquer framework is.
5. **Existing correctness contract for the new realization.** Prove source
   sortedness and keyed stability using current merge APIs, package
   `StableSort`, and derive value agreement with standard `sortOn` under key
   antisymmetry. Keep this independent of the count estimate.
6. **Other required §2.4 coverage.** Merge input-sublist lemmas and the
   sortedness converse remain an adjacent source obligation. They do not
   justify broadening cost assumptions or blocking the elementary estimate.

Before acceptance, review the exact floor orientation, zero comparison bases,
absence of sort-entry charges, comparator tie direction, recursive-result
threading, no unnecessary payload/order assumptions on cost bounds, and the
power-of-two premise of the unrounded log corollary. Source-order activation,
candidate validation and coordinated Standards/Spec review remain root's work.
