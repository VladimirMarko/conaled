# Ordinary list merge: independent case preflight for proposed FDSA-XM01

Prepared 2026-11-02. **Bounded source and mathematical preparation only.**
This report is not a requirement freeze, implementation, compiler result,
final Standards/Spec review, chapter activation or acceptance. It changes no
earlier report, ticket, source, reference, cache, gate or recorded prerequisite.

The coordinator identifies the baseline as repaired Chapter 1 commit
`07e480f6ec9958d4975bb90151005b84f2907614`, available at
`/workspace/scratch/845aa1048b05/conaled-ch01-cost-models`. All project source
locations below refer to that checkout. The separately validated initial
Chapter 2 prefix is not changed or treated as containing this proposed unit.

## 1. Scope, evidence and recommendation

A small measured counterpart of ordinary `List.merge` adds useful shared
mathematics: one actual selected-branch execution, source comparison counts,
a separately declared invocation count, and connections to existing sorting
and queue values. Retain ordinary lists, the existing value contracts and
`Resources.Measured`. The report specifies observable values and counts;
it does not freeze new declaration names or a new representation.

Read the repository policy, architectural/domain guidance, glossary, ADRs
0001/0010, and example-driven-development skill and worked example. Reused
the complete retained `mergesort-case-readiness.md`, the merge-specific
sections of `mergesort-value-api-readiness.md` and
`mergesort-cost-readiness.md`, and the companion
`ordinary-merge-source-preflight.md`. Their historical status statements
are not new gate/status assertions here. The source companion owns source
provenance and the detailed Chapter 2/14 obligation mapping.

The actual sources inspected for these cases were:

| Existing local source | Exact useful interface or content |
| --- | --- |
| `Applications/Sorting/Merge.lean:11–125` | `mergeBy`, `mergeBy_perm`, `merge_sorted_compatible_on`, `mergeBy_sorted`, `mergeBy_filter`, `mergeBy_stable`, `mergeBy_spec`. |
| `Applications/Sorting/SourceMerge.lean:13–36` | Literal `sourceMerge`, `sourceMerge_eq_merge`, and `mergeBy_source`; ordering is pulled back from keys without a public order instance on records. |
| `Applications/Sorting/Stable.lean:13–25,69–74` | Existing `KeySorted`, full-record filter observation `Stable`, `StableSort`, and `StableSort.unique`. |
| `Examples/StableSorting.lean` | Existing `input`, `expected`, `expected_spec`, `merge_equal_key_filter`, `merge_stable`, and `sorted_permutation_not_stable`. |
| `Applications/Resources/Measured.lean:13–49` | Existing `Measured`, `pure`, `bind`, `reweight`, `bind_value`, `bind_erases`, `reweight_bind`; independent value and observation universes. |
| `Applications/Resources/CallCount.lean:16–29` | `tick`, `primitive_rule`, and `let_rule`; the last exposes the body's actual input value and summed observation. |
| `Applications/Resources/CallComparison.lean:92–99,121` | `cost_le_add_entry`, `add_entry_le`, `tick_cost_comparison`, and `zero_cost_entry_matters`. |
| `Applications/Search/LeftistQueue.lean:16–39,59–61,165–180,317–333` | Raw `PQ`, separate `Ranked`, `entries_length`, actual `mergeOn`/`toListQ` equations, `toListQ_perm`, and heap-dependent `toListQ_sorted`. |
| `book-source/LeanListSort-Basic.lean:39–52` | Actual ordinary `List.merge` definition, `List.nil_merge`, and `List.merge_right`. |
| `book-source/LeanListSort-Lemmas.lean:149–180,260–273` | Actual `List.cons_merge_cons`, `List.length_merge`, `List.mem_merge`, and `List.merge_perm_append`. |
| `book-source/Sorting.thy:79–82,94–95,121–128,147–169` | Source merge, occurrence/support preservation, sortedness iff, handwritten comparison recurrence and length-sum bound. |

Paths beginning `book-source/` or `fdsa-control/` are relative to the shared
workspace `/workspace/scratch/845aa1048b05`, not to the checkout. The
companion source report records the pinned source identities. No remote
retrieval was performed here.

Expected values and counts below were first calculated by the literal
recurrence. A bounded Python mirror of that recurrence then reproduced the
small traces; it created no file. This is arithmetic/trace corroboration,
not Lean execution, proof checking or a replacement for later connected
formal examples.

## 2. Exact observable contract and its hypotheses

Write `M cmp xs ys := List.merge xs ys cmp`, with
`α : Type u` and arbitrary `cmp : α → α → Bool`. Its two empty-side
branches return the other list. When both lists are nonempty, true selects
the left head, and false selects the right head:

```text
M cmp [] ys = ys
M cmp xs [] = xs
M cmp (x::xs) (y::ys) =
  if cmp x y then x :: M cmp xs (y::ys)
             else y :: M cmp (x::xs) ys.
```

The intended comparison observation `C` and invocation observation `E`
follow those same selected recursive arguments:

```text
C cmp [] ys = 0              E cmp [] ys = 1
C cmp xs [] = 0              E cmp xs [] = 1

C cmp (x::xs) (y::ys) =
  1 + if cmp x y then C cmp xs (y::ys) else C cmp (x::xs) ys

E cmp (x::xs) (y::ys) =
  1 + if cmp x y then E cmp xs (y::ys) else E cmp (x::xs) ys.
```

The overlapping two-empty case counts one invocation, not two. Each
nonterminal step consumes exactly one input head and makes one recursive
call. There is one terminal call, so the intended universal observations are

```text
returned value = M cmp xs ys
E cmp xs ys = C cmp xs ys + 1
C cmp xs ys ≤ xs.length + ys.length
E cmp xs ys ≤ xs.length + ys.length + 1.
```

These claims need no sortedness, comparison law, order on payloads,
decidable payload equality, finiteness or inhabitant. Their termination and
bound argument uses only the decreasing sum of the two input lengths.
The requested bounds are deliberately loose; no sharp best/worst formula
or additional asymptotic theorem is necessary.

A dual observation `(C,E) : Nat × Nat` in the existing `Measured` type
is a suitable direction identified in the API discussion: base observation
`(0,1)`, selected nonempty recursion plus `(1,1)`, and construction of
the returned cons from the actual recursive value. Other representation
details remain the API/requirements owner's decision. Existing additive
coordinate projections can expose the two observations; `reweight_bind`
requires an additive homomorphism. The single-merge affine identity
`E=C+1` is not such an additive reweighting.

The source `C_merge` counts head comparisons. `E` is the separately
declared count of entries into this same logical recurrence, including its
initial and terminal calls. Neither counts the implementation work of
`cmp`, constructor allocation, computing input lengths, traversal of a
returned remainder, external list preparation or Lean's compiled runtime.
The standard merge's tail-recursive runtime replacement supplies value
equivalence, not either declared cost theorem.

## 3. Compact independent case families

These are connected-case recommendations, not a quota of one example per
helper. The same families cover several obligations. Alternative numerical
illustrations in the older and companion reports need not all become new
fixtures.

Here `L` and `R` record the selected head, and the trace ends as soon as
one operand is empty. An unexamined remainder is returned directly.

| Family | Comparator and operands | Independent returned list | Trace | C | E |
| --- | --- | --- | --- | ---: | ---: |
| Empty | Any comparator; `[]`, `[]` | `[]` | base | 0 | 1 |
| One empty | Any comparator; `[]`, arbitrary `ys` | `ys` | base | 0 | 1 |
| Other empty | Any comparator; arbitrary `xs`, `[]` | `xs` | base | 0 | 1 |
| Unequal, first singleton wins | Natural `≤`; `[0]`, `[1,2]` | `[0,1,2]` | L, base | 1 | 2 |
| Unequal, opposite exhaustion | Natural `≤`; `[2]`, `[0,1]` | `[0,1,2]` | R,R, base | 2 | 3 |
| Interleaving with duplicates | Natural `≤`; `[0,2,2]`, `[1,2,3]` | `[0,1,2,2,2,3]` | L,R,L,L, base | 4 | 5 |
| Arbitrary payloads | Always true; `[a,b]`, `[c]` | `[a,b,c]` | L,L, base | 2 | 3 |
| Same payload operands | Always false; `[a,b]`, `[c]` | `[c,a,b]` | R, base | 1 | 2 |
| Ties, ordinary source comparator | Natural `≤`; `[1,1]`, `[1]` | `[1,1,1]` | L,L, base | 2 | 3 |
| Same ties, swapped operands | Natural `≤`; `[1]`, `[1,1]` | `[1,1,1]` | L, base | 1 | 2 |
| Both inputs unsorted | Natural `≤`; `[3,1]`, `[2,1]` | `[2,1,3,1]` | R,R, base | 2 | 3 |

The unequal singleton cases are the existing retained Chapter 2 root-merge
witnesses. The interleaving case compares `0≤1`, `2≤1`, `2≤2`,
`2≤2`; the last two tests retain both left occurrences before the right
occurrence of 2. Exhausting the left side returns the remaining `[2,3]`.
The output has six occurrences, including three copies of 2. This is not a
set-only specification.

The arbitrary `a,b,c` family is quantified in `α : Type u`; no distinctness
or equality decision is required. For the empty-payload boundary, quantify
over arbitrary `xs ys : List Empty` and an arbitrary comparator. Both lists
must be empty, so the expected return is `[]` and observation `(0,1)`.
No default element or `Inhabited Empty` may enter the definition or claim.
The observation remains in the small universe of `Nat × Nat`.

The tie pair has identical full unlabelled output and identical total input
length three, with different costs under the same ordinary comparator.
Thus output equality, equal length and merge permutation do not determine
the observation. For the original operands, changing `≤` to `<` also
returns `[1,1,1]` but takes the right head once, yielding `(1,2)).
This is the same always-false branch calculation on equal keys, not another
required numerical fixture.

Future checked connections should use the actual measured branch/base
equations and value-erasure theorem, then existing `List.length_merge`
and `List.merge_perm_append` for the corresponding generic observations.
Apply the public cost bound to these actual executions, including the
unsorted and constant-comparator cases; do not independently calculate a
number while leaving its connection to the public execution missing.

## 4. One actual two-stage bind

The following three-element case exposes dependence on the first
execution's returned list in both value and subsequent work:

1. Merge `[2]` with `[0]` using natural `≤`.
   The test `2≤0` is false, then the right operand is empty.
   The actual result is `[0,2]`, with `(C,E)=(1,2)`.
2. Merge `[1]` with that actual returned `[0,2]`.
   The tests are `1≤0` false and `1≤2` true.
   The actual result is `[0,1,2]`, with `(C,E)=(2,3)`.

For a prospective measured operation `R`, the connected construction is
extensionally

```text
Resources.bind (R cmp [2] [0])
  (fun actualFirst => R cmp [1] actualFirst).
```

Its exact expected value/observation is `([0,1,2], (3,5))` with a dual
counter, or the corresponding two scalar projections. The total entry
observation is total comparisons plus **two**, because there are two
separate merge invocations, each ending in a base call. There is no extra
charge for the enclosing `bind`.

If the continuation instead receives the original concatenation `[2,0]`,
its single test `1≤2` exhausts the left singleton. It returns
`[1,2,0]` with `(1,2)`; combined with the first execution, the erroneous
pipeline would have `(2,4)`. The expected `(3,5)` is therefore sensitive
to the actual intermediate list, not just to its length or multiset.

Connect the case through `Resources.CallCount.let_rule` or the actual
`Resources.bind` equations, the new first execution's value/cost theorem,
and the new second execution's equations at that returned value.
`bind_value`/`bind_erases` support the value composition;
`reweight_bind` supports additive projections when used. Applying a
single final `+1` to the composed comparison observation would predict
four entries and is false. No new composition framework is needed.

For reference, the coordinator's larger alternative was also independently
traced: `[1,4]` with `[2,3]` returns `[1,2,3,4]` with `(3,4)`;
merging that result with `[0,5]` takes `(5,6)`, for totals `(8,10)`.
The smaller case above is sufficient and additionally distinguishes the
wrong intermediate concatenation by its cost.

## 5. Keyed stability and independent payload universes

Reuse the existing signed-record expected specification rather than create
a new sorting contract. Set

```text
xs = [(2,"first")]
ys = [(-1,"negative"),(2,"last")]
key = Prod.fst.
```

Both input blocks are key-sorted. The first test takes the right negative
record; the second is the key-2 tie and takes the left record. The exact
merge result is the existing `Examples.StableSorting.expected`:

```text
[(-1,"negative"),(2,"first"),(2,"last")],  (C,E) = (2,3).
```

The value route uses the new erasure theorem to `mergeBy`, then
`mergeBy_spec` with the two independently established input sortedness
premises, and `StableSort.unique` against the existing `expected_spec`.
Alternatively, `mergeBy_filter`/`mergeBy_stable` expose the key-2
observation directly. The source connection is the existing
`mergeBy_source` (or `sourceMerge_eq_merge` for directly ordered
elements), not a new pure merge definition.

For the capability boundary, retain a generic equal-key specialization:
for `β : Type u` and arbitrary `a b c : β`, use records
`[(1,a),(1,b)]` and `[(1,c)] : List (Nat × β)`. The full returned
records are `[(1,a),(1,b),(1,c)]`, and counts are `(2,3)`.
Swapping the two operands returns `[(1,c),(1,a),(1,b)]`, with `(1,2)`.
Each is stable relative to its own input concatenation. No order,
decidable equality or inhabitant on `β` is needed.

The general value APIs quantify separately over `α : Type u` and
`κ : Type v`. Preserve that separation in measured keyed connections.
`mergeBy_filter` and `mergeBy_stable` require key preorder, decidable
key comparison, decidable key equality and sorted blocks.
`mergeBy_spec` additionally uses the existing key linear-preorder
interface. These assumptions do not belong to the raw execution or cost
claims. Key equality is for the executable filter observation, not for
payload equality.

The API preflight proposes a measured map transport under the same
input-local comparator agreement as existing `List.map_merge`:

```text
∀ a∈xs, ∀ b∈ys, cmp a b = cmp' (f a) (f b).
```

If included, `f=Prod.fst` connects this same tagged family to the
unlabelled tie calculations, preserving the actual `(C,E)` and allowing
a noninjective map across independent universes. This needs no new
fixture. The ordinary `List.map_merge` theorem alone gives only value
transport; equality of costs needs the proposed actual-branch argument.
No exported measured-map name is asserted here.

With the original tagged operands but an always-false comparator, the
right record comes first. Because all keys equal one, the existing
input-local sortedness compatibility premise still holds, and the output
is key-sorted and a permutation. For distinct concrete tags its equal-key
filter is `[c,a,b]` instead of `[a,b,c]`. This is the retained
sortedness/permutation-versus-stability boundary, now attached to the
actual merge. Compatibility alone must not silently become a stability
hypothesis.

## 6. Genuine unsorted inputs, sublists and the converse

The nonempty unsorted case in Section 3 must remain in the raw domain;
the shared operation is not restricted to runs already proved sorted.
With tagged records, its exact independent trace is

```text
xs = [(3,"A"),(1,"B")]
ys = [(2,"C"),(1,"D")]
mergeBy Prod.fst xs ys =
  [(2,"C"),(1,"D"),(3,"A"),(1,"B")],  (C,E)=(2,3).
```

Both operands are unsorted. The key-1 filtered output is
`[(1,"D"),(1,"B")]`, whereas the filter of `xs ++ ys` is
`[(1,"B"),(1,"D")]`. Thus even the actual left-on-equal key comparator
does not establish the existing cross-block stability contract on
arbitrary unsorted operands. The sortedness premises of
`mergeBy_filter` are substantive. The raw value, occurrence, sublist
and cost claims still apply.

The API agent's scoped search confirms that the missing observations are
the two order-free input sublists of one ordinary merge:

```text
xs <+ List.merge xs ys cmp
ys <+ List.merge xs ys cmp.
```

They are proposed additions to the existing merge domain, not names
already exported by the inspected baseline. `sublist_mergeSort` concerns
a whole sort and does not supply these observations. The actual recurrence
preserves the internal order of both operands; `Sublist.cons_cons` and
`Sublist.cons` are the available branch constructors.

Use existing `List.Pairwise.sublist` to derive, for any relation `R`
independent of `cmp`,

```text
Pairwise R (List.merge xs ys cmp) →
  Pairwise R xs ∧ Pairwise R ys.
```

There is no order law, comparator law, key map or payload equality premise
in that implication. The numerical unsorted case supplies a stronger
connected application than only computing its `≤` output: for every
Boolean comparator, merging `[3,1]` with `[2,1]` cannot produce a
natural-`≤` pairwise-sorted list, because the retained left sublist
still puts 3 before 1. This conclusion should consume the new left-sublist
or converse interface. The right-sublist result is exercised in the same
full occurrence/order family, rather than by a new artificial fixture.

Forward keyed sortedness already comes from
`merge_sorted_compatible_on`: key preorder, sorted inputs, and both
branch implications for actual cross-input members. Combining that result
with the generic converse gives its input-local keyed iff. The ordinary
source/keyed specialization can instead use `mergeBy_sorted`.
Permutation or membership alone cannot replace the ordered-sublist
argument.

## 7. Actual raw LeftistQueue.toListQ body

The existing body is

```text
toListQ (PQ.fork k x p l r) =
  (x,p) :: mergeOn Prod.snd (toListQ l) (toListQ r),
```

where `mergeOn` is ordinary `List.merge` with
`cmp a b := decide (a.2 ≤ b.2)`. Keep the actual child enumerations as
the two merge operands. A local measured body is extensionally

```text
Resources.bind (R cmp (toListQ l) (toListQ r))
  (fun zs => Resources.pure ((x,p) :: zs)).
```

The new merge value-erasure law, `CallCount.primitive_rule` and the
existing `toListQ` equation establish its value for every raw
`k,x,p,l,r`, with only `[LE π] [DecidableLE π]`. Neither `Heap`
nor `Ranked` is required. Its observation is exactly that one merge's
observation; adding the root entry by `pure` adds zero.

The coordinated concrete fixture is exactly

```text
l = PQ.fork 0 () 1 PQ.null PQ.null
r = PQ.fork 0 () 2 PQ.null PQ.null
q = PQ.fork 99 () 9 l r.
```

These are raw constructors, not the smart `Search.LeftistQueue.fork`.
The child lists are `[((),1)]` and `[((),2)]`. Their one comparison
takes the left element, then the remainder is returned. The full body
value and local merge observation are

```text
[((),9),((),1),((),2)],  (C,E)=(1,2).
```

The rank caches are malformed (a raw rank-zero leaf is not ranked), and
priority 9 above priority 1 violates heap order. The body equation still
holds and its result is visibly unsorted. No separate rank-counterexample
theorem is necessary merely to retain this use of the unconditional body
bridge. `toListQ_sorted` requires `Heap`; that premise must not be
smuggled into raw value erasure.

For an optional generic size-bound application on the same body,
`toListQ_perm` and `entries_length` give
`(toListQ l).length = size l` and the corresponding right equality,
without `Heap` or `Ranked`. Thus the local merge bounds become
`C ≤ size l + size r` and `E ≤ size l + size r + 1`.
This is a direct reuse of the merge estimate, not a full extraction-cost
theorem.

The child `toListQ` computations are not instrumented by this local body
construction. Neither their costs nor an enclosing tree-entry charge is
included. A whole-tree measured traversal, its actual child binds, its
node-count/value correspondence and any quadratic theorem remain later
work. The pair `(1,2)` must never be described as the cost of traversing
the whole three-node queue.

## 8. Existing Chapter 1 positive-cost qualification

No additional fixture is needed for the useful C1 connection. In every
both-nonempty merge, the first head comparison gives `1 ≤ C`; then the
single-merge law and existing

```text
Resources.CallCount.add_entry_le C positive : C + 1 ≤ 2 * C
```

give `E ≤ 2*C`. Existing `cost_le_add_entry` gives `C ≤ E`.
The retained low-singleton case has `C=1,E=2`, so the factor-two upper
bound is attained in this small instance. This is a specialization of the
actual merge counts through the existing theorem, not a new general
cost-comparison framework.

For either empty-side family, `C=0,E=1`. For every `K : Nat`,
`E ≤ K*C` is false, by the actual base observations and existing
`Resources.CallCount.zero_cost_entry_matters K`.
Therefore a uniform multiplicative comparison over all inputs would be
false. Imports of `CallComparison` belong in the connected examples if
needed; core ordinary merge need not depend on growth/asymptotic theory.
No runtime or asymptotic transport assertion is proposed.

## 9. Statement assessment and bounded outcome

| Claim family | Required assumptions and exact boundary |
| --- | --- |
| Raw execution, erasure, C/E recurrence and bounds | Arbitrary comparator and `α : Type u`; no sorting/order/inhabitance or payload equality assumptions. Actual recursive returns construct actual output. |
| Occurrence, length and support | Reuse ordinary merge value laws after erasure; support alone does not retain duplicates or order. |
| Input sublists and pairwise converse | Arbitrary relation, independent of the comparator; proposed small value additions, not a new carrier or sortedness theory. |
| Forward key-sortedness | Existing input-local branch compatibility and both sorted blocks under a key preorder; source comparator gets the existing lawful specialization. |
| Key-filter stability | Actual left-tie key comparator and sorted blocks; key comparison/equality decisions as required by existing interfaces, none on payloads. |
| Cross-payload map | If retained, actual comparator agreement on cross-input members is essential; ordinary value-map equality alone proves no cost transport. |
| One merge versus a two-merge bind | Exact `E=C+1` for each merge; summed observation gives total `E=C+2` for the selected two-stage execution without an outer charge. |
| Root-plus-merge queue body | Existing actual raw `toListQ` value equation; only the one merge is counted, with child traversals and enclosing entry outside this observation. |
| Positive multiplicative tariff comparison | Both inputs nonempty imply positive C; the empty-side `(0,1)` case refutes the unrestricted claim. |

This unit concerns ordinary two-list merge. Binomial forest merge has a
different equal-rank branch: it consumes both roots, links them and carries
through the recursively produced forest. It changes the number of forest
trees while preserving payload contents. Its carry work and invariants are
not instances of the selected-head list recurrence or its `E=C+1`
law. The companion source report preserves the exact source distinction.

The compact families above are sufficient to expose the important semantic
and cost boundaries. Later implementations should connect them through
the actual public value/cost, sublist, stability and composition statements,
keeping independently calculated expectations fixed unless a mathematical
error is found. No additional broad framework, tight merge bound, full
sorter, queue implementation, tree traversal or chapter theorem is proposed.

Only this new report was written, after checking the path was absent.
No Lean/Lake/compiler/checker, project hash helper, repository source/ref
edit, remote retrieval, gate manipulation, chapter activation or acceptance
action was performed. The bounded Python trace calculation is not a checked
formal result. All new API names, elaboration, proof audit and eventual
acceptance remain with the existing coordinator-owned workflow.
