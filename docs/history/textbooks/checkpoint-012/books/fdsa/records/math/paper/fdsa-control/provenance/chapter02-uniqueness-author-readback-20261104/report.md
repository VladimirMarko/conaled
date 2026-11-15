# Chapter 2 ordinary-sort uniqueness: complete author statement readback

## Outcome and exact scope

**All nine declarations match their intended statements; no concrete finding.**
This is the implementing author's readback of all three library theorems,
all six connected example theorems, their complete source proofs, and the
fully explicit elaborated types. It is not an independent Standards or Spec
review, a full candidate check/audit, or Chapter 2 acceptance.

The author source is held at
`3b727e83fcf9f00ad7d0c95d07305b036ebecbca` on
`work/fdsa-ch02-three-way`. The central inspected candidate is
`fff993ec1d041c0a86e7e79a94d13f5be6b92a94`. The author commit is an
ancestor of the central candidate. Both owned files are byte-identical in
the author worktree, the author commit, and the inspected central commit.
The author worktree remains clean and unchanged.

| Source | Size / lines | SHA-256 |
|---|---:|---|
| `Applications/Sorting/Uniqueness.lean` | 1,999 bytes / 44 lines | `e0df544f59be358a3e40ad48f25115ae2ba3b4507a30cdeb3425907bf94c8744` |
| `Examples/SortUniqueness.lean` | 3,903 bytes / 87 lines | `ce63cd0d8a953f9441b9b6b1597f9a3604ef736131290cba8c0430c36cd177b7` |

The accepted whole-chapter review base remains
`07e480f6ec9958d4975bb90151005b84f2907614`. These focused development
results do not change its status or the foundation-first/full-Chapter-2
acceptance requirements.

## Terminal evidence read and reconciled

The complete type log in
`provenance/chapter02-uniqueness-types-20261104/full.log` was read without
truncation, together with its `result.json`, `inspection-integrity.json`,
and the complete nine-name inspection harness/inventory in
`provenance/chapter02-uniqueness-statement-source-20261104/`.

The type inspection passed with exit 0 in 16.487604626 seconds at the
clean, unchanged central candidate. Its closed log is 6,817 bytes, SHA-256
`11b58acd78c4f7b77bf4fbdb8bd7e4ca48378dcb2fab8c32d91fd0e4ccebda3f`.
The harness explicitly enabled universes, implicit arguments, and full
names. All nine complete declaration headers are present exactly once;
the native logs are secured in the root's preserved evidence.

The preceding focused build is
`provenance/chapter02-mean-uniqueness-xu02-focused-20261104-attempt1/` at
the same central candidate. Its actual aggregate result is **exit 1**, in
101.647276300 seconds, clean and unchanged, because unrelated
`Applications.Resources.RandomQuickSortMean` and
`Applications.Probability.PermutationOrder` targets failed. The closed log
is 17,412 bytes, SHA-256
`48063b4acf544e1cd977f2ffc039a37024bd01e30bfd42357041d4704de22d84`.
It explicitly records both owned targets as built:

- `Applications.Sorting.Uniqueness` — 11 seconds.
- `Examples.SortUniqueness` — 4.8 seconds.

The library emitted two module-system advisory import warnings for its
pinned Mathlib imports; its target still completed successfully. No
compiler error was emitted for either owned file. The aggregate failure
is preserved and is not relabeled a complete-candidate success. Neither
record is an immediate candidate-verification record.

`statements.json` contains exactly nine ordered assessment rows, including
each full elaborated type, its hash, the source location, intended claim,
quantifier/hypothesis assessment, proof connection, and boundary analysis.
The JSON also records the source equality checks and exact evidence-file
identities. Its SHA-256 is
`12dc0b4ff002161b05c0d2e99cc0e8e7011dd5f87d3747c46268a4b8ad4c487f`.

## Per-claim assessment

### 1. `Applications.Sorting.sorters_eq_at`

The elaborated domain is arbitrary `α : Type u`, relation `r : α → α →
Prop`, functions `f g : List α → List α`, and one input `xs`. The only
relation class is `Std.Antisymm r`. Each premise is precisely the
conjunction of `List.Pairwise r` on that function's output and
`List.Perm` from its output to the input. The result is `f xs = g xs`.

Both correctness premises remain local to this input. No global sorter
existence, totality, transitivity, reflexivity, `Nodup`, stability,
inhabitation, or decidable payload equality appeared in elaboration. The
proof composes the two occurrence permutations in the correct direction
and invokes the existing `List.Perm.eq_of_pairwise'`. Its pinned source
was read: that canonical theorem itself requires only antisymmetry and
the two pairwise observations. No standard uniqueness theorem was
duplicated.

### 2. `Applications.Sorting.sorters_eq`

The same arbitrary universe and antisymmetry assumptions remain. Each
correctness premise quantifies over **every** `xs : List α`; the result
is equality in the actual function type `List α → List α`. It is not
merely a single-input result or equality on a selected sample family.

The proof applies function extensionality to `sorters_eq_at`. It does
not assert that a global sorter exists for every antisymmetric relation.
This distinction matters for relations such as equality on a type with
two different elements: the pointwise theorem is still useful on
admissible inputs even where global correctness would be unavailable.

### 3. `Applications.Sorting.sorters_eq_of_multiset`

The literal source-style premise uses pairwise order and equality of the
output/input multisets for each function, for every input. The explicit
types show `Multiset.ofList (f xs)` and `Multiset.ofList xs`, and the
corresponding expressions for `g`. The conclusion is actual function
equality.

This preserves occurrence multiplicities; it is not support/set equality.
The proof uses the existing `Multiset.coe_eq_coe.mp` correspondence and
then `sorters_eq`. Its pinned source confirms precisely the quotient
equality/permutation equivalence. No `DecidableEq α` or replacement
sorting contract was introduced.

### 4. `Examples.SortUniqueness.first_pivot_eq_floor`

The full type quantifies over arbitrary-universe `α` with its existing
`LinearOrder` instance. It equates the actual `quickSortOn id` and
`sortFloorOn id` functions, with their canonical strict and nonstrict
comparison instances. The key is the identity on the same payload type.

The proof applies the new `sorters_eq` to the actual existing correctness
theorems of both algorithms. All input lengths and duplicate patterns are
included. There is no hidden `Nodup`, stability, or additional inhabitance
premise. Equality of values does not claim equal costs, recursion, or
resource observations.

### 5. `Examples.SortUniqueness.three_way_eq_floor`

The conclusion names the actual `threeWayQuickSort` function and the
actual identity-key floor sorter, under only their existing ordinary
`LinearOrder` domain. It includes all lists and equal-pivot occurrences.

The proof invokes the new multiset theorem, using
`threeWayQuickSort_sorted` and `threeWayQuickSort_multiset`. The floor
sorter's permutation is transported to its multiset equation through
the permitted existing `Quot.sound`. This meaningfully exercises the
source correspondence, instead of bypassing the new public theorem.
No equal-bucket occurrence is dropped, and no stability statement is
smuggled into the result.

### 6. `Examples.SortUniqueness.floor_mixed_duplicates`

The explicit type names `sortFloorOn id` on
`[2,3,1,2,0,3,2,1]` and the exact result
`[0,1,1,2,2,2,3,3]`. Both sides have eight occurrences, with respective
multiplicities `0:1`, `1:2`, `2:3`, and `3:2`. No premise weakens this
closed expected-value case.

The proof transfers the retained independent three-way mixed-value
expectation through the new function equality and `congrFun`. The
expected output was not changed to fit elaboration, and the case remains
connected to the actual public sorter.

### 7. `Examples.SortUniqueness.reverse_eq_of_equal`

The full type has arbitrary `α : Type u` and no payload typeclasses. Its
sole premise is `xs.Pairwise (fun a b => a = b)`, and its conclusion is
`xs.reverse = xs`. The type covers empty and singleton lists and
nonempty lists whose pairwise elements are equal.

The proof establishes a local antisymmetry instance for equality using
an ordinary `let`, derives pairwise equality after reversal, and applies
the public pointwise uniqueness theorem to `List.reverse` and `id` with
the actual reversal permutation. No local instance leaked into the
public type. The ordinary `let` respects the pinned linter instruction;
no `letI` workaround or linter suppression was added.

### 8. `Examples.SortUniqueness.equality_order_boundary`

The elaborated result is the complete intended conjunction: equality on
`Bool` satisfies antisymmetry; that same relation is not total; and the
nonempty input `[false,false]` equals its reversal. The finite relation
facts use kernel-checked ordinary `decide`. The nonempty result invokes
`reverse_eq_of_equal` with a satisfiable checked premise.

This is a concrete boundary for the source's prose about linearity.
Non-totality alone does not destroy ordinary list uniqueness once both
outputs satisfy pairwise order and the relation is antisymmetric. The
example does not pretend that equality can sort every mixed Boolean
input, and it does not require a false total-order hypothesis.

### 9. `Examples.SortUniqueness.constant_key_boundary`

Both ordinary key-correctness clauses remain universally quantified over
`List Bool`. The first uses identity; the second uses reversal. In each,
the actual `KeySorted` observation has the constant natural key zero,
and the occurrence permutation targets the same input list. The other
two conjuncts assert genuine inequality of the two functions and failure
of `Stable` for the explicit input `[false,true]` and its reversal.

The proof provides an actual two-element witness for function inequality
and checks the stability equation at key zero. It uses the canonical
`KeySorted` and `Stable` definitions, not invented surrogates. The
elaborated type confirms the same key, input, and output in that stability
claim.

An antisymmetric order on keys does not make the corresponding relation
on distinct tied payloads antisymmetric. This example correctly prevents
misapplication of ordinary payload uniqueness to key-sorted records.
It neither claims that all correct keyed sorters are unequal nor that
stable keyed sorting is impossible.

## Coverage disposition and restrictions

The bounded implementation supplies the missing generic C02-090
function-extensionality consequence and its source multiset formulation.
C02-089 continues to reuse the existing list uniqueness theorem.
C02-091's mathematical boundary is accurately expressed by the two
checked examples: totality is not itself necessary for the local theorem,
while dropping payload antisymmetry allows distinct ordinary key-correct
outputs. These are author-assessed development dispositions for the
root's later full map integration; no global coverage file was changed.

Full source and type inspection found no weakened occurrence claim,
hidden inhabitance, restricted universe, false stability implication,
altered expected output, or new sorting carrier. There is no `sorry`,
`admit`, `native_decide`, new axiom, unsafe proof escape, or proof/linter
restriction change in the owned pair. The complete source read includes
all nine proof bodies, not just their printed declarations.

This author performed no new build or cache operation for the readback
and changed no source, Git reference, public import root, tracker,
coverage map, or previous acceptance record. Only this report and the
nine-row JSON were saved. **Source HOLD remains in effect until the next
explicit bounded release.**
