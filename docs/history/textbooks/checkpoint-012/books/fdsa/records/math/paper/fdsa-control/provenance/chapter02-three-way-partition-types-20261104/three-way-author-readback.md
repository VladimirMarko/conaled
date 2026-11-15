# Three-way quicksort: complete author statement readback

Recorded 2026-11-04 by the three-way sorter implementation author,
`/root/chapter02_quicksort`, within the existing complete Chapter 2 loop.

**Author assessment: all 36 assigned elaborated declarations read; no concrete
statement or source-correspondence findings.** This assessment covers the 13
sorter declarations and 23 connected example declarations. Root separately
assesses the remaining 48 shared partition and legacy declarations in the
combined 84-declaration inspection. This is not an independent Standards or
Spec review, a full candidate check, an axiom audit, or acceptance of XQ01,
C02-102, or Chapter 2.

## Exact source and evidence

The author worktree remains clean on `work/fdsa-ch02-three-way` at
`d4208023c1c30f5f15773b1f50a4d11db0a29e2c`. The centrally compiled and inspected
candidate is `4ac0e7eed2fa41a8844fff8d213b6298e9ad5cf9`. A read-only comparison
of both complete source files against that immutable central candidate
confirmed byte identity:

| Source file | Complete source read | Bytes | SHA-256 |
|---|---:|---:|---|
| `Applications/Sorting/ThreeWayQuickSort.lean` | 150 of 150 lines | 6,597 | `7ef1adb48a9211c010c84c20c64bd01690eba11683002d8a16cc820eefaf1f0e` |
| `Examples/ThreeWayQuickSort.lean` | 142 of 142 lines | 6,360 | `0951a0f474638250912d4b6ee3084bbbf129c67c0f1527785778003ee1331d86` |

All 534 lines of `three-way-types.txt` were read, covering all 36 unique
declarations. Its independently recomputed size is 41,779 bytes and SHA-256 is
`0cfc0cbc9452e2b1dfd7eef5fe4f7022732d43cb41c1d84c308d9a145c99f70c`, matching
`type-output-sections.json`. The inspection input explicitly enables
`pp.universes` and `pp.explicit` and uses `#check @...` for every declaration.
The complete input and `inventory.json` were read from
`../chapter02-three-way-partition-statement-source-20261104/`; its inventory
records input SHA-256
`48019e7cc7c38382139b939a521527773e59b39f5b4b8ffff210d199babb7dbf` and the
36-plus-48 split.

The secured central results were read and their full-log hashes recomputed:

| Recorded operation at exact central candidate | Actual terminal result | Evidence identity |
|---|---|---|
| Six-target focused attempt in `../chapter02-variants-xd01-focused-20261104-attempt1/` | Aggregate exit **1**, elapsed **149.94887695300167 seconds**, unchanged HEAD and clean final status. The log separately records `Applications.Sorting.ThreeWayQuickSort` **built in 5.8 seconds** and `Examples.ThreeWayQuickSort` **built in 1.0 second**. | Complete log: 19,446 bytes, SHA-256 `bd000490148fe78ad1f67dfd0f1eb38c05aa9ecd3212ea58ac038e15622947fa`. |
| All 84 explicit declaration checks in this directory | Exit **0**, elapsed **14.876180347000627 seconds**, unchanged HEAD and clean final status. | Complete log: 91,292 bytes, SHA-256 `c05a5e5a0098492721b81c689383d421a24ec3d6bf2b00a7629ae18be5ad8d99`. |

The aggregate focused failure names `Applications.Resources.DifferenceListCosts`
and `Examples.RandomQuickSort`. It is not recorded as an aggregate pass. The
native result records confirm one Lean thread, actual exits 1 and 0 respectively,
no timeout and no recorder error. This author assessment launched no compiler.

The pinned FDSA PDF hash was reverified as
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. Exercise
2.3's source was reread in the supplied chapter extraction, along with the
existing three-way readiness disposition and frozen case expectations. The
exercise uses three tail filters, recursively sorts only strict buckets, and
places one held pivot before the entire equal block. Its domain is a linear
order. The implementation and examples retain that scope.

## Domains, execution and proof meaning

The elaborated generic declarations quantify over arbitrary `α : Type u` and
the source's `[LinearOrder α]`. They introduce no `Nodup`, positive-length,
finite-carrier, `Nonempty`, `Inhabited`, or pivot-in-tail premise. In particular,
the nil law needs no element. Singleton and replicate laws take their actual
element as an explicit parameter, which is not a global inhabitation instance.
The concrete fixtures elaborate over `Nat` with its ordinary linear order and
decidable equality. No hidden constraint narrows the all-input correctness
claims to the selected fixtures.

The complete defining body and the fully explicit cons equation both show
exactly three filters of the tail: `x < pivot`, `x = pivot`, and `pivot < x`.
There are exactly two recursive calls, on the strict less and strict greater
lists. The held pivot and every equal tail occurrence are emitted directly.
Both appends have the source's explicit right association. No conclusion
about these calls is inferred merely from equality of final output lists.

The shared `partition3` bridge is an exact value equation used by the proofs.
The sorter itself retains the three filters. The bridge makes no cost or
traversal equivalence claim between those filters, the shared two-partition
operation, and any separately measured worker. The source imports the small
partition boundary and the existing sorting observations, with no import of
the complete Selection algorithm or Resources implementation.

Termination decreases the whole input length. In the compiler-generated
defining goals, the filtered list is attached and then projected by
`unattach`. The checked proof normalizes `length_unattach` and `length_attach`,
uses `length_filter_le`, and takes the strict successor step from the tail to
the whole cons input. Recursive correctness proofs use the corresponding
filter length bound through `partition3_eq_filters`. No proof depends on the
pivot occurring in the tail or on either strict bucket being shorter than
the tail itself.

`KeySorted` was read at the exact central candidate: it is the existing
pairwise observation `xs.Pairwise (fun a b => key a ≤ key b)`. Therefore the
sorter's `KeySorted id` statement asserts nondecreasing order of the actual
output. The permutation proof preserves every occurrence and the one held
pivot. The order proof transfers membership from actual recursive outputs
through permutation, obtains the strict bucket bounds and middle equality,
and assembles the ordinary pairwise append laws. Multiset and support results
are derived from occurrence preservation; support equality does not replace
the stronger source requirement.

## Every core declaration assessed: 13 of 13

All names in this table have prefix `Applications.Sorting.`. The assumptions
are exactly the generic domain described above, plus the displayed arguments.
Every row was compared with its fully explicit, universe-visible output and
its complete source definition or proof. No concrete issue was found in any row.

| Declaration | Elaborated claim and source assessment |
|---|---|
| `threeWayQuickSort` | A total function `List α → List α` under the source linear order. Its literal three-filter body and only two strict recursive calls match the exercise; the attached-list length proof establishes the required decreases. |
| `threeWayQuickSort_nil` | Exact list equality on the empty input, universally quantified over the type and order, without an element or default-pivot parameter. |
| `threeWayQuickSort_cons` | For every pivot and tail, exact ordered-list equality to the strict-left recursive output appended to the held-pivot/equal block and strict-right recursive output. Predicate directions and right association are correct. |
| `threeWayQuickSort_singleton` | For every supplied element, the singleton is unchanged. It does not require a distinctness, nonempty-tail or extra order hypothesis. |
| `threeWayQuickSort_cons_partition` | The same ordered value recurrence through projections `.1`, `.2.1` and `.2.2` of the shared triple; no recursion on `.2.1` and no execution-cost assertion. |
| `threeWayQuickSort_perm` | For every input, the actual output is a `List.Perm` of that input, including duplicate occurrences. Recursive outputs, the complete equal block and exactly one pivot participate in the derivation. |
| `threeWayQuickSort_length` | Output length equals input length for every list, derived from the public permutation law. |
| `mem_threeWayQuickSort` | For every input and element, membership in the actual output is equivalent to membership in the input, in both directions. |
| `threeWayQuickSort_multiset` | Equality of the two `Multiset α` coercions, not merely support equality. It follows from the proved permutation through the existing quotient interface. |
| `threeWayQuickSort_support` | Equality of the two sets defined by output/input membership, derived from the public membership equivalence. |
| `threeWayQuickSort_sorted` | Every actual output satisfies `KeySorted id`; there is no sorted-input premise. The imported key-order observation resolves to the same linear order on `α`. |
| `threeWayQuickSort_correct` | The conjunction of actual-output nondecreasing order and full permutation of the input, for every list. It introduces no new sorting carrier or keyed-stability assertion. |
| `threeWayQuickSort_replicate` | For every natural size and supplied element, sorting the repeated list returns that exact list. Size zero is included; the successor proof returns the equal block after two empty strict calls. |

## Every example declaration assessed: 23 of 23

All names in this table have prefix `Examples.ThreeWayQuickSort.`. The checked
examples use the intended public definitions and theorems. Their conclusions
and expected cases remain those fixed before implementation.

| Declaration | Elaborated case and connection assessment |
|---|---|
| `empty_input` | Arbitrary `Type u` and `LinearOrder`, with exact empty output and no element requirement; uses the public nil law. |
| `singleton_input` | Arbitrary source-domain element and exact singleton output; uses the public singleton law. |
| `all_equal_buckets` | The actual tail `[2,2]` at pivot `2` has exact shared triple `([], [2,2], [])`. |
| `all_equal_source_equation` | The actual source call on `[2,2,2]` expands to two recursive calls on `[]` around the complete three-element middle block. This consumes the public source equation. |
| `all_equal_input` | Exact result `[2,2,2]`, connected to the generic replicate law. |
| `all_equal_family` | Arbitrary universe, linear-order type, natural size and supplied element; directly exercises the public replicate law, including zero. |
| `mixed_buckets` | Pivot `2`, tail `[3,1,2,0,3,2,1]`, and exact ordered buckets `([1,0,1], [2,2], [3,3])`. |
| `mixed_source_equation` | The source recurrence retains those actual child inputs, one pivot and both equal tail occurrences with the intended append association. |
| `mixed_left_child` | The actual source sorter on `[1,0,1]` returns `[0,1,1]`, established through its public recursion equation. |
| `mixed_right_child` | The actual sorter on `[3,3]` returns `[3,3]`, through the public replicate law. |
| `mixed_value` | `[2,3,1,2,0,3,2,1]` returns exactly `[0,1,1,2,2,2,3,3]`. The proof consumes both fields of general correctness and ordinary sorted-permutation uniqueness; it does not appeal to an independent sorting implementation. |
| `mixed_multiset` | Full output/input multiset equality for the fixed mixed input, through `threeWayQuickSort_multiset`. |
| `mixed_multiplicities` | Counts in the actual output are respectively `1,2,3,2` for `0,1,2,3`; all four equalities consume the public permutation's count observations. |
| `mixed_length` | The actual mixed output has length 8, through the public length theorem. |
| `mixed_support_boundary` | The actual output contains `0` and excludes `4`, through the public membership theorem. The negation and conjunction have their intended scopes. |
| `absent_pivot_buckets` | Pivot `0` and tail `[2,1]` yield `([],[],[2,1])`; no membership assumption is supplied. |
| `absent_pivot_source_equation` | The actual sorter on `[0,2,1]` recurses on `[]` and `[2,1]`, with `[0]` between them; it consumes the public shared-value recurrence. |
| `absent_pivot_child_decrease` | Four facts are conjoined: `0` is absent from `[2,1]`; greater-child length is 2; it is below parent length 3; it is not below tail length 2. This is a concrete inhabited boundary, not an impossible premise. |
| `absent_pivot_value` | The actual source sorter returns `[0,1,2]` on `[0,2,1]`, through its public recursion equation. |
| `omitted_pivot_boundary` | A fixed altered root uses the proved correct child results but only the two equal tail values in the middle. It is sorted and is not a permutation of the original input. |
| `omitted_equal_block_boundary` | A fixed altered root keeps only the held pivot between the correct child results. It is sorted and is not a permutation of the original input. |
| `duplicated_pivot_boundary` | A fixed altered root has four middle copies of `2`, retaining an extra pivot. It is sorted and is not a permutation of the original input. |
| `misplaced_pivot_boundary` | A fixed altered root moves one pivot ahead of the correct left result. It is a permutation of the input and is not sorted. Both sides of this contrasting contract test elaborate in the intended order. |

## Satisfiability and boundary interpretation

The mixed and absent-pivot examples are concrete natural-valued executions,
so their order and membership conditions are directly satisfiable. Duplicate
inputs are exercised both concretely and as a size-polymorphic family. The
mixed input retains all eight occurrences: one `0`, two `1`s, three `2`s and
two `3`s. The absent-pivot case demonstrates why a strict tail bound would be
false while the actual parent decrease is valid.

The altered roots are fixed let-bound list expressions, not universally
assumed arbitrary results or conclusions conditional on impossible premises.
Their correct child results are `[0,1,1]` and `[3,3]`, established by public
sorter theorems. The exact altered values are:

| Root alteration | Result after the proved child equalities | What the checked boundary distinguishes |
|---|---|---|
| Omit held pivot | `[0,1,1,2,2,3,3]` | Nondecreasing, but only two copies of `2`. |
| Omit equal tail block | `[0,1,1,2,3,3]` | Nondecreasing, but only one copy of `2`. |
| Duplicate held pivot | `[0,1,1,2,2,2,2,3,3]` | Nondecreasing, but four copies of `2`. |
| Move pivot before left output | `[2,0,1,1,2,2,3,3]` | All occurrences retained, but the leading `2` precedes the smaller `0`. |

These are explicitly local root-assembly witnesses, not purported executions
of globally modified recursive algorithms. They show why the source requires
both order and occurrence preservation. They do not by themselves establish
absence of equal-bucket recursion; that property was assessed separately from
the complete defining body and exact recurrence.

## Outcome, limits and hold

No concrete issue was found in any of the 36 elaborated declarations, their
quantifiers, domains, hypotheses, equality/relation directions, source
operations, or retained connected cases. The two proof corrections changed
only the defining decrease proof. Their original commits and both failed
attempts remain retained in the existing handoff and provenance. The successful
module builds and subsequent explicit statement inspection now validate this
source slice at the stated central candidate.

This result makes no numerical cost, expected-work, stability, stack or tail
recursion claim. Shared partition/source-value correspondence remains distinct
from traversal and resource correspondence. The complete Chapter 2 review
base remains accepted Chapter 1 at
`07e480f6ec9958d4975bb90151005b84f2907614`. The complete candidate check and
audit, independent Standards and Spec reviews, immediate candidate verification
and any acceptance/integration decision remain root-owned gates. No unit or
coverage row is accepted by this author assessment.

Only this report and an appended section of the existing implementation
handoff were written. The source/ref/build/cache hold remains in force; the
author branch and source files remain unchanged and clean. No compiler or
background build was started by this assessment.
