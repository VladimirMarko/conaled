# First-pivot quicksort and arbitrary-suffix value implementation

Author handoff within the existing active FDSA-002 implementation/review loop,
4 November 2026. **Uncompiled source draft; no acceptance or checked coverage is
claimed.** The exact compiler is being prepared by the coordinator, who has not
released a private build to this worker. No Lean command was run by the author.

Worktree: `conaled-ch02-quicksort`; branch: `work/fdsa-ch02-quicksort`.
Starting accepted Chapter 1 base:
`07e480f6ec9958d4975bb90151005b84f2907614`.
Only `Applications/Sorting/QuickSort.lean` and `Examples/QuickSort.lean` are
changed in the repository. No unaccepted shared foundation is imported, and no
public root, coverage, ticket, dependency, tooling or global record is edited.

## Source and preserved scope

The recovered source PDF was independently hash checked against
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The actual printed p.16 / PDF p.22 first-pivot definition and correctness
passage, and printed p.28 / PDF p.34 Exercise 2.2 were read. The re-extracted
Chapter 2 text has different line positions from older preparation notes;
the pinned PDF identity and page references are unchanged. Source recovery
is recorded separately in `provenance/recovery-20261104-restored/source-recovery.json`.

This subset addresses the value content of C02-017–023 and Exercise 2.2 /
C02-101. All 112 Chapter 2 obligations remain in force, including the frozen
requirements and explicit scope reconciliation. C02-024's average/randomized
claims, the exercise cost model, both ordinary append charges, the three-way
variant, and all other cost and chapter requirements remain pending.

## Definitions and reuse

- `quickSortBy` is an actual recursive operation. It chooses the head pivot,
  filters only the tail with `lt element pivot`, and uses the Boolean complement
  for the right child. Its body retains both ordinary append occurrences.
  Equal-key elements therefore go right in the lawful key specialization.
- `quickSortOn` supplies the decidable strict key comparison. Its public cons
  equation proves that the complementary filter equals the source's
  `pivotKey ≤ elementKey` filter under `LinearOrder`. The source contract is
  unchanged; arbitrary payloads acquire no order, equality or default value.
- `quickSortAccBy` implements the proposed Exercise 2.2 solution by the actual
  nested calls `A left (pivot :: A right suffix)`. The body contains no append
  and does not call the ordinary sorter. The book asks for this construction
  and its all-suffix property but does not print a worker recurrence; this
  proposal is not attributed to the book as supplied code.
- Both definitions and their recursive proofs use first-input length only.
  The pinned `List.length_filter_le` proves strict decrease below the parent
  cons length, independently of the suffix and any comparator law. There is
  no fuel, partial definition, element choice or combined-length assumption.
- Occurrence proofs compose the actual child permutations with the existing
  `List.filter_append_perm`, `List.perm_middle` and permutation append/cons
  operations. Length and membership are derived from permutation.
- Sortedness uses the existing `KeySorted` observation and
  `List.pairwise_append` / `List.pairwise_cons`. The comparator contract is
  restricted to original input members, recovered from child permutations.
  Source review removed an unused reflexivity assumption: the observed key
  relation requires only existing `IsTrans κ (· ≤ ·)`, with no global
  comparator laws, totality, antisymmetry or decision procedure for `≤`.
- The all-suffix proof instantiates its left induction hypothesis at the
  actual `pivot :: A right suffix`, then applies the right hypothesis at the
  original suffix. Only ordinary list algebra closes the value equality.
  Its keyed form requires comparison operations and decidability, not order
  laws. The empty-suffix sorting corollary separately uses lawful key order.

## Requirement-to-declaration connections

| Requirement | Proposed declarations and existing interfaces |
| --- | --- |
| C02-017 | `quickSortBy`, its nil/cons equations and length termination; `quickSortOn_cons` is the exact source strict-left/nonstrict-right equation. |
| C02-018 | `quickSortBy_perm`; `Examples.QuickSort.source_multiset` applies `Quot.sound` to that occurrence permutation. |
| C02-019 | `source_filter_multiset` consumes the pinned `Multiset.filter_coe` quotient/filter law. |
| C02-020 | `source_complementary_multiset` composes `Multiset.filter_congr` and `Multiset.filter_add_not`; `source_key_partition` instantiates `< pivot` and `pivot ≤`. Complementarity need only hold on the input multiset, a stronger usable result than the source's global premise. |
| C02-021 | `source_sorted_append` is the exact existing pairwise append characterization specialized to `KeySorted`, with no unnecessary order law. |
| C02-022 | `mem_quickSortBy` and its set equality client `source_support`, derived from the full occurrence permutation. |
| C02-023 | `quickSortBy_sorted_compatible_on` and the source `quickSortOn_correct`. |
| C02-101 | Actual `quickSortAccBy`, source-specialized worker equation, universal `quickSortAccBy_eq_append` / `quickSortAccOn_eq_append`, occurrence corollary and empty-suffix correctness. |

## Examples and statement review

The independent expected values were already recorded in the stopped
accumulator case preparation. Before these files, the accepted base had no
first-pivot quicksort operation or public correctness/suffix theorems to
connect to those expectations. This was a missing implementation and theorem
connection, not a claimed compiler failure. The new examples retain the
expectations and consume public results:

- The mixed source step exposes pivot `2` and exact children `[1,0]`, `[2,3]`
  for `[2,1,2,3,0]`. Its final value `[0,1,2,2,3]` uses the proposed general
  sortedness/permutation theorem and independent sorted-permutation uniqueness.
- The mixed worker step exposes the actual nested right-result suffix. The
  all-suffix theorem and mixed prefix value give `[0,1,2,2,3,4,0,2]` for suffix
  `[4,0,2]`. This suffix is unsorted, overlaps the input, and repeats its pivot.
- Empty and singleton first inputs preserve that exact suffix. All-equal
  input `[2,2,2]` exposes the right-recursion tie convention and retains every
  occurrence in the final value. `Empty` payload cases use the actual nil laws.
- The arbitrary-comparator occurrence client combines permutation, length and
  worker permutation without any comparison-law premise.
- The arbitrary payload client uses keys `[1,0,1]` with distinguishable but
  otherwise unstructured first/middle/last payloads. The source recurrence and
  singleton equations give the independently expected middle/first/last order;
  the suffix theorem preserves every arbitrary payload suffix.
- A comparator agrees with integer key order on `[2,0,2,1]` but deliberately
  reverses it outside the nonnegative domain. Its local compatibility proof
  feeds the proposed generic sortedness theorem, while a separate `(-1,0)`
  witness demonstrates that no global comparator contract is supplied.
- The explicit `[2]` / `[1]` example shows that a sorted suffix alone does not
  make the entire accumulated result sorted. The main law makes no such claim.

Source-level statement review checked types, quantifiers, partition direction,
tail-only filtering, full multiplicities, actual nested recursive arguments,
first-length termination, and the scope of every law premise. It found the
unused generic reflexivity premise noted above and removed it without changing
the source-specialized contract. No circular correctness premise, sorted-
suffix premise, distinctness assumption, payload typeclass or new axiom is
introduced. Full elaborated-type inspection and meaningful checked cases still
require the coordinated compiler run; no check result is inferred from source
readback.

These are value claims. They establish no allocation count, runtime bound,
tail recursion, stack bound, probability theorem, cost-preserving append
reassociation or general stable-sort contract. The selected payload example
records its concrete source order and does not substitute for a stability theorem.

## Validation and handoff state

Source readback is complete. Compilation remains explicitly held by the
coordinator while the exact private environment is qualified. No focused
module result, complete candidate check, exhaustive axiom audit, independent
Standards/Spec pass or immediate candidate verification exists for these files.
The normal integrated acceptance gates remain mandatory on the coordinator's
eventual immutable candidate. The author will preserve any proof corrections
and their actual compiler evidence rather than changing expected mathematics
to obtain successful elaboration.
