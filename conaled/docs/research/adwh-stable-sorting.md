# Stable key sorting reconstruction (#160)

`Applications.Sorting.StableSort` specifies sortedness by key, preservation of
record multiplicities, and preservation of each equal-key filtered sequence.
It contains no sorting implementation. Records need no order, and different
payloads with the same key remain distinguishable in the observations.

Both standard `List.mergeSort` and Mathlib `List.insertionSort` satisfy this
specification. `StableSort.unique` then proves their exact agreement under a
partial order on keys. The proof identifies the first key using sortedness
and permutation, identifies the first record using the equal-key filter, and
continues with the tails. Antisymmetry is required only on keys. The standard
Mathlib theorem equating merge sort and insertion sort via an antisymmetric
record relation would not justify stability for these key preorders, so this
reconstruction does not use it.

## Standard operations and laws

`mergeBy`, `sortBy`, `sortOn`, and `insertionOn` abbreviate standard operations.
`KeySorted` is standard `List.Pairwise` on the pulled-back key relation.
Comparator operations remain Boolean functions; compatibility is supplied
separately to the relevant theorems. No new comparator class or sorting
implementation is introduced.

`merge_sorted_compatible_on` constrains only a left-input record against a
right-input record. `sortBy_sorted_compatible_on` constrains only records
belonging to its actual input. Their global forms are specializations. The
law allows either choice on equal keys and therefore proves sortedness,
without asserting stability for an arbitrary comparator. Permutation is
unconditional. The canonical key comparison chooses the left side on ties;
`mergeBy_filter` preserves each key's left filtered sequence followed by its
right filtered sequence. `mergeBy_spec` packages the result for sorted blocks,
and `mergeBy_eq_sortOn` connects block merging to whole-input stable sorting.

`sortOn_stable` uses Lean's sorted-sublist preservation theorem for merge
sort. The insertion-sort contract uses Mathlib's corresponding theorem.
`stable_of_sublist` turns these independent sublist observations and
permutation into exact filter equality. The sorters need no antisymmetry for
correctness or stability. Their equality uses the separate uniqueness result.

`StableSort.map` transports the whole specification through a key-preserving
record map. Such a map may discard or identify payloads. `sortOn_map` proves
that transforming records before sorting equals transforming the sorted
output. The checked client composes payload length with parity, applying the
specification transport twice and the executable equality once.

`SourceMerge.lean` retains only the source's left-tie merge
recurrence and its standard-library equivalence. This bounded adapter makes
the source comparison reviewable. Production merge and sort operations use
standard library functions. The source's alternating splitting, tree builders,
other sorting algorithms and operation counts are not imported.

## Provenance and scope

The immutable source is
[`adwh-checkpoint-233`](../history/algorithm-design-haskell/README.md).
The three extracted members were verified against the preserved manifest:

| Archive member | SHA-256 |
|---|---|
| `project/adwh-lean/ADWH/Chapter05/KeyedMerge.lean` | `e2880c1ab1a5151a0a5fa81f5e4fa9e8cd20e34a1c8ced56b590265536fa0ce2` |
| `project/adwh-lean/ADWH/Chapter05/KeyedMergeDomain.lean` | `a58d62deae885f4d602650d4ded9892554d96537d285a5efb56395c6bf79a555` |
| `project/adwh-lean/ADWH/Chapter05/Sorting.lean` | `6fdb3d8f79783c1e047280ca9b55a46ef6d07b288d7ce144227506954a7f375d` |

The [declaration ledger](adwh-stable-sorting-provenance.tsv) records all 84
explicitly named top-level definitions, inductives and theorems in those
members. Constructor/generated names and anonymous examples are not separate
rows. Each row records the original qualified name, source hash, destination,
disposition and scope. All 16 named declarations in `KeyedMerge` and both in
`KeyedMergeDomain` are reconstructed. Of `Sorting`, only `merge` and
`merge_eq_List_merge` are retained, as `sourceMerge` and
`sourceMerge_eq_merge`. Its other 64 named declarations remain individually
marked deferred, including specialized source-merge wrappers, partition and
halving, tree/direct sorts, natural runs and comparison accounting.

The independent observation, uniqueness, insertion-sort realization,
sorted-block agreement and record-map transport are new local connections.
This slice does not establish whole-family reconstruction, acceptance of
the other source sorting algorithms, or a timing improvement.

## Statement review and checked development

The first chosen case was the signed-key input
`[(2,"first"),(-1,"negative"),(2,"last")]`. Its independently justified output
is `[(-1,"negative"),(2,"first"),(2,"last")]`: the negative key moves first,
and the two key-2 payloads retain their original order. Standard sorters could
compute this case before the reconstruction; the missing obligation was their
connection through an independent stable observation and uniqueness theorem.
`expected_spec`, `merge_sort_records`, and `insertion_sort_records` retain that
connection without reducing either sorting implementation.

All public claims and the helper proof received statement review:

| Claim group | Assumptions and interpretation checked |
|---|---|
| `KeySorted`, `Stable`, `StableSort`, `stable_of_sublist` | Finite lists; full records, not just keys, survive filtering. Permutation preserves multiplicities. Stability compares every key. The sublist premise refers to original filtered input; equal lengths from permutation turn it into equality. |
| `StableSort.unique` and its helper | Same original input, sorted outputs, permutation, and equal-key sequence equality. `Std.IsPartialOrder` is on keys only. Empty lists, heads and tail cancellation are covered. The result does not infer stability from sortedness and permutation. |
| Merge compatibility and filter results | Only actual cross-input comparisons are premises in the local theorem. A preorder suffices for compatibility sortedness and equal-key filtering. Canonical merge sortedness requires a linear preorder. Ties select left, retaining the left-before-right filter order. |
| Sort compatibility and fixed points | The local theorem restricts both records to the original input, including recursive sorted sublists via permutation. It needs only a preorder on keys. `sortOn_sorted_fixed` assumes only the input's pairwise key order and decidable comparisons, matching the source's lack of global order-law requirements here. |
| Canonical sort and insertion-sort specifications | Linear-preorder keys suffice for each sorter's sortedness and stability. Equality decisions are on keys only. No payload order or equality decision is needed. |
| Exact realization and block agreement | Key antisymmetry is explicitly added through `Std.IsLinearOrder` to consume uniqueness. Sorted block hypotheses are retained for merging. |
| Record-map transport and executable equality | Source and target record types can differ. A global key-preservation equation is proved for each map, and no injectivity is assumed. Transport preserves mapped multiplicities and mapped equal-key sequences. Exact sort commutation uses the uniqueness assumptions explicitly. |
| Source adapter | The literal recurrence compares `≤` and selects the left entry on equality. Exact agreement with standard merging requires only decidable comparison; the key pullback introduces no record-order law. |

The reconstruction weakens the source's `Std.IsLinearOrder` requirements to
`Std.IsPreorder` or `Std.IsLinearPreorder` where the proofs do not need more.
It does not silently strengthen any recovered source theorem. The new
uniqueness result states its key-antisymmetry requirement separately.

`Examples.StableSorting` also retains empty input, sorted fixed points,
left-tie filtered merge, stable block merging, the literal source bridge,
composed key-preserving transformations, and an input-local comparator. That
comparator behaves correctly on the three nonnegative input keys but violates
the global compatibility law at keys -1 and 0. Its sortedness proof consumes
`sortBy_sorted_compatible_on`; its permutation proof consumes `sortBy_perm`.
No stability claim is made for arbitrary compatible comparators. A separate
checked counterexample swaps two distinct equal-key payloads: sortedness and
permutation hold, but filtering at that key disproves stability.

The targeted check is `direnv exec . lake build Examples.StableSorting`.
`SquareApplications.lean` imports the examples, so all four library modules
and their clients enter the normal build and exhaustive axiom audit. The
coordinating session owns fresh full integration checks and independent
Standards/Spec and supervising intent reviews.
