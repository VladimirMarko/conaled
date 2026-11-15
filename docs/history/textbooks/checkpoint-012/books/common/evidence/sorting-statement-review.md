# Sorting integration: intended claims and statement review

Full integration base: `9175737c2b14ef738cfb6c2cdc68d885c0805ddd`.
Local issue: INT-012. This is implementation evidence, not independent approval.

## Intended connection

VFA's `compareSwap_perm` preserves all occurrences for any Boolean comparison.
FDSA's `sorters_eq_at` identifies outputs from independent whole-list correctness
contracts when the relation is antisymmetric on the actual records. The new
`sort_after_compareSwap` uses those public laws to prove the preprocessing does
not change a complete sorter's output. Its comparator needs no ordering laws.
This connection was missing; the existing source theorems already supplied its
premises, so no artificial failing theorem was required.

The first-pivot quicksort and independent floor-split merge sort both realize
current conaled's `sortOn id` specification. The former's equality follows via
`SortUniqueness.first_pivot_eq_floor`; the latter already uses `StableSort.unique`
through `sortFloorOn_eq_sortOn`. `jointSquare` uses the existing `synchronized`
agreement pullback and `synchronize`. Its actual paired outputs agree through
`synchronize_agrees`, rather than a new interface or duplicated correctness proof.

## Quantifiers and mathematical boundaries

The generic claim quantifies over all lists, all Boolean first-pair comparators,
and all complete sorters meeting pairwise-order/permutation contracts. Only
antisymmetry is added to those local contracts; no totality, finiteness, payload
equality, inhabitance or cost premise is inferred. The concrete squares use
`LinearOrder` on records and observe the full returned list, preserving repeated
occurrences. Inputs to the joint square carry the required agreement witness.
The paired-output client constructs that witness from identical inputs.

This is value equality. Independent execution recipes and their costs remain
separate. Antisymmetry on keys alone does not give antisymmetry on records when
the key loses information. No stable-sort claim is made about arbitrary first-pair
preprocessing; it can reverse distinct equal-key records.

## Retained connected cases

- `mixed_duplicates` transports the existing independently stated floor-sort
  expectation `[0,1,1,2,2,2,3,3]` through the new universal paired-output theorem.
- `equal_key_order_matters` uses constant natural keys on Boolean records and
  an always-swap comparison. The stable output changes from `[false,true]` to
  `[true,false]`. It uses `sortFloorOn_eq_sortOn` and the public fixed-point law
  `sortOn_sorted_fixed`, then checks the resulting finite inequality.
- The retained VFA `Examples.ComparisonPermutations.not_whole_list_sorted`
  demonstrates that first-pair comparison itself is not a whole-list sorter.

The first concrete boundary proof tried direct reduction, which stalled at the
well-founded floor-sort definition. Switching to the public correspondence and
fixed-point theorems changed only the proof, not the statement or expectation.
No hypotheses were weakened to obtain compilation. No new axioms or admissions
were introduced.

## Focused validation

`validation.json` records the exact source hash, command, before/after identity
and successful exit. `lake build Examples.TextbookSorting` through the verified
native route passed in 8.27 seconds (707 jobs, including cached dependencies).
The required full committed-candidate check/audit and independent Standards/Spec
reviews remain coordinator gates. The module is included by SquareApplications.
