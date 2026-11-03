# Increasing subsequences from checkpoint 233

Issue [#164](https://github.com/VladimirMarko/conaled/issues/164) reconstructs
Chapter 11 `Segments` from `subseqStep` through the final longest-upsequence
results. Feasibility means standard `List.Sublist` and pairwise strict integer
order. Optimality compares length with every feasible sublist, independently of
any generator or frontier.

## Operations and shared laws

`Applications/Subsequences/Candidates.lean` uses `List.sublists'` for the source
skip-block-before-take enumeration and `List.sublists` for its interleaved
variant. The source cons equations and both `*_eq_foldr` bridges establish exact
ordered equality with the printed algorithms. Completeness, permutation and
`2 ^ length` entry counts reuse Mathlib. Permutation preserves repeated
occurrences; it does not identify the two enumeration orders. The helper
`subseqExtend_perm` reuses `List.flatMap_append_perm`.

The executable `up` remains the adjacent `zipWith`/Boolean-and test.
`up_correct` relates it to pairwise strict order. `canPrepend_iff` requires an
already increasing tail; this premise is needed to infer every later comparison
from the head comparison. Empty and singleton lists pass. `filter_subseqs`
uses `SquareKit.ListFusion.foldr_reachable` with the true invariant because
`filter_subseqStep` holds for arbitrary lists, including duplicate candidates.
It preserves output order and multiplicity.

`lus0` reuses `Segments.maxsWith`. The new selector facts
`Segments.maxsWith_sublist` and `maxsWith_eq_filter_of_mem` live beside that
operation and give the exact stable filter of all maximum occurrences.
`mem_lus0` is an equivalence with independent global optimality. Lengths embed
into integer scores without overflow or extra assumptions. These selector
helpers were located in the source's later subsequence section; they were not
part of the earlier #161 reconstruction.

`Applications/Subsequences/Frontier.lean` keeps the actual source step: filter
by `canPrepend`, prepend, merge by non-strict length order, and apply
`Optimization.Thinning.thinBy`. Merging uses standard `List.merge`;
`lengthMerge_source` specializes the existing `Applications.Sorting.sourceMerge`
recurrence to length keys. `sourceMerge_length_sorted` reuses the sorting
library's key-order theorem. The first list wins a merge tie. There is no new
recursive merge implementation.

`UpDominates` treats the empty candidate separately. Among nonempty lists a
representative has at least the candidate's length and at least its head value,
so any new element that can precede the candidate can precede the
representative. The source compatibility and frontier-order proofs are retained.
On length-sorted input, the actual adjacent `bump` guards produce strictly
increasing lengths and strictly decreasing nonempty heads. That premise is
necessary: generic adjacent thinning does not guarantee an antichain.

`lusStep_refinement` gives `IsThinning` relative to the **merged** intermediate
list. `lusStates_refinement` gives `Represents` relative to the unmerged
`upStates` enumeration: origin and coverage hold, but order may change. The
retained `[[], [4], [1,3]]` frontier for `[4,1,3]` is not a sublist of its
unmerged enumeration. The two relations are deliberately not interchanged.

`Applications/Subsequences/Selection.lean` selects the last frontier entry.
`lengthOrdered_last` uses Mathlib's pairwise/get-last theorem. `lus_optimal`
transports this local minimizer through `minimizer_of_represents`, using
`OrderDual Nat` and dominance's length inequality. Its conclusion quantifies
over all increasing input sublists. The selected list belongs to `lus0`; it
need not equal that list's first optimum. Retained frontier entries are bounded
by optimum length plus one, hence by input length plus one. These are list-entry
bounds, not runtime, allocation, distinct-subset or physical-memory claims.

## Witness and length consumers

`Applications/Subsequences/Observation.lean` relates `LusOptimal` to the shared
`Optimization.minimizers` semantics. `witnessSquare` uses `selectionSquare`.
`lengthSquare` is the actual relational composition of that witness selection
with `Optimization.observationSquare List.length`. The composed observation is
attained by an independently optimal witness, and all independent optima have
the same reported length.

The new `Optimization.observationSquare` extracts the existing segment score
observation. It retains the problem index and sends the permitted-output set to
its actual image under an arbitrary observation. It requires no objective,
order, injectivity or inverse. Its two clients are subsequence length and
contiguous-segment sum. `Segments.scoreObservation` now forwards to this shared
construction; its type, implementation, image semantics, and all existing
segment observation theorem statements are unchanged. The original
`Examples.BoundedSegments` checks remain part of targeted validation.

## Checked applications and statement review

The worked cases distinguish mathematical feasibility from source tie choices.
For `[1,3,2]`, both `[1,2]` and `[1,3]` are increasing length-two sublists, while
the source frontier selects `[1,3]`. For `[1,1,2]`, two enumeration occurrences
of `[1,2]` survive the all-optima filter. For `[4,1,3]`, length merging reorders
the frontier. Source computations already supplied these expected values;
the reconstruction adds checked connections to the shared refinement and public
witness/length contracts. The merged intermediate list is
`[[], [3], [4], [1,3]]`: merging places `[4]` before the length-two candidate.

`Examples/IncreasingSubsequences.lean` retains these applications:

| Cases | Public contracts exercised |
| --- | --- |
| `empty`, `singleton`, `increasing`, `negative` | Empty optimum, singleton/full-input uniqueness, negative integer domain, witness and composed length consumers. |
| `generator_orders`, `duplicate_entries` | Different exact orders, shared permutation, and entry count with duplicates. |
| `strict_boundary`, `repeated_filter` | Adjacent-test correctness and exact filter fusion; `[1,1]` is not strictly increasing. |
| `repeated_all_optima`, `repeated_witness`, `repeated_membership` | Duplicate optimal occurrences versus one selected value and independent global membership. |
| `reordered_frontier`, `reordered_refinement`, `not_global_sublist`, `local_merged_refinement` | Actual frontier values and the distinct global membership/local sublist contracts. |
| `actual_adjacent`, `frontier_order`, `frontier_antichain` | Adjacent thinning's arbitrary-input boundary and the stronger reachable-frontier properties. |
| `tie_choices`, `tied_global`, `alternative_global`, `tied_length` | Exact source tie choice, two independent witnesses, and equal observed optimum length. |
| `decreasing`, `frontier_bound` | A decreasing input's chosen singleton and the retained-entry bound. |

Statement review checked the source and destination families together. Generator
claims are universe-generic and preserve occurrences. Increasingness, dominance
and optimization retain the source `Int` domain and strict comparisons. The
all-optima contract is membership plus a global length bound, with exact output
order established separately. Frontier order assumes the source length-sorted
intermediate states, which the merge theorem supplies. Empty lists are not
silently comparable to nonempty candidates under dominance. Nonempty reachable
frontiers justify the last-element default. No correctness theorem assumes its
final optimum as a premise. The relational observation preserves the problem
and image membership, not uniqueness of witnesses.

## Provenance and remaining scope

Reference: [`adwh-checkpoint-233`](../history/algorithm-design-haskell/README.md),
member `project/adwh-lean/ADWH/Chapter11/Segments.lean`, SHA-256
`a4133351a867423bca581ed9036d7f0ee8adbb04fcbf813d5d4faa312020c058`.
Both the preserved ZIP member and the extracted reference were hashed before
handoff. Historical code remains unchanged and outside the public build.

The [declaration ledger](adwh-increasing-subsequences-provenance.tsv) accounts
for all 244 named source declarations: 138 previously reconstructed by #161,
85 adapted here, 18 reconstructed through shared operations or proofs, and
3 pre-existing deferrals (`DownScore`, `downScoreLE`, `minWithBy`). The last three
are the generic selector helper scope recorded in #161; its used integer
maximum specialization is already reconstructed. No declaration from
`subseqStep` through the end of the source remains deferred. Anonymous source
examples are represented by the named application cases above, not counted as
separate source declarations. Newly introduced shared observation/refinement
bridges are local constructions, not source declarations.

Other subsequence representations, edit distance and resource cost models
remain future work. This slice makes no claims about execution complexity.
The targeted command is `direnv exec . lake build Examples.IncreasingSubsequences
Examples.BoundedSegments`; full fresh build, exhaustive audit and independent
reviews are integration checks performed by the supervising workstream.
