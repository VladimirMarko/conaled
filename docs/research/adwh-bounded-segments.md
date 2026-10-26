# Bounded prefixes and maximum segments (#161)

`Segments.maxSegmentThinScan` returns a globally maximum-sum contiguous segment
whose length is at most the supplied natural bound. Empty segments are allowed.
The selected witness retains the source's first-maximum suffix-order tie rule;
the separate `msp0` and `mss0` functions retain every maximizing occurrence in
candidate order.

## Reconstructed interface and shared mathematics

`Applications/Segments/Candidates.lean` uses standard `List.IsPrefix` and
`List.IsInfix` for independent feasibility. `inits` and `tails` abbreviate the
standard list enumerators. `inits_eq_foldr` recovers the source's prefix fold
exactly. `PrefixOptimal` and `SegmentOptimal` compare against every independently
feasible candidate under the length bound, including the empty candidate.

The all-optima selector retains the source's score cache, maximum and filtering
operations. `maxsWith_cons` is an exact filtering equation and therefore retains
order and duplicate occurrences. Its existence argument now uses the accepted
`Optimization.Thinning.argmin_correct` with `OrderDual Int`. `mem_msp0`,
`mem_mss0` and `mem_maxSegmentExhaustive` establish independent global-optimum
membership. `mss0_membership_refinement` asserts membership equivalence with
exhaustive segment enumeration; it is not presented as exact list equality.

`Prefixes.lean` retains the actual `cut`/`op` fold and dropWhile-based
`thin`/`op2` frontier. `cut_eq_filter` requires strictly increasing lengths and
the bound invariant. `thin_eq_filter` requires strictly increasing sums. Raw
`thin [[-1],[2],[-3]]` stops at the positive entry and retains the later negative
entry, so unconditional replacement by a positivity filter would be wrong.
`boundedStates_eq_filter` uses `SquareKit.ListFusion.foldr_reachable`;
`boundedPrefixes_eq_filter` then recovers exact source candidate order.

`thinnedPrefixes_refinement` packages the actual frontier's sublist and
independent length/sum dominance coverage in the accepted
`Optimization.Thinning.IsThinning` interface. `msp1_optimal` derives global
optimality through `minimizer_of_represents` with reversed sum order. The
source's shortest-optimal-prefix, antichain and candidate-cardinality contracts
are retained. This is the source dropWhile implementation, not the existing
adjacent-pair `thinBy` implementation. The unconditional `pruneFold` contract
requires correctness on arbitrary states; the source `cut` and filter bridges
instead need the proved reachable order/bound invariants.

`scanrTotal` abbreviates Lean's inclusive `List.scanr`.
`scanrTotal_source_cons` proves the source's head-based recurrence, and
`scanrTotal_eq` proves exact suffix-fold order, including the final seed.
The accepted parallel scanner requires a monoid and a homogeneous multiplication
step. Here `op2` takes an integer and a list-of-prefixes state; no such monoid
law is assumed. Standard right scanning and the applicable arbitrary-state
fold-fusion theorem are reused without a parallel-execution claim.

`Maximum.lean` implements `maxWith` using the existing `argmin`, an `OrderDual Int`
objective and an empty-input fallback. The nil, singleton and cons-cons theorems
recover the source foldr1/Down recurrence exactly, including first-biased ties.
`FirstMaximum` is an alias of `Optimization.FirstMinimum` specialized to
`OrderDual Int`; Bracketing uses the same predicate specialized to `Nat`.
This independent decomposition requires strictly smaller scores before the
chosen occurrence and no greater scores after it. Certification and its
converse reuse `Optimization.argmin_firstMinimum` and
`Optimization.argmin_eq_some_of_firstMinimum`. Membership and maximality
reuse `argmin_correct`. The public source names and their assumptions remain
unchanged; `maxWith_eq_of_firstMaximum` certifies an exact answer through the
shared converse.

`maxSegmentThinScan_eq` proves exact equality with suffix-prefix realization.
`maxSegmentThinScan_optimal` compares the result with all bounded contiguous
segments. `maxSegmentThinScan_mem_mss0` states membership of the single witness
in the all-optima result. Equal optimum scores, exact witnesses and full output
lists remain separate claims.

## Witness and score consumers

`Observation.lean` identifies `SegmentOptimal` with the accepted optimization
library's minimizers of the independent feasible set. `witnessSquare` uses
`Optimization.selectionSquare`. `scoreObservation` forgets the witness while
retaining the problem and mapping its set of permitted outputs to scores.
`scoreSquare` is their actual `Relational.compose`.

`selected_witness_optimal` consumes the first square's preservation proof.
`selected_score_attained` consumes the composed square and produces an optimal
segment attaining the reported score. `selected_score_eq` compares that score
with any independently certified optimum. The module also proves that every
strictly negative input produces the empty witness, using the global optimum
and Mathlib's strict sum comparison.

## Checked cases and statement review

The starting cases were the tied inputs `[1,1,-10,2]` and `[2,-10,1,1]` at bound
2. Their optimum score is 2, but suffix order selects `[1,1]` in the first case
and `[2]` in the second. Source computation alone did not connect these choices
to the shared selector and independent first-maximum certificates. The new
recurrence and certificate theorems supply that connection.

`Examples.BoundedSegments` checks the public interfaces:

| Case | Expected result and public connection |
|---|---|
| `empty`, `zero_capacity` | Empty witness and score zero through the universal nil/zero and score-observation results. |
| `negative_input` | `[-5,-1,-2]` selects empty through `maxSegmentThinScan_of_negative`, with global optimality retained. |
| `binding_capacity` | `[3,4,5]` selects `[4,5]` at bound 2 and the full list at bound 3, using explicit first-maximum certificates. |
| `distinct_tied_witnesses` | The two tied inputs select different witnesses through `maxSegmentThinScan_eq_of_firstMaximum`; the certificates record the independently calculated candidate sequence and score ordering. |
| `first_tie_global`, `reversed_tie_global`, `tied_scores` | The witness consumer proves both global optima; the composed score consumer reports 2 for both. |
| `repeated_all_optima`, `repeated_global_membership` | `mss0 1 [0] = [[],[0],[]]` preserves both empty occurrences; exact scan agreement and the independent membership theorem are exercised. |
| `single_zero_witness` | The single-witness algorithm selects empty, while the all-optima list above retains three occurrences. |
| `binding_prefixes`, `actual_frontier` | Exact bounded-prefix filtering and shared sublist/coverage refinement apply to concrete states. |
| `dropWhile_boundary` | An unordered raw frontier distinguishes source dropWhile from an unconditional filter. |

Statement review covered all retained and changed claim families. Feasibility
is contiguous infix membership, not arbitrary subsequence membership. Bounds
are natural numbers and scores are mathematical integers. Empty candidates
ensure attainment and a nonnegative optimum; zero capacity forces empty.
Strict negativity is required for the general theorem returning an empty witness;
zeros can create additional all-optima occurrences. Thinning trades length
against sum and preserves candidate origin. The last-prefix fallback is unused
on reachable nonempty frontiers. The shared selector's fallback is unused on
the nonempty suffix candidate list. First-maximum certificates distinguish
exact tie choices from score equality. No result assumes the final global
optimum as a premise of its algorithm correctness theorem.

The tie-contract consolidation was reviewed by reducing the dual-order alias:
its strict-before and weak-after inequalities are definitionally the original
integer maximum conditions. The converse still requires a positional
certificate, and certification still requires a nonempty list; arbitrary empty
fallbacks are unchanged. Existing distinct-tie, repeated-zero, zero-capacity
and negative-input examples exercise the unchanged public statements.
`Examples.SelectionTies` also checks the shared predicate at `Nat` and reversed
`Int` scores, including first versus last ties.

## Provenance, remaining scope and validation

The reference is
[`adwh-checkpoint-233`](../history/algorithm-design-haskell/README.md), member
`project/adwh-lean/ADWH/Chapter11/Segments.lean`, SHA-256
`a4133351a867423bca581ed9036d7f0ee8adbb04fcbf813d5d4faa312020c058`.
The bytes were verified before adaptation. The
[declaration ledger](adwh-bounded-segments-provenance.tsv) records all 244 named
source definitions, abbreviations, structures, inductives and theorems:
125 adapted, 13 reused through existing constructions, and 106 deferred.
Anonymous source examples and generated declarations are not separate ledger
rows; compiled project declarations remain covered by the exhaustive audit.

The scope ends at `maxSegmentThinScan_nonnegative`, before subsequences.
The source Down/minWithBy helpers are replaced only in the integer maximum
specialization; arbitrary-comparator helper generality is not claimed.
Subsequences/LUS, difference partitions, cached symmetric-list realizations
and all operation-count models remain separate work. The frontier length
bound counts stored candidate lists; it does not measure copied elements,
allocation, evaluator work or runtime.

Targeted validation passes with `direnv exec . lake build Examples.BoundedSegments`
and a direct `direnv exec . lake env lean Examples/BoundedSegments.lean` check.
All 244 provenance rows, their source hash and retained destinations were validated;
`git diff --check` also passes.
The public entrypoint imports the examples and all four implementation modules.
Fresh full compilation, exhaustive axiom audit and independent reviews belong
to the coordinating integration run.
