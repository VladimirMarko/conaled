# ADWH thinning and optimization reconstruction

Issue [#151](https://github.com/VladimirMarko/conaled/issues/151), part of
[#149](https://github.com/VladimirMarko/conaled/issues/149).

The pilot reconstructs finite candidate pruning and connects its correctness to
conaled's existing optimization transport. Layered networks and 0/1-knapsack use
the same refinement laws. The public entrypoint imports their checked examples.

## Interface and recovered scope

`Optimization.Thinning.Covers R retained original` requires a representative
for each original candidate. `Represents R original retained` additionally
requires every representative to originate in the original list.
`IsThinning R original retained` instead includes the stronger sublist contract.
Membership origin forgets order and multiplicity; sublist retains both.
None of these contracts alone asserts that representatives form an antichain.

Operations take ordinary functions and lists. Reflexivity and transitivity are
arguments to the proofs that need them, not fields required to construct an
algorithm. `represents_map` changes both the carrier and dominance relation;
`represents_flatMap` permits several extensions per candidate and a distinct
representative for each extension. `pruneFold_refinement` shares iteration across
candidate-first knapsack and edge-first network enumeration. The ordered
`pruneFold_thinning` also preserves the network's stronger source-order contract.

`minimizer_of_represents` calls `Optimization.minimizer_transport` with identity
candidate/cost interpretation. Candidate origin discharges admissibility,
dominance and cost compatibility supply dominating lifts, and objective
agreement is reflexive. Its cost type needs only a preorder. The executable
`argmin` needs a linear order to choose a minimum and retains the first minimum.
`argmin_first` checks that tie rule for every tail whose costs are no lower.
Failure remains `none`, characterized by an empty candidate list.

The source adjacent `bump`/`thinBy` guard priority is preserved. The network
reconstruction preserves edge-first enumeration, arbitrary integer weights,
source-sensitive dominance, absent source for the empty path, and the selected
path on ties. Its independent specification chooses one edge from each layer
and checks adjacent endpoints. The public correctness and failure results now
use the shared fold theorem and optimization transport.

Knapsack retains the source item, selection, summary, and independent feasible
sublist specification. It reconstructs a finite frontier with weight/value
Pareto dominance: a representative weighs no more and is worth no less.
`mem_candidates_iff` proves soundness and completeness against feasible input
sublists before using pruning. `solve_optimal` proves the global maximum via
`OrderDual Nat` and the common minimum transport. Empty input always has the
empty selection. Duplicate labels and zero weights are permitted; names alone
never witness item identity.

The knapsack frontier is a new algorithm. It does **not** claim exact equality
with checkpoint 233's `swag`, `table`, or `swag0` enumeration or tie choices.
Its candidate-first enumeration places skip before take for each suffix,
whereas the source capacity recursion groups all skip alternatives first.
The checked zero-value, zero-weight tie retains skip, but this is not a theorem
of global source tie equivalence. Reconstructing the source table, its exact
agreement with recursive `swag`, all-optima output, and complexity proofs remains
outside this slice. Network algorithms are recovered exactly; knapsack's
independent optimization contract is recovered with a different realization.

Other excluded source algorithms are forward thinning, one-drop thinning,
global antichain insertion, sorted merge, coin-change optimization, generic
filter/fold fusion, and the full Chapter 10/13 resource models. Reversal checks
the weaker order-changing refinement interface without claiming to reconstruct
the source coin merge implementation.

## Composition and caller effort

The ordinary interface has no categorical wrappers. Optional `candidateRep`,
`foldSquare`, and `mapSquare` adapters use existing `Relational.RelSquare` and
`Relational.compose`. `Examples.Thinning.knapsackValues` composes the actual
knapsack fold with objective observation. Its preservation theorem says every
feasible value is dominated by a retained value and every retained value comes
from the unpruned list. `observed_sample` connects that composition to the
independently computed optimum 9.

Deleting the generic fold and transport layer would restore the same induction,
origin, and dominance-to-optimum proof to both clients. The network needs
source-aware extension preservation, and knapsack needs weight/value extension
preservation; these domain obligations remain explicit. There is no new IR,
proof syntax, or assumption of whole-solver correctness.

## Checked cases and statement review

The initial gap was a missing connection: source network proofs and the local
optimization transport existed separately, while knapsack had no local
frontier-to-feasible-sublist connection. The retained numerical expectations
came from the source examples and direct finite calculations. They were not
changed to fit a proof.

| Claims reviewed | Checked use and interpretation |
|---|---|
| Coverage, origin, composition and mapping | Reversal preserves membership/coverage but fails sublist order; `origin_required` exhibits coverage by the absent cheaper candidate 0. This rules out silently using coverage as admissibility. |
| Adjacent pruning and ordered fold | Network uses the actual source `thinBy`; `adjacent_tie` retains label 10 when both labels cost 4. No idempotence, shortest-list or antichain theorem is claimed. |
| Fold refinement and extension laws | The generator is independent of pruning. Network extensions preserve source and add the same integer weight; knapsack extensions preserve weight/value dominance and capacity. Their hypotheses hold on all inputs, not just the examples. |
| Minimum transport and selector | Origin, candidate-restricted cost compatibility, and coverage have separate roles. The theorem concludes feasibility and comparison with **every** original candidate. `reverse_minimum` uses an order-changing representation; `selector_tie` connects to `argmin_first`. |
| Network semantics and failure | `disconnected_network` uses the public failure theorem for incompatible endpoints. `network_optimum` uses the public optimum theorem for a network whose cheapest suffix cannot connect. Negative weights are allowed because layers bound path length. Source empty-layer, empty-network, first-tie and duplicate-edge examples remain checked. |
| Knapsack feasible semantics | Every result is a summary of an actual input sublist, including cached value and weight. The empty selection is optimal on empty input at every capacity. Capacity 5 with items `(value, weight) = (6,4), (4,3), (5,2)` selects labels `[2,3]`, value 9, weight 5. `sample_optimal` uses `solve_optimal`. |
| Knapsack maximization and ties | `objective` is `OrderDual Nat`, so least objective means greatest value. The zero-value zero-weight item ties with skip and returns empty; the result's optimality uses the universal theorem. No universal source-table tie correspondence is inferred. |
| Relational adapters | Input equality preserves the problem instance. The intermediate relation is candidate origin plus dominance, not equality of candidate lists. `knapsack_values_refinement` consumes preservation of the composed square; `observed_sample` combines it with the global optimum bound. |

Review covered quantifier domains and implicit carriers, dominance direction,
order reversal, membership versus sublist, seed behavior, failure, independent
feasibility and satisfiable extension assumptions. Helper claims are exercised
by these applications. The checked proofs establish the stated contracts;
examples and this statement review assess their intended meaning.

## Immutable provenance

The reference is snapshot `adwh-checkpoint-233` in
[`docs/history/algorithm-design-haskell/`](../history/algorithm-design-haskell/README.md).
The archive is unchanged. Member hashes come from
[`checkpoint-233.files.sha256`](../history/algorithm-design-haskell/checkpoint-233.files.sha256).
The [declaration record](adwh-thinning-provenance.tsv) gives the snapshot,
archive member, member SHA-256, source declaration, and disposition for each
named declaration in this slice. Newly constructed declarations identify the
source obligation they reconstruct or state that they are local additions.
Generated structure projections and decidable instances belong to the recorded
parent declaration and are covered by the exhaustive proof audit.

The separate assessment of `CoinThinning.frontier_refinement`,
`GeneralScheme.thinned_refinement`, and `MergedFold.Represents` motivates keeping
membership refinement distinct from source-order thinning. Their full
algorithms are not imported. Later snapshots can be compared by member and
source declaration without changing the historical reference.

## Validation at implementation handoff

`direnv exec . lake build Examples.Thinning` passed, including all new modules.
Elaborated public types were inspected for carrier generality, dominance
orientation, independent feasibility and reversed cost order. The fresh
`direnv exec . ./check.sh --jobs 2` run was still in progress when this candidate
was handed to independent review; full-build and exhaustive-audit acceptance
remain pending the coordinator's recorded result. No project source changed
after that check started.
