# Growing-tree Prim and shared optimum observations (#183)

`Prim.Correctness.prim_minimum` proves that every successful valid Prim run is
minimum against every independent `Kruskal.SpanningTree` competitor. Validity
requires distinct listed vertices and in-domain endpoints. Labels and weights
are arbitrary integers, including negative weights; loops and repeated or
parallel edge occurrences are allowed. A nonempty valid graph succeeds exactly
when connected. The raw vertex order is retained and related to the input by
permutation. Explicit normalization changes only the vertex list before using
the accepted spanning-tree predicate.

`Prim.Observation.kruskal_cost_agreement` compares the actual total Prim and
nested Kruskal realizations on the existing
`MinimumSpanningForest.TreeProblem`. Both attain the same signed optimum.
`forest_cost_agreement` composes this with the accepted tree/forest cost theorem.
These equalities concern cost, not equality or permutation of output witnesses.

## Source state and first-hit meaning

`Core.StateP` holds the growing tree and ordered pending edges. `Safe` means
exactly one endpoint is visited. `addP` prepends the new vertex and accepted
edge, so the raw result retains reverse discovery order. `gstepP` selects the
first currently safe occurrence. It keeps every earlier unsafe edge in order:
an edge with two unvisited endpoints can become safe after another step.
`FirstSafe` specifies the exact prefix/selected occurrence/suffix and the
residual `pre ++ post`; `gstepP_firstSafe` is an iff without a validity premise.
`applyP_source_iff` relates the actual multi-step executor to that source trace.

Stable sorting reuses `Kruskal.sortEdges`. `gstepP_least` combines ordered
first-safe selection with sortedness, while `step_edge_permutation` retains
the exact chosen-plus-pending multiset. Duplicate occurrences are not silently
collapsed. The existing `ForestKruskalSource.Occurrences.picks` supplies branch
enumeration and its exact ordered output. `untilBranches_eq_branch` and
`spatsP_fixed` preserve source branch order and multiplicity; no theorem here
claims that `spatsP` enumerates every spanning tree.

`untilP_eq_apply` proves guarded/fixed agreement at the state level for enough
fuel and an initial visited size at most the target. `prim_eq_prim1` retains
the source wrapper equality. The added `untilP_first_hit` and
`primState_first_hit` use accepted `Iteration.UntilSpec`. Its total transition
uses a fallback only to type the trace; each actual transition in a successful
trace comes from a successful `gstepP` predecessor. The guard is checked before
fuel: an already complete state succeeds even at zero fuel. A mismatching
zero-fuel state fails. Overlarge raw visited states are not silently repaired.

Empty graphs return outer `none` from both `prim` and `spatsP`. A singleton
returns its zero-edge tree. For a valid disconnected nonempty graph, `prim`
fails; the branch-list wrapper may successfully return an empty list, as the
checked disconnected example does. These Option/list boundaries are distinct.

## Shared proof and consumers

The operation, growing-state representation and global optimum layers remain
separate. `Growing` requires a nonempty distinct visited list inside the input,
acyclic chosen edges on the whole carrier, endpoints inside the visited list,
and connectedness among those vertices. `Invariant` adds the exact multiset
complement and sorted pending list. Availability follows by finding a crossing
edge from a visited vertex to an unvisited vertex in the connected input.

The new cut reasoning is `reach_same_side`, `reach_crossing`,
`visited_cut_exchange` and `exchangeInv_cut_step`. An arbitrary independent
competitor contains a path across the actual visited cut. Exchanging one of
that path's crossing edges preserves every already chosen edge, since chosen
edges have both endpoints inside the visited set. The accepted exchange
invariant then compares the resulting signed cost with every competitor.

Fourteen historical exchange helper declarations are replaced by existing
Kruskal/Connected interfaces. In particular, path existence, repeated-edge
removal, edge membership, forest restriction, reachability replacement and cost
identity are reused. Existing `Kruskal.walk_restrict` and
`tree_path_edge_cut` are now public with their proofs and statements unchanged.
The source correctness module's repeated reach-edge wrapper and permutation-sum
proof are also removed; mapped weight permutations use `List.Perm.sum_eq`.
There is no second graph semantics, connectivity relation, forest theory,
occurrence generator or sorting implementation.

`selectedRawTree_result` excludes the total interface's default for every
`TreeProblem`. `selectedRawTree_minimum` retains the source vertex permutation
and normalized independent optimum. `treeSquare` uses accepted
`Optimization.selectionSquare`; `costSquare` composes
`Optimization.observationSquare costMCST`, retaining the original problem on
both sides. `costResult_exact` relates this composed value to the actual
Option executor. Existing global minimum uniqueness proves agreement with
nested Kruskal. Different tied witness lists are allowed.

## Checked applications and statement review

`Examples.Prim` consumes the source `kept_edge_becomes_safe` theorem and connects
both steps to the public `FirstSafe`/`SourceRun` contracts. The signed graph has
noncontiguous labels `[10,-4,90]`, a weight −100 loop, a weight −7 edge and duplicate
weight 2 edges. The selected cost is −5. Its raw vertex order is `[90,-4,10]`;
normalization restores the input order while preserving selected edge order.
The exact residual retains the skipped loop, one duplicate edge and the unused
weight 9 edge. `signed_minimum`, `signed_optimum`, `signed_first_hit`, and the
Kruskal/forest agreement examples use the universal public results.

An all-zero triangle checks stable first crossing selection. Prim and nested
Kruskal produce different edge-list order but the same optimum. This example
does not claim different selected edge sets. `duplicate_branches` checks that
two equal occurrences yield two equal outputs, and `branch_fixed` applies the
source fixed-branch theorem. Empty, singleton, disconnected, exhausted,
zero-fuel and one-extra-step cases retain the original behavior.

The source kept-edge diagnostic fixed the first operational expectation. The
new obligations were its exact trace interpretation, arbitrary-label signed
optimality, first stopping state, and composed comparison with an actual
accepted tree realization. Calculations establish those cases; public theorem
specializations provide their semantic connections. No artificial failing
numerical proposition was used as EDD evidence.

Statement review covered all source declarations and new claims:

- Safety has exactly one visited endpoint, so loops never cross a cut. The raw
  operation and occurrence theorems have no hidden graph-validity premise.
  Residual equality retains unsafe prefixes rather than discarding them.
- Growing and invariant claims are about the actual current tree and residual
  list. Their hypotheses do not assume optimality or successful completion.
  The progress theorem needs connectedness and a strict size gap.
- Exchange quantifies over every independent spanning tree. Signed weights
  require only the least-crossing inequality; no positivity or distinct-weight
  assumption enters the proof. Forest/path helper exposure preserves the
  previously accepted statements exactly.
- Source minimum retains vertex permutation. Normalized optimum replaces only
  vertices; edge order and costs are unchanged. Total existence needs nonempty
  connected valid input, whereas correctness of successful runs does not add
  that connectivity assumption.
- First-hit traces distinguish successful stop, failed edge search and fuel
  exhaustion. Branch-list success with no outputs is not an outer failure.
  The branch contracts establish operation/size facts, not enumeration
  completeness.
- Consumers keep `TreeProblem` identity and actual executor results. Their
  comparison is attained cost equality, not equal tied witnesses. Signed,
  disconnected and singleton cases give concrete satisfiable uses and expose
  the different domain boundaries.

Targeted checks passed with `direnv exec . lake build Examples.Prim
Examples.Kruskal Examples.NestedKruskal Examples.SelectionTies`. Elaborated
source-step, cut-exchange, first-hit, successful optimum, success/connectivity,
total realization and cost-agreement statements were inspected. Representative
axiom checks contain only `propext`, `Classical.choice` and `Quot.sound`.
Independent reviews and the fresh exhaustive build/audit remain integration
gates; the targeted build does not claim those gates have run.

## Provenance and boundaries

The immutable
[`adwh-checkpoint-233`](../history/algorithm-design-haskell/README.md) ZIP has
SHA256 `8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`.
The ZIP and all six selected member hashes were checked against the preserved
manifest and byte-compared with the inspected extraction.

[The declaration ledger](adwh-prim-provenance.tsv) records all 94 explicit names
from the three whole source modules: 50 Core, 18 Exchange and 26 Correctness.
It contains 147 rows total: 94 whole-module dispositions, three selected helper
rows, two existing Kruskal interface exposures and 48 new declarations/examples.
Private names are included; anonymous instances, generated names and anonymous
examples are excluded. Replaced helper names have explicit destinations.

PrimWeights, PrimArray/PrimArrayOptimality, finite sentinels, numeric cached
implementations and execution costs remain deferred. Broader enumeration
completeness, tours and GraphWorkedExamples' array-only diagrams are not claimed
by this ordinary growing-tree closure.
