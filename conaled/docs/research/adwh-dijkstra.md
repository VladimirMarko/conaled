# Finite Dijkstra, exact paths and queue agreement (#180)

`Dijkstra.Observation.queue_distance_eq` proves that the literal link-array
Dijkstra loop and the accepted closed search with a zero heuristic return the
same optional distance for every destination. The array loop performs exactly
n−1 steps. The queue run uses the existing exact leftist queue through its keyed
interface and the existing sufficient `closedBudget`; completion is proved,
not assumed. Equal-cost path witnesses may differ.

The domain is a directed matrix `Fin n → Fin n → Option Nat` with a root in
`Fin n`. Missing edges and infinite distances use `none`. Nonnegative costs
include zero, and loops are allowed. The root implies a nonempty carrier.
The global correctness theorem needs no reachability premise. Negative costs,
finite-sentinel arithmetic, overflow and raw numeric indices are outside this
slice.

## Independent semantics and consumers

`Semantics.adjacency` filters the finite vertex list for present edges.
`mem_adjacency` proves exact matrix/edge membership. `walk_iff` connects the
source snoc presentation to accepted `Search.Heuristic.Walk`, whose competitors
may repeat vertices and edges. `path_iff_route` additionally connects the
forward vertex sequence and cost to accepted `Route` and `extract`. Thus a
shortest-distance proof does not stand in for a proof about the emitted list.
The implementation-specific parent-chain invariant proves that the returned
finite path is simple and fits within n cells of reconstruction fuel.

`Observation.result` is a total interface to the source Option executor;
`final_exact` and `result_exact` exclude its defaults on every valid input.
`witnessSquare` retains the original matrix, root and target on both sides.
Its permitted finite outputs carry the exact accepted route and the independent
shortest-distance claim. Its infinite branch instead requires `[target]` and
independent absence of a path. `distanceSquare` composes the accepted
`Optimization.observationSquare` to discard the witness.

`allResults_exact` relates the whole list consumer to source `extractPaths`.
`allWitnessSquare` uses `List.Forall₂` over `List.finRange n`; its composed
`allDistanceSquare` preserves this order. `allDistanceSquare_correct` gives the
complete independent distance vector, and `allDistanceSquare_exact` equates it
to the actual queue distances at those same indices.

`Target.dijkstraZ_total` strengthens the retained reachable-target theorem:
every requested target returns either a simple shortest path or the successful
unreachable value `([target], none)`. `untilTarget_infinitySelf` supplies the
missing parent invariant through the exact first-hit loop. The target loop
still checks removal from `fresh` before testing its fuel. In particular,
root=target requires one successful removal, and an unreachable target is
removed normally rather than causing an outer failure. `target_distance_eq`
connects this early-stop result to the n−1-step all-target executor.

## Exact behavior and shared constructions

`Core.score_le_iff` identifies standard lexicographic order on
`WithTop Nat ×ₗ Nat` with the entire historical score comparison. It transports
both directions, using injectivity of the infinity observation. The source
selector's `FirstMinimum` contract and the accepted `choose_first` iff both
identify the first minimizing occurrence. This preserves source selection even
on reordered or repeated fresh lists; equal distances choose the smallest
vertex rank. `better_tie` retains the old parent, independently of that rank
choice. There is no copied score-order axiom hierarchy or coin-selection proof.

The eight selected array declarations use standard `Vector` get/set operations.
`accum_lookup` observes the literal left fold as a fold over all values at one
index, preserving repeated updates and noncommutative combining. Existing
`DynamicProgramming.arrayAssign` provides replacement on distinct indices,
so it does not justify identifying these two operations. No unrelated array
construction or execution-cost closure was imported.

The last fresh vertex has its own `completed_bound` proof. Replacing n−1 by n
would give the same final labels on the figure but a different fresh list.
`run 0` returns its input; requesting a further step after exhaustion fails.
Raw malformed states keep those operational behaviors. `getPathFuel` stops at
a self-parent, follows parent links backwards otherwise, and fails at zero
fuel. Nontrivial parent cycles can fail. `InfinitySelf` ensures that generated
unreachable vertices have successful singleton reconstruction.

`List.Forall₂`, `List.mapM_pure`, `forall₂_map_right_iff`, `forall₂_same` and
`List.head?_filter` replace historical list helpers and private inductions.
`Iteration.UntilSpec` supplies the existing first-hit trace.
`Search.Heuristic.DistanceResult.unique` is the only change to existing search
code. Its proof compares the two global minima or contradicts the no-goal
branch; it does not require decidable vertex equality. The existing search
executor, queue implementation, termination proof and correctness proof are
reused unchanged.

## Checked cases and statement review

The retained Figure 9.2–9.4 declarations compute every source snapshot, final
distances `[0,7,9,12,11,10]`, the one remaining fresh vertex, and the path
`[0,1,2,5,4,3]` of cost12. Their ordinary source correctness specializations
remain checked. `figure_accepted_route`, `figure_accepted_shortest`,
`figure_vector_contract` and `figure_queue_vector` connect those calculations
to the public bridges and composed observations.

The further applications check singleton/root=target first-hit behavior,
disconnected output placeholders, zero-weight cycles, rank selection despite
reversed fresh order, old-parent retention on equal routes, insufficient path
fuel, an empty fresh list, cyclic parents and n−1/n/exhausted-step boundaries.
`tied_queue_agreement` and `disconnected_queue_agreement` instantiate the actual
queue equality in both finite and infinite branches. Repeated noncommutative
store updates exercise the selected array observation rather than a distinct
replacement operation.

The initial source examples already established their numerical expectations.
The development obligations were their connection to accepted walk and ordered
route semantics, the missing total target no-path branch, and the comparison
with an actual completed queue run. These obligations are discharged by the
public theorems above. No deliberately broken numerical example was used as
an EDD substitute.

Statement review covered every retained source claim and new observation:

- Core order/addition and selector claims distinguish infinity from Option's
  bottom order, transport the full rank comparison, and keep raw-state domains.
  The standard score order's elaborated type and the two directions of its
  source bridge were inspected.
- Frontier, settled and final-vertex claims quantify over every source walk,
  not just generated paths. The iff to the accepted relation transfers that
  quantification. The nonnegative hypothesis is encoded by `Nat` edge costs.
- Chain and path claims distinguish backwards parent lists from forward output,
  include the endpoint and exact accumulated cost, and establish simplicity
  only on invariant states. Raw cycles remain outside these hypotheses.
- Whole-list and target claims distinguish outer failure from an infinite
  successful label. Their no-path branches do not assert that the singleton
  is a route from the root. Index order is retained through `Forall₂` and map.
- Queue completion follows finite closure and degree at most n. Queue agreement
  compares optional distances rather than requiring identical tie witnesses.
  Every input matrix/root/target is retained by the relational consumers.
- Helper claims concern only the selected operations. The repeated-update case
  verifies the stronger combining-store meaning. Examples of both reachable
  and unreachable targets establish satisfiable uses of the global contracts.

Targeted checks passed with `direnv exec . lake build Examples.Dijkstra
Examples.HeuristicSearch Examples.SelectionTies Examples.CoinChoice`.
Elaborated statements were inspected for the score, walk/route, queue/vector,
total-target and shared uniqueness contracts. Representative `#print axioms`
checks are limited to `propext`, `Classical.choice` and `Quot.sound`.
Independent reviews and the exhaustive fresh audit belong to the integration
gate; these targeted checks do not claim that gate has already run.

## Provenance and remaining boundaries

The immutable snapshot is
[`adwh-checkpoint-233`](../history/algorithm-design-haskell/README.md).
Its ZIP SHA256 is
`8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`.
All ten selected source member hashes were checked against the preserved
manifest and their extracted bytes before this handoff.

[The declaration ledger](adwh-dijkstra-provenance.tsv) records 212 rows:
102 names across the five whole Dijkstra modules, 29 selected helper/example
names, and 81 new local or shared declarations. Private declarations are
included; anonymous instances and generated declarations are excluded. The
removed private mapM/filter helper names have explicit replacement rows.
The source score's anonymous custom order instances are replaced by standard
instances with the exact `score_le_iff` bridge. These counts do not claim the
whole Arrays, CoinChangeSelectors, InversionCount, Iteration or
GraphWorkedExamples modules.

The original #180 candidate `e0d76c8` deferred `DijkstraSentinel`. The separate
[#184 reconstruction](adwh-dijkstra-sentinel.md) now supplies that raw executor
and its correspondence under all-vertex reachability, bounded edges and
`n * bound < sentinel`. Its source sum guards the edge sentinel but not an
infinite accumulated label. #184 also moves the existing private association
lemma to public `Dijkstra.Store.valuesAt_map_unique`, shared by the genuine and
raw executors; the ledger records its current destination and historical pin.
NumericCached, roots/saved roots, execution costs, broader jogger clients,
shortest-path structure modules, and Prim's ordinary/array closures remain
separate work.
