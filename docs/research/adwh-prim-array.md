# Matrix construction and array Prim (#186)

`Prim.ArrayOptimality.prim2_minimum` proves the global minimum of the actual
signed link-array executor against every independent `Kruskal.SpanningTree`
competitor. `ArrayObservation.constructed_rep` connects a coherent finite edge
list, its actual two-pass matrix, and its explicitly bidirected graph.
`constructedTreeSquare` executes that construction and array algorithm;
`constructedCostSquare` observes the attained cost while retaining the original
edge problem. `prim_cost_agreement` and `kruskal_cost_agreement` compare this
array realization with the actual accepted ordinary Prim and nested Kruskal
realizations on the same graph.

## Exact source behavior and domain

`Weights` keeps universe-general finite weights, row-major `u*n+v` indexing,
missing cells, and ordered overwrite behavior. The standard `finProdFinEquiv`
has value `v+n*u`; `index_value` checks its equality with the source arithmetic.
`weightsD` writes forward associations. `weightsP` writes every forward
association first, then every reverse association in input order. The exact
lookup observes `edgeValues es u v ++ edgeValues es v u`. It preserves repeated
occurrences; it does not interleave opposite writes or deduplicate input.

The standard `List.getLast?` replaces last-write recursion.
`overwrite_fold` proves the correspondence with the historical overwrite fold
for every initial seed. Membership and empty/constant observations reuse
standard last-element laws. `undirected_two_passes` is an equality of stores.
The source reverse-conflict example remains: `(0,1,3),(1,0,7)` yields opposite
cells 7 and 3. An interleaved alternative would instead leave the reverse cell
at 7. Incoherent input executes; it is not rejected. Coherence is required for
complete symmetric representation, since a single cell cannot retain unequal
weights for the same unordered pair. Directed uniqueness needs only agreement
among the occurrences of that directed pair.

`Array` uses `Option Int` for cached weights and observes it through
`WithTop Int`. `dle_iff` checks infinity as top, including negative finite
weights. `Score` is the standard lexicographic product with natural rank.
`score_le_iff` and `choose_first` connect this order to the source comparison
and the accepted exact first-minimum selector. Rank breaks equal-weight ties
independently of the order of distinct fresh ranks. `better_tie` keeps the old
parent. Updates read the column `wa u v`; they do not add the selected cached
weight. Raw fresh lists retain the source filter behavior, including malformed
lists outside the invariant.

Ranks represent fixed integer labels `rank+1`. The initial root has cached
weight zero and remains in fresh. The wrapper performs exactly `n-1` steps,
leaving one fresh rank. `full_run_minimum` proves the n-step result;
`final_pending_link` proves that the last update changes no link. This transfers
successful extraction and optimality to the actual n-1-step wrapper.
`extractOn` skips the root, requires a finite cached weight for every other
requested rank, and emits parent edges in the requested order. `extractP` uses
all ranks in order. `edgesFor` instead omits infinite entries; the two agree only
under the finite-label premise in `extractOn_eq`.

`MatrixRep` requires exact directed tuple membership, symmetric cells, the
fixed label list, and in-domain graph endpoints. Consequently a one-way edge
list is not itself a representation of a symmetric matrix. `bidirectedGraph`
explicitly concatenates forward label edges and reversed label edges, preserving
order and duplicates. `constructed_rep` proves the required adjacency and
symmetry for coherent inputs. Raw array output need not be a subset of the
original one-way list; it is a spanning tree of this constructed graph.

The invariant reuses `Prim.Correctness.Growing` and `Kruskal.ExchangeInv`.
It partitions fresh/marked ranks, retains the root, records finite marked
labels, and relates each finite cached link to a marked parent. Crossing-edge
availability, minimum cut selection and global exchange reuse the accepted
ordinary Prim proofs. The final competitor comparison uses the shared forest
and spanning-edge contracts. `List.filterMap_congr`, `List.Perm.filterMap` and
`List.Perm.sum_eq` replace inherited list inductions where applicable.

The total `Problem` retains graph, weight function, root, representation and
connectivity. These establish representation and feasibility; none assumes an
optimum. `selectedTree_result` rules out the fallback on that domain. The
conversion to the existing `MinimumSpanningForest.TreeProblem` proves distinct
vertices and nonemptiness from the finite rank list and root. The cost consumers
compose accepted `Optimization.selectionSquare` and `observationSquare`; their
relations retain the input identity. The raw source theorem does not claim a
general success iff connectivity theorem. Disconnected state execution can
succeed while subsequent extraction fails. Construction permits n=0; an actual
root in `Fin n` excludes n=0. Singleton extraction works for every matrix.

## Checked development and statement review

The intended examples were worked out in the issue before implementation.
The initial missing connections were a coherent builder-to-`MatrixRep` proof,
an actual total array realization into the independent minimizer set, and
composition with existing tree/cost observations. Raw computations alone could
not establish those obligations. `ArrayObservation` now supplies those public
connections. Compiler errors encountered while adapting the standard order and
finite index were elaboration failures, not evidence that the intended
mathematical claims were false. No worked expectation was changed to obtain a
successful proof.

`Examples.PrimArray` connects the following cases to the public contracts:

- Row-major indexing, empty construction, missing directed cells, repeated
  writes, the source reverse conflict and its interleaving distinction.
- The printed eight-cell Prim illustration, its parents and cached weights,
  and the public first-minimum certificate. This raw state is not asserted
  reachable from any particular graph.
- The four selected source figure declarations: `primDiagram`,
  `prim_diagram_arrays`, `figureEdges`, `figure_matrix`. The directed Nat matrix
  feeds the already accepted Dijkstra figure shortest-path theorem.
- A signed graph with a loop of weight -100, a useful edge of weight -7,
  coherent duplicate edges, and nonzero root rank 1. The result has rank-ordered
  edges `(2,1,2),(2,3,-7)`, independent global minimum and attained cost -5.
  Its constructed consumer agrees with actual ordinary Prim and nested Kruskal.
- Reversed fresh-list rank ties, retained old parent, an asymmetric column
  update of -8 distinct from both the opposite cell and accumulated distance,
  singleton arbitrary matrices, exhausted fresh lists, zero steps, and
  disconnected execution/extraction boundaries. Exact n-1/n fresh counts and
  equal stores/extractions accompany an application of `final_pending_link`.
- A zero-weight triangle in the prescribed input order. The array selects
  `(1,2,0),(1,3,0)`, while ordinary Prim and nested Kruskal select `(2,3,0)`
  and `(1,3,0)`. `tied_edge_sets_differ` checks actual edge membership, not just
  list order. `tied_all_minimum` and `tied_costs` use the public global and
  consumer theorems for all three realizations.

Statement review covered every declaration through these groups and their
helper derivations: universe/domain parameters for matrix operations; seed and
ordered-list quantifiers for overwrite; top infinity versus Option ordering;
signed weights; exact column direction; rank and parent ties; source numbering;
coherence versus raw execution; directed cells versus undirected graph reach;
n-1 state versus n-step proof; partial edge observation versus total extraction;
all-competitor minimum versus cut minimum; and retained problem identity in
both relational square sides. The nonempty signed and tied examples establish
usable representation/feasibility hypotheses. Equal costs are not claimed to
identify tree witnesses. The independent spanning-tree predicate is reused,
not defined in terms of success or output of the new algorithm.

## Provenance and validation

The immutable source is
[`checkpoint-233.zip`](../history/algorithm-design-haskell/checkpoint-233.zip),
SHA256 `8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`.
The source archive and all nine scoped/reference members were rehashed and
byte-compared against the inspected extraction. The archive is unchanged.

The [declaration ledger](adwh-prim-array-provenance.tsv) contains 192 rows:
117 core names (115 selected and two deferred), four additional selected source
examples, 19 bounded historical helper origins, and 52 local declarations.
Named private helpers are included; generated declarations and anonymous
example statements are not counted. This gives 119 selected algorithm/example
names, not 115. Dispositions distinguish source reconstruction, existing reuse,
standard replacement, local extension and deferral.

| Core member | Selected / total | SHA256 |
| --- | ---: | --- |
| Chapter09/PrimWeights.lean | 30 / 32 | f8b823b0ca92e54e01f75bd841242d90215313900edbd6e82a1ac4f6748bf8ed |
| Chapter09/PrimArray.lean | 58 / 58 | e196d1dea1aab1f55b40043c7d5d0a68da53cb2a31f5c524cdae9d3ec5559543 |
| Chapter09/PrimArrayOptimality.lean | 27 / 27 | 7d0eabba384e9e1dbd0233373d538a53f2237817a63b60fe173329aba89157e7 |

The ledger pins the selected Arrays, CoinChangeSelectors and GraphWorkedExamples
member hashes. Accepted `PrimCore`, `PrimExchange` and `PrimCorrectness`
prerequisites are accounted for in the [ordinary Prim record](adwh-prim.md)
and its declaration ledger. No shared Store, search, exchange, coverage map or
application catalog file is changed. The existing polymorphic
`Dijkstra.Store.valuesAt_map_unique` from #184 is reused unchanged.

Targeted Lean builds passed for `Examples.PrimArray`, `Examples.Prim`,
`Examples.Kruskal`, `Examples.NestedKruskal`, `Examples.Dijkstra` and
`Examples.DijkstraSentinel`. Representative `#print axioms` checks on overwrite,
selection, global minimum, construction, cost agreement and tied witness claims
reported only `propext`, `Classical.choice` and `Quot.sound` (some need fewer).
The elaborated `prim2_minimum` and `prim_cost_agreement` types were inspected.
`SquareApplications` imports the new examples for
the ordinary build and exhaustive proof audit. Independent review and the
fresh full audit are integration gates owned by the coordinating session;
these targeted checks do not claim those gates have passed.

Explicit deferrals remain `PrimWeights.constructionRun` and
`constructionRun_exact`, whose counted initialization/copy and association
executor is outside this semantic slice. Prim array cost modules, finite
sentinels/numeric cached variants, batch/root-sharing optimizers and tours are
also outside this issue. No construction-cost or whole-PrimWeights completion
claim is made.
