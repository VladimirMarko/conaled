# Nested forests and global minimum spanning forests (#172)

`MinimumSpanningForest.mcsf_correct` proves that the corrected all-edge scan
completes on every graph with distinct listed vertices and endpoints in that
carrier. Its selected edges are globally minimum among all independent spanning
forests. Empty graphs, disconnected components and isolated vertices are part
of this domain. Labels are arbitrary integers; weights may be signed, and input
edges may include loops, parallel edges and repeated occurrences.

`ForestKruskalClient.kruskal1_result_minimum` and
`kruskal0_result_minimum` prove global spanning-tree optimality for the source
nested-forest wrappers. Both wrappers succeed exactly on connected graphs within
the nonempty valid domain. The raw returned vertex list is permutation-equal to
the input list. The optimum theorem explicitly normalizes that list to the input
order, as required by the accepted `Kruskal.SpanningTree` predicate.

## Independent meanings and representation

This work reuses #169's `Kruskal.Graph`, `Reach`, `EdgeForest`, `StateRep` and
spanning-tree meanings. A `MinimumSpanningForest.SpanningForest g fs` is an
acyclic selected edge list contained in the original edges, inducing exactly
the same reachability as those edges. `Minimum` compares its signed sum against
every such forest. Neither feasible candidates nor competitors are defined by
running the implementation or enumerating its possible results. A negative
loop is inadmissible despite lowering the sum; repeated input occurrences do
not permit selecting a cyclic or repeated edge list.

`ForestPartition.project` observes the first vertex and full vertex list of each
nested component. `chosen` flattens component edge lists. The representation is
accepted `Kruskal.StateRep` applied to those observations. Component lookup and
merge commute with accepted first-name list partition operations. Component
uniqueness follows from Mathlib's `List.nodup_flatten` and pairwise disjointness;
lookup reuses the existing `ListPartition.lookupDS_of_member`, now public with
its proof unchanged. Singleton flattening, mapped sums and cost permutation use
standard list lemmas.

The scan proof maintains an exchange-extension invariant over independent
spanning forests. Its exchange step uses accepted `Kruskal.forest_exchange`,
`exchange_cost_identity` and `same_components_subforest_eq_perm`. Reachability,
forest acyclicity, singleton state representation and merge representation
reuse #169; partition invariants and union laws reuse #158. There is no second
connectivity, cut/exchange or sorting theory. Stable weight sorting calls the
existing `Kruskal.sortEdges`.

## Exact source behavior

`Applications/Kruskal/Nested.lean` retains first-match lookup, prepending the
merged component, vertex concatenation, new-edge-first component edge order,
source iteration counts, and exact residual suffixes. Raw operations remain
defined on malformed states. `gstep_source_iff` relates execution to the
independent take/skip relation without a validity hypothesis. Missing endpoints
fail; internal edges are skipped recursively until a crossing edge or exhaustion.
`add` retains its source behavior even when both lookups return the same tree.

`gstep_projection` preserves the component/residual observation exactly.
`gstep_selected_projection` additionally exhibits the actual flat step result
and a permutation of selected edges. Nested edge concatenation need not equal
the flat implementation's reverse acceptance order. `kruskal1_forest_result`
proves that a successful tree wrapper equals the entire singleton corrected
forest before vertex normalization. First-hit behavior uses the accepted
`Iteration.UntilSpec`; the fallback transition in that trace does not hide a
failed step, since the proof produces every successful predecessor step.

The printed `mcsfLiteral` remains separate. Its null test sits outside `gstep`,
which may exhaust an internal suffix and fail. The source triangle therefore
returns `none` from that wrapper after its tree is complete. Corrected `scan`
consumes each internal edge successfully and returns the completed forest.
Both forest wrappers return `some []` for an empty input; both tree wrappers
return `none`. A singleton tree wrapper takes zero steps and can ignore malformed
unused edges. No optimum theorem is claimed for those unsupported inputs.

The bounded occurrence helper retains `picks`, its prefix/suffix decomposition,
and its projected order. `stepsDiscard_same_forests` is equality of the mapped
forest lists; `stepsDiscard_residual_subset` only relates the residual lists by
sublist. The exact full-state counterexample is retained. It refutes equality
at the full-state observation, not forest optimality.

The diagnostic's all-minima operation is ordered filtering by every candidate's
cost. `AllMinima.minsWith_eq_filter` proves exact equality with the source
three-guard scored fold, including empty inputs, ties and repeated occurrences.
Its existence and first-tie arguments use accepted `Optimization.Thinning.argmin`
and `Optimization.argmin_firstMinimum`. `minima_eq_source` connects the actual
diagnostic to that equality; `minima_mem_iff` connects membership to independent
`Optimization.minimizers`. This helper stays in the Kruskal application; no coin
change or permutation enumeration theory is imported.

## Consumers and connected examples

`ForestObservation.lean` supplies the actual corrected-forest selector on valid
graphs and its edge-list selection square. Its default result is proved
unreachable. The cost consumer composes `Optimization.observationSquare`, keeping
the graph index and the image of permitted outputs. Its cost is attained and
equals every independent optimum cost.

The connected-tree consumer retains the raw tree separately and explicitly
normalizes its vertex list. `selected_tree_forest` equates the raw tree's singleton
forest with the corrected scan. `tree_forest_cost` connects their cost consumers;
`numbered_cost_agreement` connects the nested tree implementation to #169's flat
implementation on their shared domain, without equating tied witnesses.

The checked applications in `Examples/NestedKruskal.lean` were developed with
these intended distinctions:

- The original state counterexample, discarded residuals, selector ties, printed
  triangle failure, empty graph, arbitrary singleton and isolated vertices.
  The boundary computations feed the public global optimum theorems where their
  hypotheses hold.
- A graph with labels `[99,42,7,-3]`, a negative loop, repeated negative parallel
  edges and a zero-weight connection. The intended optimum costs -2, excludes
  the loop and keeps isolated vertex 99. `signed_minimum`, `signed_consumer` and
  `signed_square_preservation` establish that result through the universal
  theorem and composed square, not merely by evaluation.
- Removing vertex 99 gives input order `[42,7,-3]` and raw output order
  `[-3,7,42]`. `normalized_optimum` proves their inequality and permutation and
  applies the normalized global tree theorem. `signed_first_hit` uses the public
  first-hit result; connected tree/forest consumers preserve the same raw tree.
- Equal-weight edges yield nested order `[(1,3,1),(1,2,1),(3,4,1)]` and leave the
  exact residual `[(2,4,1)]`. The accepted flat algorithm conses accepted edges,
  so its order differs. `tied_distinct_orders` checks both executions, and
  `tied_equal_costs` applies the shared cost agreement at value 3.
- Malformed unused endpoints and duplicate listed vertices expose the domain
  boundary. The corrected scan's successful internal-edge no-op differs from
  the source step's exhausted-suffix failure.
- The selected textbook path graph and triangle connect exact nested execution
  to their global minimum-tree theorems. Shortest-path and divide-and-conquer
  claims from the example source are outside this selection.

No fabricated failing Lean test is claimed. Initial obligations were the absent
public connections from these calculated outputs to global minima, exact source
fold behavior and composed consumers. The completed cases use those public
results. Routine elaboration failures during adaptation were not treated as
mathematical counterexamples.

## Statement review and verification

The statement review checked all source dispositions and local additions against
the cases above. In particular, forest competitors preserve each original
connected component, the empty forest is feasible on the empty graph, and tree
nonemptiness is retained. Input edges need not be nodup or positive. Vertex
normalization is visible in the conclusion; raw component and residual order
are unchanged. `kruskal_variants` retains its weaker distinct/nonempty-vertex
premises without requiring endpoint validity. Source-step correspondence has
no validity premise. Global optimum statements compare every independent
competitor and do not assume an optimum or an exchange invariant at the public
entrypoint. Selection fallbacks and valid domains have checked inhabitants.

Targeted checks cover `Examples.NestedKruskal`, `Examples.Kruskal`,
`Examples.Connectivity` and `Examples.StableSorting`. Representative axiom checks
for corrected global optimality, normalized tree optimality, first-hit iteration,
step projection, exact all-minima filtering and numbered cost agreement report
only `propext`, `Classical.choice` and `Quot.sound`. Full fresh integration,
exhaustive audit and independent reviews belong to the orchestration gate.

## Provenance and limits

The preserved archive is
[`checkpoint-233.zip`](../history/algorithm-design-haskell/checkpoint-233.zip),
SHA256 `8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`.
Inspected extracted members were compared byte-for-byte with the ZIP and their
hashes checked against its manifest. The
[declaration ledger](adwh-forest-kruskal-provenance.tsv) records all 123 named
source declarations in `ForestKruskalSource`, `ForestPartition`,
`MinimumSpanningForest` and `ForestKruskalClient`, selected occurrence/selector/
iteration helpers and eight selected textbook example declarations. It also
records every new explicit local declaration, including private proof helpers.

The four core modules are complete for this issue's semantic closure. Remaining
forest enumeration, greedy-condition/search developments, `ForestKruskalCosts`,
`ForestUntilCosts`, disjoint-set execution counts, array variants and Prim/
Dijkstra algorithms remain deferred. The signed edge-weight objective is not a
runtime or operation-count bound. Labels are arbitrary integers as in the source;
no polymorphic-label generalization is claimed.
