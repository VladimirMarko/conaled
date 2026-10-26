# Disjoint-set Kruskal reconstruction (#169)

`Kruskal.kruskal_minimum` proves that every successful execution on a
`NumberedGraph` returns a globally minimum spanning tree. It compares the signed
sum of selected weights against every independent spanning-tree competitor.
`kruskal_defined_iff_connected` characterizes success on that domain. Exact source
execution and malformed-input behavior have separate, unconditional contracts.

## Independent graph model and source adapter

Vertices are integers, as in the source. `Reach` uses the already accepted
`Connectivity.ListPartition.Connected` presentation. `reach_partition_iff`
identifies it with the finite-carrier Mathlib equivalence closure in
`Connectivity.partition`; `reach_observe_iff` connects it to the public optional
connectivity query. Invalid vertices do not become connected to themselves.

`EdgeForest` requires a nodup vertex list, endpoints in that list, nodup chosen
edges, and disconnection of each chosen edge's endpoints after its removal.
`SpanningEdges` additionally requires a nonempty carrier and connectivity.
`SpanningTree` preserves the original vertex-list order and chooses edges from
the input. Input edges may contain loops, identical occurrences, reversed or
parallel edges, tied weights and negative weights. A feasible forest cannot
choose a loop or a cycle, even when its weight is negative. The nonempty spanning
convention excludes an empty graph from having a spanning tree.

The source executor initializes blocks named 1 through n. `NumberedGraph` makes
its supported domain explicit: a nonempty vertex list permuting exactly 1..n,
with every input endpoint in that list. Vertex order may be arbitrary within
this permutation. Abstract connectivity on labels 10 and 20 does not validate
this adapter. A singleton takes zero steps and therefore does not inspect unused
edges; its raw result can exist even when `NumberedGraph` fails.

`sortEdges` calls accepted `Applications.Sorting.sortOn`. The source's
`StableWeightSort` observation is equivalent to accepted `StableSort` by
`stableWeightSort_iff`; correctness and uniqueness use `sortOn_spec` and
`StableSort.unique`. This preserves input order among equal-weight edges without
repeating the sorting proof. `SourceStep`, `SourceRun` and `SourceResult` describe
the exact first-match lookup, first-name union, recursive skip, successful-step
count, consed selection and residual list behavior. `kruskal_source_iff` holds
without a numbered or well-formed-state premise.

## Proof structure and reuse

`Basic.lean` contains the independent predicates, source operations and their
state observations. `Correctness.lean` retains the ordinary walk, cut, invariant,
cardinality and greedy-exchange mathematics. `Observation.lean` connects the
proved algorithm to shared optimization and observation facilities.

The source walk/cut proofs construct a removable edge on a path across the cut
induced by the already chosen forest. The removal preserves that forest and the
ambient connectivity. `forest_exchange` is the common proof for disconnected
forests; `cut_exchange` specializes it to spanning trees.
`same_components_subforest_eq_perm` likewise supplies the spanning-subforest
maximality specialization. This shares the stronger forest proofs instead of
retaining two copies of each argument.

`exchange_cost_identity` uses signed integer addition and subtraction, so the
greedy argument needs no positivity assumption. `KInvariant` tracks the valid
partition, the independent selected forest, consumed prefix, reversed acceptance
order and internality of skipped edges. `invariant_crossing_weight` proves that
the chosen edge is no heavier than every crossing input edge, including an edge
in an arbitrary competing spanning tree. `ExchangeInv` then supplies a
no-more-expensive competing tree extending the entire chosen forest. At
completion, spanning-subforest maximality identifies its edges up to permutation
with the returned tree. This proves the global optimum over all competitors.

The source's `perm_sum_int`, `head_member`, `sameBlock_symm` and `reach_nil_iff`
helpers now delegate to Mathlib or accepted ListPartition facts. Following review
I169-1, `reach_mono` also specializes the accepted `connected_mono` theorem to
endpoint-map inclusion. The existing ListPartition `carrier_singletons` helper
is public, and the Kruskal helper forwards to that unchanged proof. The source
stable-sort helper proofs are replaced by the accepted sorting interface. Three
unused premises were removed: `ts.Nodup` from `exchange_cost_identity`, `e ∉ ts`
from `cut_exchange`, and `NumberedGraph` from `gstepK2_sizes`. These statements are
stronger; their original source specializations remain available. The executor's
numbered-domain correctness requirements remain intact.

The generic global minimizer contract is definitionally equivalent to
`MinimumSpanningTree` on the selected domain. The exchange invariant already
quantifies over every competitor, so its final inequality directly supplies that
contract to `Optimization.selectionSquare`. No additional optimizer or
optimality oracle is introduced.

## Public consumers

`Problem` packages a numbered connected graph. `selectedTree` retains the actual
source-selected tree, with `selectedTree_result` proving that its fallback is
unreachable. `treeSquare` uses the shared optimization selection construction.
`costSquare` actually composes it with `Optimization.observationSquare costMCST`;
both sides retain the original problem. `selected_cost_attained` recovers an
optimal witness for the observed cost, and `selected_cost_eq` compares it to any
other independently optimal tree.

The raw `costResult : Graph → Option Int` remains available outside that total
domain. Its correctness and failure/connectivity equivalence require
`NumberedGraph`. `costResult_perm` proves equal optional costs under input-edge
permutation, retaining the same vertex list. Equal-weight inputs can choose
different edge sets, so this theorem deliberately concerns cost agreement.

## EDD and statement review

The starting obligations were to connect the source's global cut argument to the
accepted connectivity/sorting interfaces and to a total selected-tree/cost
consumer. The existing connectivity and sorting libraries supplied the needed
operations and observations; the missing connections were Kruskal's reachable
invariant, competitor-preserving exchange and its justified total domain.
The source diagnostics provided concrete expected results before their new
consumer connections were added.

All sixteen source diagnostics are named checked theorems in
`Examples.Kruskal`, with public optimum, source-step or failure contracts:

| Diagnostic | Expected mathematics or exact source behavior |
|---|---|
| D01 | Empty wrapper returns none; no nonempty spanning tree exists. |
| D02 | Singleton returns no edges without validating an unused malformed edge. |
| D03 | Supported disconnected input fails. |
| D04 | Weighted triangle returns reversed acceptance order; global optimum 1+2=3. |
| D05 | Tied triangle permutations select different edge sets; optimum 1+1=2. |
| D06 | Identical/reversed parallels preserve the exact unused suffix. |
| D07 | Negative loops are skipped; global optimum −5+(−2)=−7. |
| D08 | Numbered vertices in order 3,1,2 retain that order in the result. |
| D09 | Connected labels 10,20 remain outside the source adapter domain. |
| D10 | Overlapping raw blocks follow first-match lookup and concatenate duplicates. |
| D11 | An internal same-name loop is skipped, then exhaustion fails. |
| D12 | An extra step fails on an all-internal suffix after a completed tree. |
| D13 | Source g4 has global optimum 5+6+7=18. |
| D14 | Arbitrary cycle-edge removal can discard the chosen forest and raise cost 3 to 4. |
| D15 | A single edge of arbitrary integer weight is globally optimal. |
| D16 | A symbolic loop is skipped; a following crossing edge is taken and every remaining edge is untouched. |

Additional applications exercise the actual composed consumers, the finite-carrier
query on unsupported labels, signed symbolic costs, the disconnected failure
contract, a universal competitor bound from the cost square, equal cost for tied
input permutations, exact residual invariants, and forest/spanning cardinality
of the public selected tree. Computed executor results serve as hypotheses to
public correctness results. Arithmetic alone does not establish optimality.

Statement review covered the complete selected source closure and local additions:

- The reachability bridge is an equivalence on the same finite carrier and edge
  endpoints. Graph order remains observable in tree results, while connectivity
  forgets ordering and repeated edge requests.
- Forest removal quantifies over each chosen edge and excludes loops and cycles.
  The chosen-edge nodup premise does not restrict repeated input occurrences.
  Spanning and optimum predicates are independent of the executor.
- Raw step/run equivalences preserve failure, first-name choices, skip behavior
  and suffix order on malformed states. Invariant and minimum theorems state the
  additional valid numbered domain instead of deriving it from raw success.
- The walk/cut and forest-extension claims preserve all already chosen edges.
  Their weak weight comparison admits ties, and integer cost arithmetic admits
  negative weights. D14 checks why arbitrary cycle removal would be inadequate.
- Successful-step counting counts accepted crossing edges, not scanned edges.
  The partition count drops once per accepted edge. Definedness, the n−1 result,
  cardinality and residual claims share the full reachable invariant.
- The exchange invariant ranges over every feasible competitor. Cost uniqueness
  and input-permutation agreement do not identify tied witnesses.
- `Problem` carries nonempty numbered connectivity; selection is executable and
  its fallback is proved unreachable. Composition preserves problem identity and
  observes the image of the independent set of minimizers. Raw optional outputs
  retain their separate failure and domain contracts.

These checks are author statement review. Independent Standards, Spec and
supervising intent review, the fresh full source build and exhaustive axiom audit
are separate integration requirements.

## Provenance and scope

The preserved source is
[`adwh-checkpoint-233`](../history/algorithm-design-haskell/README.md), archive
SHA-256 `8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`.
Archive and selected member bytes were verified against the extracted reference:

| Archive member | SHA-256 |
|---|---|
| `project/adwh-lean/ADWH/Chapter09/Kruskal.lean` | `430e187d6d491e9304cbb4071a29c22036371d5e69630c76ef2e80d1aed97f49` |
| `project/adwh-lean/ADWH/Chapter09/DisjointSets.lean` | `2ce4a50a4188afea8c7a94a152d37f9f4a906ed356162912ee1b2f948e1acd49` |

The [208-row declaration ledger](adwh-kruskal-provenance.tsv) records all 139 named
Kruskal declarations, its sixteen anonymous diagnostics under their D01–D16
labels, 33 reused DisjointSets declarations and twenty local additions. Private
helpers use their lexical names in the ledger; generated constructor and private
compiler names are covered by their containing declaration. Additional anonymous
consumer applications are covered by `Examples.Kruskal`. Reused connectivity
ownership remains with #158, and stable sorting remains with #160.

The scope includes the complete source Kruskal module and its forest-extension
helpers. It excludes an array Kruskal executor, arbitrary-label nested-forest
Kruskal, corrected all-edge minimum spanning forest, Prim, directed/shortest
paths, enumeration, and operation/runtime bounds.

Targeted author validation: `direnv exec . lake build Examples.Kruskal
Examples.Connectivity Examples.StableSorting`. Full integration validation is
performed separately by the supervising session.
