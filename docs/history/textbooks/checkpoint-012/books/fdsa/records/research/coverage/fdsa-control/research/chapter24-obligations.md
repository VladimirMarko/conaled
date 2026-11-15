# Chapter 24: Graph Algorithms — source obligations and reuse limits

Research date: 2026-11-02. Local ticket: `FDSA-024`.

**State: queued; source preparation only.** This inventory performs no Lean
implementation or build, changes no ticket or acceptance status, and makes
no remote write. Its rows are future proof and implementation obligations,
not claims of formal coverage. Sequential implementation remains under the
parent's chapter-order gate.

## Sources, pins and licenses

| Source | Inspected identity |
|---|---|
| Book | Mohammad Abdulaziz, Chapter24, printed pp.267–292, PDF pages273–298, July27,2026 version. Official PDF <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. |
| Direct manuscript link | <https://isa-afp.org/entries/Graph_Algorithms.html>, *Elementary Graph Traversal Algorithms*, Mohammad Abdulaziz, published January14,2025. |
| Inspected formal companion | <https://isa-afp.org/release/afp-Graph_Algorithms-2026-10-26.tar.gz>, 36,596 bytes, SHA-256 `b841179282aa527c8d16c2ce645a881cc499183f94ba67c8c27d62e8b4478006`. The dated archive postdates the book; it is the inspected formal-source identity, not a claim about the source that generated the July PDF. |
| Imported graph theory | <https://isa-afp.org/entries/Graph_Theory.html>; dated archive <https://isa-afp.org/release/afp-Graph_Theory-2026-10-26.tar.gz>, 69,044 bytes, SHA-256 `e8b335a4d290fdb91837e4cf41f004ce98e87714a8f2e8831006f2a40185aae7`. The chapter's `Pair_Graph` imports its restricted reflexive-transitive closure `Rtrancl_On`. |
| Imported set/map specifications | Isabelle mirror pin `f86f290225eebcc52c1ae7dba2e098f405f51c21`; `src/HOL/Data_Structures/Set_Specs.thy` and `Map_Specs.thy`, already pinned for Chapter6. `Set2_Addons`, `Set_Addons`, and `Map_Addons` import those interfaces. |
| Licenses | AFP entries advertise BSD; <https://isa-afp.org/LICENSE>, SHA-256 `9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`. Isabelle BSD3 notice SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`. Preserve attribution/notices in any adaptation. |
| Lean reuse | conaled baseline `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`, inspected workspace HEAD `1aabd512284fe86254278ac631eda061d311050b`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`; Lean4.35.0 source `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Standard-library and Mathlib reuse is Apache-2.0. Inspection is not acceptance of local candidate changes. |

| Exact companion file | Bytes | SHA-256 |
|---|---:|---|
| `Graph_Algorithms/Pair_Graph.thy` | 6849 | `38a96f233fd7c52e3ec7089bf98f49f7d29d72f739332b16c0cdcb96f52d6fed` |
| `Graph_Algorithms/Vwalk.thy` | 43059 | `5f171c129e02af19319c5e40e2a3e31166dc1fb9fe47372c73db2bcb1b501fba` |
| `Graph_Algorithms/Dist.thy` | 32125 | `5ddcbb48abd04bd7b06b75a825ddc24bd3b3b9e13725c7da7a511a8b451c09d3` |
| `Graph_Algorithms/Pair_Graph_Specs.thy` | 11764 | `876cfbc9e9c63d3dfd72dc25dc566a29993e84ba29a28a7e3fe87b5490e8c52d` |
| `Graph_Algorithms/DFS.thy` | 35595 | `5f281c45e0bac2ac64957e273156686cc741a33468f03dc85a36ea0b5233ec77` |
| `Graph_Algorithms/BFS_2.thy` | 74642 | `b9d754fa88528ad2c92d85cff3085e457f6d9dfb907feecab5e5081a9b975554` |
| `Graph_Algorithms/More_Lists.thy` | 5959 | `5a4715420baebfdd94dbef5932aa4c92996c78f5d132db30d90e06a3cabcbc64` |
| `Graph_Algorithms/Enat_Misc.thy` | 415 | `ad87c96a786edc789d09c9dd9fccac51ebdf17f1aa84cafe1a1c125368001999` |
| `Graph_Algorithms/Set_Addons.thy` | 253 | `6bf72ba3ec33d2d253ce3744d6fbb40a2d3921a2111b0cb9a993f194d38375cf` |
| `Graph_Algorithms/Set2_Addons.thy` | 384 | `50a2219895c7e459915a1ab6e0ce5b1f98fe907dbc6e00eb47c17bc44119c7e5` |
| `Graph_Algorithms/Map_Addons.thy` | 224 | `eabcb26db92ba486ec89af1cff69b5c0fe888802f89ebd1efc730754b1e847a9` |
| `Graph_Theory/Rtrancl_On.thy` | 4498 | `f010434854a7104b971c41d33e76c79be7d2ae058754ebc0ab1fef1ead6ff45a` |

All reading copies are under `book-source/`. The original inventory and
provenance are the deliverable; the manuscript is not redistributed. There
are **no numbered exercises** in Chapter24. All nine numbered results,
displayed definitions and auxiliary mathematical assertions, including the
unprinted invariants required by the cited proofs, remain in scope.
Historical comparisons and discussions of automation are identified
analysis, not additional universal performance theorems. A reference to
matching, flow or diameter algorithms does not request formalization of
those entire external algorithms.

No active `sorry`, `oops`, or `axiomatization` was found after stripping
nested Isabelle comments from the archive's theory files. In particular,
the unfinished `forest_insert`/`forest_union` material at the end of
`Dist.thy` is **inside a comment**, not a checked theorem or a trusted
axiom. The active BFS development constructs a DAG with multiple parents;
it does not establish the commented unique-walk forest specification.

## Exact semantic boundaries and reuse

Use `E : Set (V × V)` for the abstract edge relation, `vertices E` for its
incident vertices, and `N E u = {v : (u,v) ∈ E}`. The source has no separate
ambient vertex set. An empty list is a walk, but a singleton `[v]` is a
walk **only when `v ∈ vertices E`**. Thus
`distance ∅ v v = ∞`, whereas a reflexive ambient-vertex walk relation
would give zero. Self-loops are permitted. A self-loop makes its endpoint
a vertex even when there are no other vertices.

An adjacency map may store an empty neighbor set. Such a map key is not
necessarily a vertex of its abstract graph. Likewise a BFS source with no
forward edge can disappear from the final DAG's incident-vertex set.
These are semantic facts, not implementation failures. Any bridge to a
library graph must preserve them explicitly.

| Existing component | Useful support and required limit |
|---|---|
| Mathlib `Combinatorics/Digraph/Basic.lean`: `Digraph`, `Digraph.ext`, `adj_inj`, subgraph order/lattice | A directed relation carrier allowing loops. Set `Adj u v := (u,v) ∈ E`. `SimpleGraph` imposes symmetry and irreflexivity and is not the source carrier. |
| Mathlib `Quiver/Path/Vertices.lean`: `vertices`, `vertices_length`, `vertices_head?`, `vertices_getLast`, `vertices_comp`, `exists_eq_comp_of_mem_vertices` | Endpoint/list and composition facts, after an incident-vertex bridge. `Path.nil` exists at every ambient vertex, so reuse without that bridge changes zero-length reachability. |
| Mathlib `Quiver/Path/Decomposition.lean`: `exists_notMem_mem_hom_path_path_of_notMem_mem`, `exists_mem_notMem_hom_path_path_of_notMem_mem` | Useful boundary-crossing decompositions for DFS stack/frontier cuts and BFS frontier cuts. Directed order and endpoint conventions still need correspondence. |
| Mathlib `Data/ENat/Lattice.lean`: `ENat.iInf_eq_natCast_iff`, `ENat.exists_eq_iInf`, `ENat.iInf_natCast_eq_top`, `iInf_natCast_ne_top`, `ENat.iInf_add`, `add_iInf`, `sInf_add` | Extended-natural minima and addition. Nonempty index premises for attainment, finite-value premises for cancellation/subtraction, and the empty source set must remain explicit. |
| Lean `Std/Data/TreeMap/{Basic,Lemmas}.lean` | `getElem?_emptyc`, `getElem?_insert`, `getElem?_insert_self`, `getElem?_erase`, `keys`, `mem_keys` provide a concrete finite adjacency-map candidate. This is a size-balanced implementation, not red-black merely because it is a tree map. |
| Lean `Std/Data/TreeSet/{Basic,Lemmas}.lean` | `mem_insert`, `mem_erase`, `mem_union_iff`, `mem_inter_iff`, `mem_diff_iff`, `toList`, `mem_toList`, `isEmpty_iff_forall_not_mem`, `min?`, `min_mem` can realize finite vertex sets and selection. Require the actual comparator laws, notably `TransCmp` and `LawfulEqCmp`, when comparator equality must mean vertex equality. |
| conaled `Applications/Search/HeuristicSemantics.lean` | `Eval`, `run_eval`, `eval_run`, `run_add_budget`, `run_unique`, `eval_unique` are a project precedent for the HOL-domain/bounded-run bridge. They are specialized to different transitions, not an existing generic DFS proof. Budget exhaustion must remain distinct from completed unreachable failure. |
| conaled `Applications/Dijkstra/Core.lean`, `Optimality.lean` | `Distance := Option Nat`, `toTop`, `dle_iff`, `toTop_plus`, and `dijkstra_correct` offer independent finite-distance checks after a unit-weight graph bridge. Dijkstra keeps one predecessor, not the BFS DAG's multiple parents. Its fixed rounds and queue choices are not source DFS/BFS costs. |
| Mathlib `Quiver/Arborescence.lean`: `shortestPath`, `geodesicSubtree` | Noncomputable shortest-path/arborescence mathematics under rooted-connectivity premises. It chooses a path/parent, whereas this chapter's executable BFS keeps every forward layer edge. |
| Mathlib `WellFounded.prod_lex`, `Set.ncard_sdiff_singleton_lt_of_mem`, finite-set cardinality laws | Termination scaffolding. Actual state validity, finiteness, strictness and recurrence correspondence are new obligations. |

The bounded repository search found no existing exact implementation of
this chapter's DFS or BFS recurrence. Heuristic search expands multiple
children from a removed frontier entry and marks its closed set at a
different time. It cannot discharge a source DFS proof merely by choosing
a stack-like priority. Neither an existing search path nor Dijkstra's
single-parent map represents the chapter's BFS DAG.

`Set_Choose.choose` in the book and active AFP source is stronger than an
ordinary arbitrary-representation set interface: `s ≠ empty` implies
membership of the selected value, even before an invariant premise is
written. Combined with the base set laws, it forces every **valid**
extensionally empty set to be represented by `empty`. A Lean adaptation
may instead expose selection with a proof of nonemptiness, or `Option`
selection plus its exact success/failure law, and use `isEmpty`. Record the
bridge to the source's equality guard; do not assume raw representation
equality is extensional for every set implementation. No global
`Inhabited V` is justified just to give `sel empty`, `head []`, or
`the none` an arbitrary value.

## Exhaustive coverage checklist

Notation in the rows: `A g` is the adjacency representation's abstract edge
set; `S s` is a vertex-set representation's abstraction; `U = S srcs`;
`d E u v` is vertex distance; `D E U v` is distance from a source set.
All mathematical walk lengths are **edge counts** `p.length − 1`.
Named source assertions carry the locale/interface and graph assumptions
specified here even where the printed formula suppresses them.

### Graph model, finite interfaces and operations

| ID | Required object or checked statement | Source, premises and reuse/gap |
|---|---|---|
| C24-001 | Directed edge-set carrier `Set (V × V)`, without symmetry, irreflexivity, weights or a global finiteness assumption. | pp.267–268; `Pair_Graph.dgraph`. Abstract mathematical carrier; executable representation is separate. |
| C24-002 | `vertices E = ⋃ {( {u,v} ) : (u,v) ∈ E}` and endpoint/image characterization `fst '' E ∪ snd '' E`. | p.267; `dVs`, `dVs_eq`. Include empty graph, insertion, union and edge-membership consequences used later. |
| C24-003 | `N E u = {v : (u,v) ∈ E}`, with membership/edge equivalence and every neighbor incident in `E`. | p.267; `neighbourhood`, `in_neighbourhood_dVs`. Direction matters. |
| C24-004 | Empty-list walk equation. | p.268; `Vwalk.vwalk0`; empty walk is allowed but is not a walk *between* two endpoints. |
| C24-005 | Singleton walk iff its vertex belongs to `vertices E`. | p.268; `vwalk1`, `vwalk_1`; explicit guard prevents ambient reflexivity from changing the chapter. |
| C24-006 | `walk E (u::v::vs) ↔ (u,v) ∈ E ∧ walk E (v::vs)`. | p.268; `vwalk2`, `vwalk_2`; exact recursive characterization/induction. |
| C24-007 | `walkBetween E u p v` requires a nonempty walk with first vertex `u` and last vertex `v`. | p.268; `vwalk_bet`. Use guarded/optional endpoints; no undefined empty-list observation. |
| C24-008 | Walk endpoints and all listed vertices are incident; singleton/edge paths, prefix/suffix splitting and edge concatenation preserve the source walk relation. | pp.276–278,281–289 proof support; `Vwalk` endpoint, `split_vwalk`, `vwalk_bet_pref/suff`, concatenation lemmas. Quiver bridges can reuse existing proofs after C24-005. |
| C24-009 | Edge list of a nonempty vertex walk has length `p.length−1`; composition removes the duplicated joining endpoint and adds edge lengths. | pp.281,288–289; `edges_of_vwalk_length`, `vwalk_bet_transitive`. Needed for triangle and shortest-prefix proofs. |
| C24-010 | Existence of a walk between endpoints implies existence of a distinct-vertex walk between them. | p.268's reachability promise versus Theorem24.3 p.279; cycle erasure or the minimum-length/distinctness proof closes this logical gap. No finiteness of the whole graph is necessary. |
| C24-011 | Restricted reflexive-transitive reachability agrees with existence of a nonempty source vertex walk. | Formal companion `Pair_Graph.reachable` and `Vwalk.reachable_vwalk_bet_iff`; restriction is to `vertices E`. Use only as needed for chapter claims. |
| C24-012 | List representation neighborhood membership has a linear worst-case comparison bound, with a linear witness family. | p.269 mathematical performance claim. Reuse prior list/search counts; assume unit-cost lawful equality/comparison and state which operation count is measured. |
| C24-013 | A balanced search-tree set gives logarithmic neighborhood membership work under its balance/order invariant and comparison tariff. | p.269; discharge through already formalized balanced-set chapters and their size/height bridge. This sentence is not a detailed DFS complexity theorem. |
| C24-014 | Extend the Chapter6 set contract by valid nonempty selection and prove the source `s ≠ empty` guard matches nonempty abstraction for the chosen representation. | Figure24.2 p.270; active `Pair_Graph_Specs.Set_Choose`, lines41–77. Preserve its stronger canonical-empty consequence explicitly. |
| C24-015 | Empty selection has explicit failure or is guarded by a nonempty proof; successful selection is an actual member. | Lean adaptation of C24-014 and cross-cutting decisions. Empty payload types remain usable where no selection is made. |
| C24-016 | Assemble the adjacency-map and neighbor-set interfaces with consistent vertex/value types and unambiguous names; reuse Map, Set and Set2 laws. | Figure24.3 p.271, Figure24.4 p.273; `Pair_Graph_Specs` locale. Avoid a duplicate project-wide hierarchy. |
| C24-017 | `neighbors g u` returns the stored vertex set on successful lookup and the vertex-set empty value otherwise. | p.271; `neighb`, lines139–142. Optional lookup and empty-default semantics are exact. |
| C24-018 | `addEdge g u v` on a missing `u` inserts `v` into an empty neighbor set and updates the map at `u`. | pp.270–271; `add_edge`. It need not add `v` as a map key. |
| C24-019 | `addEdge` on an existing key inserts `v` into its neighbor set and updates that key; preserve or explicitly relate the source's repeated lookup. | p.271; source lines148–163 pattern-matches one lookup and then calls it again under `the`. A shared-lookup optimization is value-equivalent, not automatically cost-identical. |
| C24-020 | `deleteEdge` leaves an absent source key unchanged; otherwise deletes the target from its stored set and updates the key, even if that set becomes empty. | p.272 invokes the operation but omits its definition; recover `delete_edge`, lines165–175. The same repeated-lookup caveat applies. |
| C24-021 | `graphInv g` combines the map invariant with the neighbor-set invariant for every successful lookup. | p.272; `graph_inv`, line134. No extra assumption that every stored set is nonempty. |
| C24-022 | `A g = {(u,v) : isin (neighbors g u) v}`; under `graphInv`, this equals abstraction membership. | pp.271–272; `digraph_abs`, `are_connected_abs`. Do not conflate keys with incident vertices. |
| C24-023 | Under `graphInv g`, `S (neighbors g u) = N (A g) u` and lookup-neighbor membership iff abstract edge membership. | Three displayed abstraction facts p.272; `neighbourhood_abs`, `are_connected_abs`. |
| C24-024 | Empty graph representation is valid and abstracts to no edges. | Interfaces and initialization pp.279,290; source empty-map/default-neighbor laws. |
| C24-025 | Adding an edge preserves `graphInv` and abstracts to exact set insertion of `(u,v)`. | p.272; `adjmap_inv_insert`, `digraph_abs_insert`, lines311–315. Repeated insertion has set semantics. |
| C24-026 | Deleting an edge preserves `graphInv` and abstracts to removal of exactly `(u,v)`. | p.272 invariant assertion plus companion `adjmap_inv_delete`, `digraph_abs_delete`, lines317–321. |
| C24-027 | Preserve the precise source finiteness predicates: finite successful-lookup domain and finite abstraction of every represented vertex set. | pp.279,286; `finite_graph`, `finite_vsets`, lines135–136. The latter quantifies over all representations, not just current valid state sets. Weaker sufficient assumptions may be proved separately. |
| C24-028 | A valid graph satisfying C24-027 has finitely many abstract edges and incident vertices; individual neighborhoods are finite. | `Pair_Graph_Specs.finite_graph`, `finite_vertices`; `Pair_Graph.finite_vertices_iff`. The abstract edge-set type itself remains unrestricted. |
| C24-029 | Provide a concrete lawful finite map/set/selection/Set2 realization and its abstraction bridge, with executable enumeration for later helpers. | §24.1.5 p.280. Earlier red-black sets/maps are the source's example; Std tree maps/sets are another possible adapter with distinct implementation identity. |

### DFS transition system, invariants and correctness

| ID | Required object or checked statement | Source, premises and reuse/gap |
|---|---|---|
| C24-030 | State stores a vertex-list `stack`, vertex-set `seen`, and a result flag `Reachable` or `NotReachable`. | pp.273–274; `DFS_state`, `return`. Stack head is current vertex; stack order is reversed path order. |
| C24-031 | DFS assumptions: `graphInv G`, finite lookup domain, finite represented sets, and `s ∈ vertices (A G)`. | p.279; `DFS_axioms`, source line41. Target `t` need not be an incident vertex. |
| C24-032 | Initial state has stack `[s]`, seen singleton `s`, and flag `NotReachable`. | p.279; `initial_state`, lines77–78. Initial flag is overwritten at termination, not a proof of initial unreachability. |
| C24-033 | Empty stack terminates with `NotReachable`, preserving seen and stack. | p.274; `DFS` empty branch, `DFS_ret1`. |
| C24-034 | Nonempty stack with head `t` terminates with `Reachable`, preserving the live path stack. | p.274; `DFS_ret2`. Goal test precedes unseen-neighbor processing. |
| C24-035 | If head `v ≠ t` and `neighbors G v \ seen` is nonempty, select `u` from that difference, push `u` onto the unchanged old stack, and insert `u` into seen before recursion. | p.274; `DFS_upd1`, exact `DFS` recurrence. Do not expand all neighbors or pop `v` before descending. |
| C24-036 | If head `v ≠ t` has no unseen neighbors, pop only the head and recur with seen unchanged. | p.274; `DFS_upd2`. Discovery and completion are different events. |
| C24-037 | Make the four branch guards exhaustive/exclusive, and prove the guarded equation for each recursive/terminal branch. | pp.274–276; `DFS_cases`, `DFS_simps`, `DFS_call_1/2_conds`, `DFS_ret_1/2_conds`. `head` is observed only under a nonempty-stack guard. |
| C24-038 | Conditional computation induction has hypotheses for both recursive successors and an explicit terminating-domain premise. | pp.275–276; `DFS_induct`, `DFS_domintros`. A Lean well-founded/evaluation formulation must recover this principle rather than assume unrestricted termination. |
| C24-039 | Connect a concrete total valid-state runner, or a bounded runner plus finite evaluation relation, to the exact DFS equations and completed results. | §24.1.3 and project partiality requirements. Fuel exhaustion is not `NotReachable`; generic heuristic-search semantics is only a proof pattern. |
| C24-040 | `WF st`: the seen representation is valid. | p.276; `invar_well_formed`, line243. |
| C24-041 | `StackWalk st`: reversing stack gives an abstract walk in the fixed graph. | p.276; `invar_stack_walk`, line247. |
| C24-042 | `SeenStack st`: stack is distinct, its vertex set is contained in seen, and seen is contained in graph vertices. | p.277; `invar_seen_stack`, lines250–254. All three conjuncts matter. |
| C24-043 | `SourceInStack st`: a nonempty stack ends in `s`. | p.277; `invar_s_in_stack`, lines256–258. It is conditional because failure empties the stack. |
| C24-044 | `SeenCut st`: every distinct walk from any seen vertex to target `t` intersects the live stack. | p.276; `invar_visited_through_seen`, lines260–263. Quantification is over all seen vertices and all distinct endpoint-correct walks. |
| C24-045 | Preserve WF in push, pop and both returns, then in any terminating run. | pp.276–278; `invar_well_formed_holds_*`, lines314–337. |
| C24-046 | Preserve StackWalk in push using chosen-neighbor membership, and in pop using walk prefixes; returns preserve it. | pp.276–278; `invar_stack_walk_holds_*`, `invar_2_holds`, lines348–377. |
| C24-047 | Preserve every SeenStack conjunct; a pushed selected vertex is unseen, so cannot duplicate a stack vertex. | p.277 and termination proof; `invar_seen_stack_holds_*`, lines386–417. |
| C24-048 | Preserve SourceInStack through push, pop, returns and any terminating run. | p.277; `invar_s_in_stack_holds_*`, lines426–455. |
| C24-049 | Push preserves SeenCut: old witnesses remain in the extended stack and a newly seen start vertex itself lies in that stack. | p.277 proof context; `invar_visited_through_seen_holds_1`, lines474–479. |
| C24-050 | **Lemma24.1:** pop preserves SeenCut under pop guard, WF, SeenStack and old SeenCut. | pp.277–278; source `invar_visited_through_seen_holds_2`, lines482–563. Global DFS graph/ADT assumptions are inherited. Retain the corrected suffix argument below. |
| C24-051 | Both returns preserve SeenCut. | p.278 proof support; `invar_visited_through_seen_holds_4/5`, lines565–570. |
| C24-052 | **Lemma24.2:** a terminating DFS preserves SeenCut given WF, SeenStack and SeenCut initially. | p.278; `invar_visited_through_seen_holds`, lines571–581, conditional induction C24-038. |
| C24-053 | Prove the corresponding whole-run preservation of the other four displayed invariants with their actual sufficient premises. | pp.276–279; companion global invariant theorems. One aggregate inductive valid-state predicate may package them without dropping individual projections. |
| C24-054 | Seen grows monotonically from initial to final state. | Used in Theorem24.3 p.279; source `state_rel_1`, transition/transitivity/run lemmas, lines587–626. This retains `s` in final seen even when final stack is empty. |
| C24-055 | A completed `NotReachable` result has empty stack; a completed `Reachable` result has nonempty stack with head `t`. | pp.279–280; source `ret1_holds`, `ret2_holds`, lines631–661. Initial flag alone gives no such terminal characterization. |
| C24-056 | First termination measure is the finite cardinality of `vertices (A G) \ S seen`. | pp.278–279; `call_1_measure`, line265. This is not a count of finished vertices. |
| C24-057 | Second measure is cardinality of `set stack`; under SeenStack it equals stack length. Use lexicographic order with the first measure primary. | pp.278–279; `call_2_measure`, `DFS_term_rel`, lines268–273. |
| C24-058 | Push strictly decreases the first measure by discovering a previously unseen graph vertex. | p.279; source `call_1_terminates`, `in_DFS_term_rel`. Establish finite complement and actual selected membership. |
| C24-059 | Pop leaves the first measure equal and strictly decreases the second; stack distinctness prevents removal of an element still present later. | p.279; `call_2_measure_1`, `call_2_terminates`, lines697–707. |
| C24-060 | WF and SeenStack imply DFS termination under the global graph assumptions. | p.279 displayed implication; `DFS_terminates`, lines719–728. Do not replace this with an arbitrary finite budget. |
| C24-061 | All five displayed invariants and the terminating-domain predicate hold initially. | p.279; `initial_state_props`, lines732–739. Requires `s` to be incident. |
| C24-062 | **Theorem24.3:** completed initial DFS failure implies no distinct walk from `s` to `t`. | p.279; `DFS_correct_1`, lines741–753. Preserve the exact printed distinctness qualifier, then strengthen via C24-010. |
| C24-063 | **Theorem24.4:** completed initial DFS success returns a live stack whose reversal is a walk from `s` to `t`. | pp.279–280; `DFS_correct_2`, lines755–773. Invariants also give a distinct returned path. |
| C24-064 | Fulfil the opening iff promise: DFS succeeds iff a source-model walk exists; failure iff none exists. | p.268; derive from C24-060–063 plus cycle erasure and the two result constructors. The distinct-only failure theorem alone does not yet express the full promise. |
| C24-065 | Domain/edge regressions: valid `s=t` returns `[s]`; a target outside graph vertices is unreachable; omitting the source-membership premise makes success at `s=t` on an empty graph invalid. | pp.268,279; retain the empty-graph counterexample rather than silently change walk reflexivity. |
| C24-066 | Instantiate and execute the exact DFS recurrence with a lawful concrete graph/container adapter and demonstrate both result branches and a cycle. | §24.1.5 p.280. Any minimum selector is an allowed deterministic realization, but not the only permitted successful path. |
| C24-067 | Correct and document the prose description of seen as completed vertices and insertion on popping. | p.274 versus displayed recurrence and active `DFS.thy`: seen records discovery, insertion happens on push, and pop does not change it. Keep a small state trace demonstrating the distinction. |

### Distances and shortest-walk lemmas

| ID | Required object or checked statement | Source, premises and reuse/gap |
|---|---|---|
| C24-068 | Extended-natural distance values, infinity and coercions from natural edge counts. | pp.280–281; source `enat`; Mathlib `ENat` is an appropriate value-level carrier. Distances are unweighted and nonnegative. |
| C24-069 | `d E u v` is the infimum over all vertex lists of their edge count when they are walks between `u,v`, and infinity otherwise. | pp.280–281; `Dist.distance`, lines9–10. This is a specification, not a computable enumeration of all lists. |
| C24-070 | Distance is finite iff a source-model walk/restricted reachability exists, and equals infinity otherwise. | p.281 prose; `reachable_dist`, `unreachable_dist`, `dist_reachable`. No finite-graph premise is required. |
| C24-071 | A finite distance is attained by a walk of exactly that many edges; every endpoint-correct walk is at least that long. | pp.281,287–289; `reachable_dist_2`, `vwalk_bet_dist`, `shortest_path_exists_2`. Well-ordering of natural lengths is enough. |
| C24-072 | `d E u v = 0` iff `u=v` and `v ∈ vertices E`; either endpoint outside vertices forces infinity. | p.281 interpretation; `distance_0`, `dist_inf`, `dist_inf_2`. Include `d ∅ v v=∞` as a bridge regression. |
| C24-073 | **Theorem24.5:** `d E u w ≤ d E u v + d E v w`, including unreachable/infinite cases. | p.281; `triangle_ineq`, lines61–85. Finite cases use shortest witnesses and concatenation; do not cancel infinity. |
| C24-074 | `shortestWalk E u p v` is endpoint-correct walk plus equality of its edge count and `d E u v`. | p.281; book `shortest_walk`, companion `shortest_path`, line141. Match the name through an explicit reconstruction entry. |
| C24-075 | Shortest walks are distinct-vertex walks. | pp.281,289 supporting graph theory; `shortest_path_distinct`, lines280–298. Cycle deletion strictly lowers finite edge length. |
| C24-076 | A nonempty shortest-walk prefix/suffix split at a listed vertex is shortest for its endpoints; prefix distance is bounded by full distance. | p.289 proofs; `shortest_path_split_1/2`, `shortest_path_split_distance`. Preserve endpoint overlap and edge-count arithmetic. |
| C24-077 | `D E U v = inf {d E u v : u ∈ U}` and its universal lower-bound/minimum characterization. | p.281; `distance_set`, lines379–380. Arbitrary, possibly infinite, source sets are allowed mathematically. |
| C24-078 | Empty source set has infinite distance; source-set distance zero iff `v ∈ U ∩ vertices E`; a vertex outside graph vertices has infinite set-distance. | pp.281,286 initialization; `dist_set_inf`, `distance_set_0`, `finite_dist_nempty`. State the incident-vertex premise in the source theorem. |
| C24-079 | Finite source-set distance has an attaining source in `U` and an attaining finite shortest walk; for any nonempty `U`, the extended-natural infimum is attained even when all values are infinity. | pp.287–289 proof support; `distance_set_wit`, `dist_set_not_inf`, `dist_not_inf'`, `Inf_enat_def1`. Distinguish these two attainment statements. |
| C24-080 | Enlarging edge sets cannot increase vertex distance or source-set distance; enlarging the source set cannot increase set-distance. | **Equation24.1** p.287; `distance_subset`, `distance_set_subset`, `distance_set_union`. All are inequalities in the indicated direction. |
| C24-081 | For an edge `u→v`, `d E x v ≤ d E x u+1` and `D E U v ≤ D E U u+1`; preserve the companion's `U≠∅` premise or prove an explicit empty-set extension. | pp.288–289; `distance_neighbourhood'`, `distance_set_neighbourhood`, lines659–670. |
| C24-082 | A finite positive distance has a predecessor whose distance is one smaller and which has an edge to the target. | Used in BFS invariant proofs pp.288–289; `distance_parent`, `distance_set_parent/parent'`. Retain non-source/positive-distance and finite-distance conditions. |
| C24-083 | If `u∈U` attains finite `D E U v`, there is a shortest walk `u::p` to `v` whose tail contains no source from `U`. | First displayed lemma p.289; `dist_not_inf'''`, lines429–446. Includes empty tail when `u=v`. |
| C24-084 | If `u∈U` attains source-set distance at `v`, then along any shortest `u→v` walk, each vertex `w` satisfies `D E U w = d E u w`. | Second displayed lemma p.289; `distance_on_vwalk`, lines480–523. |
| C24-085 | If that shortest walk passes through `w∈W`, and all members of `W` have source-set distance `d E u w`, then `D E (U∪W) v = D E U v − d E u w`. | Third displayed lemma p.289; `shortest_path_dist_set_union`, lines528–620. Shortest-walk hypotheses make the relevant distances finite; use the actual extended-natural subtraction law. |
| C24-086 | Correct the statement that `Inf (range f)` is an `argmin` witness. | p.281. It is the infimum **value**; a minimizing path/source is a separate existence theorem C24-071/079. Retain this type/meaning correction. |

### Multi-source BFS DAG and correctness

| ID | Required object or checked statement | Source, premises and reuse/gap |
|---|---|---|
| C24-087 | BFS state contains current frontier, visited vertices and the output adjacency representation. Use one consistent output field name. | pp.282–283; printed `DAG` versus active source `parents`. See explicit naming defect below. |
| C24-088 | Fixed parameters are `G`, `srcs`, `expandTree` and `nextFrontier` over the shared graph/Set2 interfaces. | Figure24.6 p.284; `BFS` locale, lines23–46. The two helpers are specified, not implemented in the companion. |
| C24-089 | `expandTree H front vis` preserves graph validity and abstracts to `A H ∪ {(u,v) : u∈S front ∧ v∈N (A G) u \ S vis}`. | Figure24.6; require validity of `H`, front, vis and fixed `G`. Every eligible edge is retained, including two parents of the same new vertex. |
| C24-090 | `nextFrontier front vis` preserves vertex-set validity and abstracts to `(⋃ u∈S front, N (A G) u) \ S vis`. | Figure24.6; require valid front, vis and fixed graph. This is set union, not concatenation with duplicate occurrences. |
| C24-091 | Preserve all BFS assumptions: valid/finite fixed graph, finite represented vertex sets, `U⊆vertices (A G)`, finite neighborhoods, `U≠∅`, and valid `srcs`. | p.286; `BFS_axiom`, lines49–55. Some finiteness premises are redundant but must be visible before any proved weakening. |
| C24-092 | Exact recursive step: form `vis′=visited∪current`; then `H′=expandTree H current vis′`; then `cur′=nextFrontier current vis′`; recurse on all three updated fields. | p.283; `BFS`, `BFS_upd1`, lines61–92. Both helpers use the same old frontier and the same newly enlarged visited set. |
| C24-093 | If current is empty, return the whole state unchanged. | p.283; `BFS_ret1`. Visited need not be empty. |
| C24-094 | Initial state has empty output graph, current equal to `srcs`, and empty visited set. | p.290; `initial_state`, line231. The pseudocode's initial `visited=current` is redundant for its first update but is not this exact initial record. |
| C24-095 | One recursive guard and one terminal guard yield conditional equations, domain introduction and a computation-induction principle. | pp.283–285; `BFS_cases`, `BFS_simps`, `BFS_induct`, `BFS_domintros`, lines114–159. Connect to a total valid-state implementation or proved evaluation relation. |
| C24-096 | WF requires valid current and visited sets, valid output graph, and finite current/visited abstractions. | p.286; `invar_well_formed`, lines163–167. |
| C24-097 | Subsets invariant includes: output edges ⊆ input edges; visited/current ⊆ graph vertices; output incident vertices ⊆ visited∪current; sources ⊆ visited∪current. | pp.286–287; `invar_subsets`, lines169–175. No converse vertex equality is printed or generally true for sources. |
| C24-098 | Distance invariant: for every non-source incident input vertex in visited∪current, input and output source-set distances are equal. | p.285; `invar_dist`, lines206–210. The excluded source vertices are essential under the edge-only vertex model. |
| C24-099 | Parent-walk invariant: every output walk from a source `u∈U` to `v` has edge length exactly `D (A G) U v`. | p.285; `invar_parents_shortest_paths`, lines212–216. It is stronger than merely choosing one shortest witness. |
| C24-100 | Frontier-cut invariant: any input walk from visited∪current to outside that union intersects current. | p.285; `invar_goes_through_current`, lines199–204. This is about all walks, without DFS's distinctness restriction. |
| C24-101 | Recover auxiliary `invar_3_1`: if `v` is current, then for every ambient `u`, membership of `u` in current is equivalent to equality of their source-set distances. | Unprinted auxiliary support mentioned p.288; `BFS_2`, lines177–180. This characterizes the whole current distance layer, not only equality among current vertices. |
| C24-102 | Recover `invar_3_2`: each already discovered vertex has distance at most that of any current vertex. | `BFS_2`, lines182–185. Used with complete layers in distance-bound preservation. |
| C24-103 | Recover `invar_3_3`: all neighbors of every visited vertex are in visited∪current. | `BFS_2`, lines187–189. This is closure of processed vertices. |
| C24-104 | Distance-bounded invariant: if `v` is discovered and `D (A G) U u ≤ D (A G) U v`, then `u` is discovered. | p.288; `invar_dist_bounded`, lines191–197. Quantifies over all ambient `u`, so finite-distance/reachability support is important. |
| C24-105 | Recover `invar_current_reachable`: every vertex in visited∪current has finite source-set distance. | `BFS_2`, lines412–459; its name covers both sets. This prevents an infinite-distance layer from claiming arbitrary ambient vertices. |
| C24-106 | Recover `invar_current_no_out`: a current vertex has no outgoing edge yet in the output graph. | `BFS_2`, lines982–1017. Used by shortest-output-walk preservation and carried in the source termination package. |
| C24-107 | From initialization and the exact step, current and visited are disjoint, new frontier is outside the old discovered union, and discovered/visited sets grow monotonically. | pp.282–283,289–290 operational meaning. These may be derived lemmas rather than extra source assumptions. |
| C24-108 | Prove transition and terminal preservation of WF and Subsets, and their conditional whole-run forms. | pp.286–287; `invar_well_formed_holds_*`, `invar_subsets_holds_*`, lines276–337. |
| C24-109 | Prove preservation of complete-current-layer, earlier-layer bound, visited-neighbor closure and distance-bounded invariants with their dependency premises. | pp.288–289, source `invar_3_1/2/3_holds_upd1*`, `invar_dist_bounded_holds_upd1`, lines512–697. These omitted proofs are retained obligations. |
| C24-110 | Prove preservation of finite discovered reachability and current-no-out, including their required representation/subset invariants. | Source lines431–461,997–1017. Needed to support the abstract correctness claims, not merely documentation. |
| C24-111 | Prove frontier-cut preservation using an input walk's first boundary-crossing edge, and extend it through a terminating run. | p.289 describes this walk-based proof; `invar_goes_through_active_holds_upd1`, `invar_goes_through_current_holds`, lines738–823. |
| C24-112 | **Lemma24.6:** under BFS assumptions, nonempty-current guard, WF, Subsets, distance-bounded and old distance invariant, one step preserves the distance invariant. | pp.286–288; `invar_dist_holds_upd1_new`, lines825–963. Other auxiliary invariants are not needed as new premises for this specific step lemma. |
| C24-113 | Infinite-distance case of Lemma24.6 follows from output subgraph inclusion; old discovered non-source case follows by sandwiching old/new/output/input distances. | p.287; source lines835–878. The target's non-source condition is inherited from the invariant, even when suppressed in the prose. |
| C24-114 | **Equation24.2:** for a new frontier vertex `v` and its old-current predecessor `v′`, `D input U v = D input U v′+1`. | p.288; `dist_current_plus_1_new`, lines463–502. Uses edge upper bound, discreteness of `ENat`, distance-boundedness, and genuinely new membership. |
| C24-115 | **Equations24.3–24.4, corrected domain:** when that predecessor is not a source, old distance preservation and subgraph sandwiches transfer its distance through old/new DAGs. | p.288; source lines918–950 explicitly assumes `v′∉U`. The printed unrestricted equalities are false at a newly represented source. |
| C24-116 | Complete the missing source-predecessor case: if `v′∈U`, its new outgoing edge makes it a vertex of the new DAG, hence its new source-set distance is zero; use that directly. | AFP lines908–917. Do not assume it had a zero-distance singleton walk in the empty old DAG. |
| C24-117 | Prove parent-walk invariant preservation, separating old paths from paths extended by newly added edges and using current-no-out and distance-boundedness. | p.285 asserted invariant and p.289 omitted proofs; `invar_parents_shortest_paths_holds_upd1`, lines1032–1212. |
| C24-118 | Assemble whole-run preservation of all three main invariants and their auxiliary dependencies under the terminating-domain predicate. | pp.285–290; source `invar_dist_holds`, `invar_parents_shortest_paths_holds`, lines969–980,1219–1232. Actual source has more named auxiliary predicates than the prose's count of four. |
| C24-119 | Primary termination measure is `card (vertices input \ (visited∪current))`. | p.289; `call_1_measure_1`, lines220–222. A vertex is discovered before it becomes visited. |
| C24-120 | Secondary termination measure is `card current`, and the order is lexicographic. | pp.289–290; `call_1_measure_2`, `BFS_term_rel`, lines224–229. |
| C24-121 | A nonempty new frontier strictly decreases the first measure; an empty new frontier leaves it equal and reduces the positive old-current cardinality to zero. | p.290; `call_1_terminates`, lines1291–1364. Check finiteness, subset and canonical-empty/selection laws before converting representations to cardinalities. |
| C24-122 | Prove termination from the source package WF, Subsets, current-no-out and global BFS assumptions; weaker sufficient packages may be separate theorems. | p.290; `BFS_terminates`, lines1374–1383. No fuel bound is given by the book. |
| C24-123 | All three main invariants and the recovered auxiliary invariants hold initially; the initial run terminates. | p.290; `initial_state_props`, lines1394–1442. Source nonemptiness and incident membership establish the zero-distance initial layer. |
| C24-124 | Every terminating BFS result has empty current; visited then contains all input vertices reachable from any source. | pp.285,290; `ret1_holds`, `BFS_correct_1_ret_1`. Phrase the coverage in terms of visited; the DAG may omit source vertices. |
| C24-125 | **Theorem24.7:** if `u∈U` and `t` is not in final visited, there is no input walk from `u` to `t`. | p.290; `BFS_correct_1`, lines1444–1448. Carries `BFS_axiom` through the context. |
| C24-126 | **Theorem24.8:** for a final visited vertex `t∉U`, input and final DAG source-set distances are equal. | p.290; `BFS_correct_2`, lines1450–1455. Do not remove the non-source exception or replace set-distance with each root's distance. |
| C24-127 | **Theorem24.9:** every final DAG walk from any source `u∈U` to `v` has edge length `D input U v`. | p.290; `BFS_correct_3`, lines1457–1462. Consequently such a walk is shortest from that particular source too, because `D≤d(u,v)≤its length`. |
| C24-128 | Final visited membership iff reachability from at least one source, with a returned shortest witness for each reachable non-source vertex. | pp.280–281,285 coverage/shortest-path promises. Combine C24-105,125–127 and finite-distance attainment; do not assert all original roots remain incident in the DAG. |
| C24-129 | The output is a directed acyclic graph: no nonempty closed edge walk. | pp.281–285 use of “DAG” is a mathematical property, not merely a field name. Prove strictly increasing finite layer rank along every added edge, or derive it from reachable output vertices and the shortest-walk invariant. No active acyclicity theorem is supplied by the companion. |
| C24-130 | Preserve the multiple-parent behavior and demonstrate that the output need not be a unique-walk forest. | pp.281–285. Diamond `s→a,s→b,a→t,b→t` retains both length-two walks. A predecessor map choosing only one is not the source output. |
| C24-131 | Correct the per-root distance-preservation prose with the actual set-distance theorem and a checked counterexample to the unrestricted version. | p.285; example below keeps both roots incident in the output, yet loses one root's longer route. Conditional per-root preservation for an existing output walk follows from C24-127. |
| C24-132 | Correct the assertion that the DAG itself contains every reachable vertex: visited does; all reachable non-source vertices appear, but a source without a forward edge can be absent. | p.285 and Theorem24.8's exclusion. Input self-loop at a sole source yields final visited singleton and empty output graph. |
| C24-133 | Correct the pseudocode loop guard to current nonempty and retain a counterexample showing the printed visited guard does not terminate. | p.282 versus p.283 and source lines63–75. Do not formalize the erroneous guard as a terminating BFS. |
| C24-134 | Repair `DAG`/`parents` field inconsistency in displayed update and initialization, keeping an explicit reconstruction mapping. | pp.282–283,290; source consistently declares/updates `parents`. This is a syntax/type correction, not a semantic choice of another algorithm. |
| C24-135 | Implement `expandTree` and `nextFrontier` with finite enumeration/folds and prove all four Figure24.6 laws, including preservation of every eligible multiple-parent edge. | pp.282–284 describe nested loops abstracted by these assumptions. Source locale axioms alone are not an executable realization. Share finite-fold infrastructure with AppendixC where suitable. |
| C24-136 | Instantiate the complete BFS with concrete containers, prove erasure/correspondence to the specified state steps, and exercise branching, multiple roots, cycles, unreachable targets and missing-output-root cases. | §24.2 and whole-book executable scope. No Lean implementation or acceptance is claimed by this inventory. |
| C24-137 | Keep source resource scope exact: there is no specified DFS/BFS call-cost recurrence or proved `O(V+E)` theorem in this chapter. | pp.269,280,283,290–292. Preserve C24-012/013's actual container claims; if additional measured operations are supplied, state their own tariff, repeated lookups/differences, and concrete helper costs. |
| C24-138 | Record graph-model and proof-method alternatives as contextual analysis while retaining the precise mathematical consequences used above. | §24.3 pp.290–292. Self-loops refute a literal reading that every vertex connects to a *different* vertex; model limitation is lack of isolated vertices. There is no demand here to formalize all cited matching/flow/refinement systems. |

## Source defects and required checked dispositions

1. **Discovery versus completion, p.274.** The prose treats seen as the
   collection of completed vertices and says popping inserts the vertex.
   The displayed code and `DFS.thy` insert on discovery/push. For input
   `s→u`, just after the first push, `seen={s,u}` and stack is `[u,s]`,
   although neither has been popped. At the later pop, seen is unchanged.
   Formalize the code's actual transition and preserve this trace.

2. **DFS pop-proof suffix, pp.277–278.** After decomposing a distinct walk
   as `p₁ ++ [v₂] ++ p₂`, the nonempty suffix begins at a seen neighbor of
   the popped vertex. Apply SeenCut to **`p₂`**, not merely to `v₂::p₂`:
   the latter intersects the old stack at `v₂` trivially and proves no
   surviving intersection. Distinctness of the original walk establishes
   `v₂∉set p₂`; stack distinctness alone does not. The active proof at
   `DFS.thy` lines545–560 takes the correct suffix and uses `distinct p`,
   despite a similar inaccurate explanatory comment.

3. **Infimum versus argmin, p.281.** The printed definition has result
   type `ENat`; the prose describes a path witness. Retain the infimum
   value and prove witness attainment separately. No arbitrary default
   path is returned for an unreachable pair.

4. **Nonterminating pseudocode guard, p.282.** Take the graph `{(s,s)}`
   and initial current `{s}`. After the first loop body, current is empty
   and visited is `{s}`. Subsequent bodies change neither, so the printed
   `while visited != empty` continues forever. The actual recursive
   definition and AFP use **current** as the guard. Correct that guard,
   and record/check the self-loop state counterexample. The pseudocode
   also assumes initial empty accumulator/output values implicitly; make
   those explicit in an executable nested-loop realization.

5. **Output field name, pp.282–283 and290.** The book declares `DAG`,
   reads `DAG`, but updates/initializes `parents`. AFP declares and uses
   `parents` consistently. A Lean record must choose one field and prove
   its reconstruction correspondence; this is not a reason to introduce
   two independent output graphs.

6. **Per-root distance assertion, p.285.** Let all four vertices be
   distinct, `U={a,b}`, and `E={(a,x),(x,v),(b,v)}`. First-layer expansion
   adds `(a,x)` and `(b,v)`. The next layer is `{x,v}`; `(x,v)` is excluded
   because `v` is already discovered. Final `H={(a,x),(b,v)}` contains
   both roots as incident vertices, yet `d E a v=2` and `d H a v=∞`.
   The actual theorem is `D E U v=D H U v=1`. Preserve both the corrected
   set-distance result and a small Lean counterexample to the broader
   printed claim. The later formal statements and AFP are already correct.

7. **Source predecessor omitted from the proof, p.288.** Take
   `E={(s,t)}`, `U={s}`, initial output `H₀=∅`, and first new vertex `t`.
   Its predecessor is `s`. Equation24.2 gives `1=0+1`, but the printed
   Equation24.3 would equate this with `D H₀ U s+1=∞`. Equation24.4 also
   cannot identify old and new distances to `s`: the new edge first makes
   `s` incident. AFP `invar_dist_holds_upd1_new` explicitly splits
   `v′∈U` at lines908–917 and proves zero distance in the **new** DAG.
   Keep that branch and the counterexample; the lemma itself remains true.
   The surrounding prose also drops `U` from several applications of the
   ternary function `D`; restore it in a typed statement. The concluding
   sandwich uses old **equality**, not just the three displayed lower
   bounds.

8. **DAG vertex coverage and self-loop wording, pp.285,290.** With
   `E={(s,s)}`, `U={s}`, BFS finishes with visited `{s}` and `H=∅`.
   Thus the DAG does not contain every reachable root. The non-source
   restriction in Theorem24.8 is substantive. The graph model also allows
   a single vertex with a self-loop, so it excludes isolated vertices,
   not all singleton vertex sets or all edges to oneself.

9. **Unprinted support and inactive forest draft.** The book summarizes
   auxiliary invariants without listing them all. The inspected source
   additionally has complete-layer, earlier-layer, processed-neighbor,
   finite-discovered-distance and current-no-out predicates. Retain them
   or a proved sufficient replacement. Conversely, do not promote the
   commented forest draft in `Dist.thy` to established mathematics.
   Its `forest_insert` statement even lacks a premise preventing a new
   self-loop: inserting `(a,a)` into the empty graph gives different
   walks `[a]` and `[a,a]`. This is an inactive draft defect, not a hole
   in the active BFS theorems or a new whole-forest chapter obligation.

The small graph examples were independently evaluated with a finite
Python set/BFS model during source preparation. Those evaluations are
discovery checks only; they are **not** Lean proofs and confer no formal
acceptance. Future correction modules should state/check the meaningful
counterexamples alongside the corrected source-facing theorems.

## Handoff and completion boundary

Formal implementation should follow the already accepted Chapter6 graph
container interfaces, reuse Mathlib directed-relation/path/`ENat` facts
through checked source-model bridges, and retain the exact DFS push/pop
and BFS layer transitions. A map or search with the same final reachable
set does not establish these recurrences, path-return behavior or the DAG
edge contract. Concrete `expandTree`/`nextFrontier` implementations must
discharge the locale assumptions before the chapter is called executable.

The mathematical graph theory permits infinite graphs; termination claims
are restricted to the stated finite representations. Any future measured
extension should separately name selection, lookup, set difference,
union, iteration and allocation observations. Recomputing a difference or
projecting a result from another search algorithm is not free merely
because a value-level correspondence is available.

Chapter24 can close only after every applicable row has an implementation
or theorem/reuse witness, exact source reconstruction references and
visible defect dispositions, the concrete realizations satisfy their
contracts, and conaled's candidate validation plus both independent
review axes have succeeded. This inventory changes none of those states.
