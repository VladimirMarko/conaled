import Applications.Kruskal.ForestObservation

/-! Checked source boundaries, signed disconnected forests, exact tied order,
and consumers of the independent global optimum theorems. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.NestedKruskal
open Kruskal (Graph Tree Edge nodes edges source target weight EndpointsIn)
open ForestKruskalSource
open ForestPartition (chosen)

/-- The source full-state counterexample survives the exact selector bridge. -/
theorem source_state_counterexample :
    apply 2 (startSorted statePropertyGraph) = some statePropertyBefore ∧
    gstep statePropertyBefore = some statePropertyAfter ∧
    statePropertyAfter ∈ AllMinima.minsWith stateCost [statePropertyAfter] ∧
    statePropertyAfter ∉ AllMinima.minsWith stateCost (steps statePropertyBefore) := by
  simpa only [← minima_eq_source] using full_state_property_counterexample

theorem discard_observation (s : State) :
    (stepsDiscard s).map Prod.fst = (steps s).map Prod.fst ∧
    ∀ out ∈ stepsDiscard s, ∃ full ∈ steps s,
      out.1 = full.1 ∧ out.2.Sublist full.2 :=
  ⟨stepsDiscard_same_forests s, fun out h => stepsDiscard_residual_subset s out h⟩

theorem minima_independent (ss : List State) (s : State) :
    s ∈ minima ss ↔ s ∈ ss ∧ ∀ t ∈ ss, stateCost s ≤ stateCost t := by
  rw [minima_mem_iff]
  simp [Optimization.minimizers, isMinOn_iff]

/-- The corrected one-edge operation succeeds on a loop that gstep exhausts. -/
theorem internal_edge_boundary :
    scanStep ([([7],[])], [(7,7,-4)]) = some ([([7],[])], []) ∧
    gstep ([([7],[])], [(7,7,-4)]) = none := by
  simp [scanStep, gstep, find, nodes, source, target]

theorem raw_step_semantics (s out : State) : gstep s = some out ↔ SourceStep s out :=
  gstep_source_iff s out

/-- Source empty and repeated ties retain every minimum occurrence, in order. -/
theorem selector_occurrences :
    AllMinima.minsWith (fun p : String × Int => p.2) [] = [] ∧
    AllMinima.minsWith (fun p : String × Int => p.2)
      [("high", 2), ("a", -1), ("b", -1), ("a", -1), ("zero", 0)] =
      [("a", -1), ("b", -1), ("a", -1)] := by
  simp only [AllMinima.minsWith_eq_filter]
  decide

theorem literal_triangle :
    mcsfLiteral triangle = none ∧ mcsf triangle = some [([1,2,3], [(2,3,2), (1,2,1)])] ∧
    MinimumSpanningForest.Minimum triangle [(2,3,2), (1,2,1)] := by
  refine ⟨literal_mcsf_boundary.1, literal_mcsf_boundary.2, ?_⟩
  have h := MinimumSpanningForest.mcsf_result_minimum (g := triangle) (by decide)
    (by simp [EndpointsIn, triangle, nodes, edges, source, target]) literal_mcsf_boundary.2
  simpa [chosen, edges] using h

theorem empty_optimum :
    kruskal0 ([],[]) = none ∧ kruskal1 ([],[]) = none ∧
    mcsfLiteral ([],[]) = some [] ∧ mcsf ([],[]) = some [] ∧
    MinimumSpanningForest.Minimum ([],[]) [] := by
  exact ⟨empty_boundaries.1, empty_boundaries.2.1, empty_boundaries.2.2.1,
    empty_boundaries.2.2.2, MinimumSpanningForest.mcsf_result_minimum (by decide)
      (by simp [EndpointsIn, edges]) empty_boundaries.2.2.2⟩

theorem singleton_optimum (v : Int) :
    kruskal0 ([v],[]) = some ([v],[]) ∧ kruskal1 ([v],[]) = some ([v],[]) ∧
    Kruskal.MinimumSpanningTree ([v],[]) ([v],[]) :=
  ⟨(singleton_boundaries v).1, (singleton_boundaries v).2,
    (ForestKruskalClient.kruskal1_result_minimum (by simp [nodes]) (by simp [nodes])
      (by simp [EndpointsIn, edges]) (singleton_boundaries v).2).2⟩

theorem isolated_vertices :
    kruskal0 ([1,2],[]) = none ∧ kruskal1 ([1,2],[]) = none ∧
    mcsf ([1,2],[]) = some [([1],[]),([2],[])] ∧
    MinimumSpanningForest.Minimum ([1,2],[]) [] := by
  have h := MinimumSpanningForest.disconnected_boundary
  exact ⟨h.1, h.2.1, h.2.2,
    MinimumSpanningForest.mcsf_result_minimum (by decide)
      (by simp [EndpointsIn, edges]) h.2.2⟩

/-- The isolated vertex 99 must remain, while the negative loop must be excluded. -/
def signedGraph : Graph := ([99,42,7,-3],
  [(-3,-3,-10), (-3,7,5), (-3,7,-2), (-3,7,-2), (7,42,0), (42,-3,4)])
def signedForest : Forest := [([-3,7,42], [(7,42,0),(-3,7,-2)]), ([99],[])]

theorem signed_endpoints : EndpointsIn (nodes signedGraph) (edges signedGraph) := by
  simp [EndpointsIn, signedGraph, nodes, edges, source, target]

theorem signed_actual : mcsf signedGraph = some signedForest := by
  simp +decide [mcsf, start, scan, find, merge, signedGraph, signedForest,
    Kruskal.sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy,
    List.mergeSort, nodes, edges, source, target, weight]

theorem signed_minimum : MinimumSpanningForest.Minimum signedGraph (chosen signedForest) :=
  MinimumSpanningForest.mcsf_result_minimum (by decide) signed_endpoints signed_actual

def signedProblem : MinimumSpanningForest.Problem := ⟨signedGraph, by decide, signed_endpoints⟩

theorem signed_consumer :
    (MinimumSpanningForest.forestSquare.impl signedProblem).1 = signedProblem ∧
    (MinimumSpanningForest.forestSquare.impl signedProblem).2 = [(7,42,0),(-3,7,-2)] ∧
    (MinimumSpanningForest.costSquare.impl signedProblem).2 = -2 := by
  have hout : MinimumSpanningForest.selectedForest signedProblem = signedForest :=
    Option.some.inj ((MinimumSpanningForest.selectedForest_result signedProblem).symm.trans signed_actual)
  refine ⟨rfl, ?_, ?_⟩
  · change chosen (MinimumSpanningForest.selectedForest signedProblem) = _
    rw [hout]; rfl
  · exact (MinimumSpanningForest.selected_cost_eq signedProblem _ signed_minimum).trans rfl

theorem signed_square_preservation :
    ∃ fs, MinimumSpanningForest.Minimum signedGraph fs ∧ MinimumSpanningForest.cost fs = -2 := by
  obtain ⟨fs, hf, hc⟩ := MinimumSpanningForest.selected_cost_attained signedProblem
  exact ⟨fs, hf, hc.trans signed_consumer.2.2⟩

/-- Removing the isolated vertex yields a connected, non-numbered input. -/
def signedConnected : Graph := ([42,7,-3], edges signedGraph)
def signedTree : Tree := ([-3,7,42], [(7,42,0),(-3,7,-2)])

theorem signed_connected_endpoints : EndpointsIn (nodes signedConnected) (edges signedConnected) := by
  simp [EndpointsIn, signedConnected, signedGraph, nodes, edges, source, target]

theorem signed_tree_actual : kruskal1 signedConnected = some signedTree := by
  simp +decide [kruskal1, apply, startSorted, gstep, find, merge, extract,
    signedConnected, signedGraph, signedTree, Kruskal.sortEdges,
    Applications.Sorting.sortOn, Applications.Sorting.sortBy, List.mergeSort,
    nodes, edges, source, target, weight]

theorem normalized_optimum : nodes signedTree ≠ nodes signedConnected ∧
    (nodes signedTree).Perm (nodes signedConnected) ∧
    Kruskal.MinimumSpanningTree signedConnected (nodes signedConnected, edges signedTree) :=
  ⟨by decide, ForestKruskalClient.kruskal1_result_minimum (by decide) (by decide)
    signed_connected_endpoints signed_tree_actual⟩

def signedTreeProblem : MinimumSpanningForest.TreeProblem :=
  ⟨signedConnected, by decide, by decide, signed_connected_endpoints,
    (ForestKruskalClient.kruskal1_defined_iff_connected (by decide) (by decide)
      signed_connected_endpoints).mp ⟨signedTree, signed_tree_actual⟩⟩

theorem signed_tree_consumers :
    MinimumSpanningForest.selectedRawTree signedTreeProblem = signedTree ∧
    MinimumSpanningForest.selectedForest signedTreeProblem.forest = [signedTree] ∧
    (MinimumSpanningForest.treeCostSquare.impl signedTreeProblem).2 = -2 := by
  have ht : MinimumSpanningForest.selectedRawTree signedTreeProblem = signedTree :=
    Option.some.inj ((MinimumSpanningForest.selectedRawTree_result signedTreeProblem).symm.trans signed_tree_actual)
  refine ⟨ht, (MinimumSpanningForest.selected_tree_forest signedTreeProblem).trans (congrArg List.singleton ht), ?_⟩
  change Kruskal.costMCST (nodes signedConnected, edges (MinimumSpanningForest.selectedRawTree signedTreeProblem)) = -2
  rw [ht]; rfl

theorem signed_first_hit : ∃ s,
    Iteration.UntilSpec done (fun x => (gstep x).getD x) (startSorted signedConnected) s ∧
    extract s = some signedTree ∧ apply 2 (startSorted signedConnected) = some s := by
  have h0 : kruskal0 signedConnected = some signedTree :=
    (ForestKruskalClient.kruskal_variants (by decide) (by decide)).trans signed_tree_actual
  exact ForestKruskalClient.kruskal0_first_hit (by decide) (by decide) h0

/-- Equal weights expose the different nested and flat selected-edge orders. -/
def tied : Graph := ([1,2,3,4], [(1,2,1),(3,4,1),(1,3,1),(2,4,1)])
def tiedTree : Tree := ([1,2,3,4], [(1,3,1),(1,2,1),(3,4,1)])

theorem tied_actual :
    apply 3 (startSorted tied) = some ([tiedTree], [(2,4,1)]) ∧
    kruskal1 tied = some tiedTree := by
  simp +decide [apply, startSorted, gstep, find, merge, tied, tiedTree,
    kruskal1, extract, Kruskal.sortEdges, Applications.Sorting.sortOn,
    Applications.Sorting.sortBy, List.mergeSort, nodes, edges, source, target, weight]

theorem tied_minimum : Kruskal.MinimumSpanningTree tied tiedTree :=
  (ForestKruskalClient.kruskal1_result_minimum (by decide) (by decide)
    (by simp [EndpointsIn, tied, nodes, edges, source, target]) tied_actual.2).2

def tiedProblem : Kruskal.Problem :=
  ⟨tied, ⟨by decide, by decide,
    by simp [EndpointsIn, tied, nodes, edges, source, target]⟩,
    (ForestKruskalClient.kruskal1_defined_iff_connected (by decide) (by decide)
      (by simp [EndpointsIn, tied, nodes, edges, source, target])).mp ⟨tiedTree, tied_actual.2⟩⟩

theorem tied_distinct_orders :
    Kruskal.kruskal tied = some ([1,2,3,4], [(1,3,1),(3,4,1),(1,2,1)]) ∧
    edges tiedTree ≠ [(1,3,1),(3,4,1),(1,2,1)] := by
  refine ⟨?_, by decide⟩
  simp +decide [Kruskal.kruskal, Kruskal.kruskalState, Kruskal.applyK, Kruskal.startK,
    Kruskal.gstepK2, Kruskal.selected, tied, Kruskal.sortEdges,
    Applications.Sorting.sortOn, Applications.Sorting.sortBy, List.mergeSort,
    Connectivity.ListPartition.startDS, Connectivity.ListPartition.vertices,
    Connectivity.ListPartition.findDS, Connectivity.ListPartition.unionDS,
    Connectivity.ListPartition.lookupDS, List.lookup, List.range_succ, nodes, edges, source, target, weight]

theorem tied_equal_costs :
    (Kruskal.costSquare.impl tiedProblem).2 = 3 ∧
    (MinimumSpanningForest.treeCostSquare.impl (MinimumSpanningForest.numberedProblem tiedProblem)).2 = 3 := by
  have h : (Kruskal.costSquare.impl tiedProblem).2 = 3 :=
    (Kruskal.selected_cost_eq tiedProblem tiedTree tied_minimum).trans rfl
  exact ⟨h, (MinimumSpanningForest.numbered_cost_agreement tiedProblem).trans h⟩

theorem step_projection (s out : State) (hr : MinimumSpanningForest.Rep [1,2,3,4] s.1)
    (hs : gstep s = some out) :
    ∃ flat, Kruskal.gstepK2 (ForestPartition.project s.1, chosen s.1, s.2) = some flat ∧
      flat.1 = ForestPartition.project out.1 ∧ flat.2.2 = out.2 ∧ (chosen out.1).Perm flat.2.1 :=
  ForestKruskalClient.gstep_selected_projection (MinimumSpanningForest.rep_partition hr) hs

/-- A zero-step tree wrapper ignores unused malformed edges; the scan does not. -/
theorem malformed_endpoints :
    kruskal1 ([7],[(99,99,-1)]) = some ([7],[]) ∧
    mcsf ([7],[(99,99,-1)]) = none ∧
    ¬ EndpointsIn [7] [(99,99,-1)] := by
  refine ⟨by decide, ?_, ?_⟩
  · simp [mcsf, start, scan, find, nodes, edges, source, target, Kruskal.sortEdges,
      Applications.Sorting.sortOn, Applications.Sorting.sortBy]
  · simp [EndpointsIn, source, target]

theorem duplicate_vertices :
    mcsf ([7,7],[]) = some [([7],[]),([7],[])] ∧
    kruskal1 ([7,7],[]) = none ∧ ¬ ([7,7] : List Int).Nodup := by
  simp [mcsf, start, scan, kruskal1, apply, startSorted, gstep, nodes, edges,
    Kruskal.sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy]

/-- Selected textbook Answer 9.4 minimum-tree example; shortest paths are separate. -/
def pathGraph : Graph := ([1,2,3,4], [(1,2,4),(1,3,3),(2,3,2),(2,4,5),(3,4,6)])
def pathTree : Tree := ([1,2,3,4], [(2,4,5),(1,3,3),(2,3,2)])

theorem pathGraph_actual : kruskal1 pathGraph = some pathTree := by
  simp +decide [kruskal1, apply, startSorted, gstep, find, merge, extract,
    pathGraph, pathTree, Kruskal.sortEdges, Applications.Sorting.sortOn,
    Applications.Sorting.sortBy, List.mergeSort, nodes, edges, source, target, weight]

theorem pathTree_minimum : Kruskal.MinimumSpanningTree pathGraph pathTree :=
  (ForestKruskalClient.kruskal1_result_minimum (by decide) (by decide)
    (by simp [EndpointsIn, pathGraph, nodes, edges, source, target]) pathGraph_actual).2

def textbookTriangle : Graph := ([1,2,3], [(1,2,1),(1,3,2),(2,3,10)])
def textbookTriangleTree : Tree := ([1,2,3], [(1,3,2),(1,2,1)])

theorem textbook_triangle_actual : kruskal1 textbookTriangle = some textbookTriangleTree := by
  simp +decide [kruskal1, apply, startSorted, gstep, find, merge, extract,
    textbookTriangle, textbookTriangleTree, Kruskal.sortEdges, Applications.Sorting.sortOn,
    Applications.Sorting.sortBy, List.mergeSort, nodes, edges, source, target, weight]

theorem textbook_triangle_minimum :
    Kruskal.MinimumSpanningTree textbookTriangle textbookTriangleTree :=
  (ForestKruskalClient.kruskal1_result_minimum (by decide) (by decide)
    (by simp [EndpointsIn, textbookTriangle, nodes, edges, source, target]) textbook_triangle_actual).2

/-- Every numbered connected input is a checked specialization of the cost agreement. -/
theorem numbered_consumers (i : Kruskal.Problem) :
    (MinimumSpanningForest.treeCostSquare.impl (MinimumSpanningForest.numberedProblem i)).2 =
      (Kruskal.costSquare.impl i).2 ∧
    (MinimumSpanningForest.costSquare.impl (MinimumSpanningForest.numberedProblem i).forest).2 =
      (Kruskal.costSquare.impl i).2 :=
  ⟨MinimumSpanningForest.numbered_cost_agreement i,
    (MinimumSpanningForest.tree_forest_cost _).symm.trans
      (MinimumSpanningForest.numbered_cost_agreement i)⟩

end Examples.NestedKruskal
