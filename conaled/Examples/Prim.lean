import Applications.Prim.Observation

/-! Exact growing-tree traces and applications of global optimum and cost consumers. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.Prim
open Kruskal Prim.Core Prim.Exchange Prim.Correctness

example :
    gstepP (([1], []), [(2,3,1),(1,2,2)]) = some (([2,1],[(1,2,2)]),[(2,3,1)]) ∧
    gstepP (([2,1],[(1,2,2)]),[(2,3,1)]) = some (([3,2,1],[(2,3,1),(1,2,2)]),[]) :=
  kept_edge_becomes_safe

theorem retained_first_safe :
    FirstSafe (([1], []), [(2,3,1),(1,2,2)]) (([2,1],[(1,2,2)]),[(2,3,1)]) :=
  (gstepP_firstSafe _ _).mp kept_edge_becomes_safe.1

theorem retained_source_run :
    SourceRun 2 (([1], []), [(2,3,1),(1,2,2)]) (([3,2,1],[(2,3,1),(1,2,2)]),[]) :=
  (applyP_source_iff _ _ _).mp (by decide +kernel)

def signedGraph : Graph :=
  ([10,-4,90],[(90,90,-100),(-4,90,-7),(10,-4,2),(10,-4,2),(10,90,9)])

theorem signed_valid : (nodes signedGraph).Nodup ∧ EndpointsIn (nodes signedGraph) (edges signedGraph) := by
  constructor
  · decide
  · simp [EndpointsIn, signedGraph, nodes, edges, source, target]

theorem signed_result :
    prim signedGraph = some ([90,-4,10],[(-4,90,-7),(10,-4,2)]) := by
  simp +decide [signedGraph, prim, primState, startP, untilP, visited, gstepP, addP, nodes, edges, target, weight, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, List.mergeSort]

theorem signed_minimum : SourceMinimum signedGraph ([90,-4,10],[(-4,90,-7),(10,-4,2)]) :=
  prim_minimum signed_valid.1 signed_valid.2 signed_result

def signedProblem : MinimumSpanningForest.TreeProblem :=
  ⟨signedGraph, signed_valid.1, by decide +kernel, signed_valid.2,
    (prim_defined_iff_connected signed_valid.1 (by decide +kernel) signed_valid.2).mp ⟨_, signed_result⟩⟩

theorem signed_normalization :
    Prim.Observation.selectedRawTree signedProblem = ([90,-4,10],[(-4,90,-7),(10,-4,2)]) ∧
    Prim.Observation.selectedTree signedProblem = ([10,-4,90],[(-4,90,-7),(10,-4,2)]) ∧
    (Prim.Observation.costSquare.impl signedProblem).2 = -5 := by
  have he : Prim.Observation.selectedRawTree signedProblem =
      ([90,-4,10],[(-4,90,-7),(10,-4,2)]) := by
    change (prim signedGraph).getD ([], []) = _
    rw [signed_result]
    rfl
  refine ⟨he, ?_, ?_⟩
  · change (nodes signedGraph, edges (Prim.Observation.selectedRawTree signedProblem)) = _
    rw [he]
    rfl
  · change costMCST (normalize signedGraph (Prim.Observation.selectedRawTree signedProblem)) = -5
    rw [he]
    rfl

theorem signed_optimum : MinimumSpanningTree signedGraph (Prim.Observation.treeSquare.impl signedProblem).2 :=
  Prim.Observation.selectedTree_minimum signedProblem

theorem signed_kruskal_exact :
    ForestKruskalSource.kruskal1 signedGraph = some ([10,-4,90],[(10,-4,2),(-4,90,-7)]) := by
  simp +decide [signedGraph, ForestKruskalSource.kruskal1, ForestKruskalSource.startSorted,
    ForestKruskalSource.apply, ForestKruskalSource.gstep, ForestKruskalSource.find,
    ForestKruskalSource.merge, ForestKruskalSource.extract, nodes, edges, source, target,
    weight, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, List.mergeSort]

theorem signed_cost_result : Prim.Observation.costResult signedGraph = some (-5) := by
  have he := Prim.Observation.costResult_exact signedProblem
  rw [signed_normalization.2.2] at he
  exact he

theorem signed_kruskal_agreement :
    (Prim.Observation.costSquare.impl signedProblem).2 =
      (MinimumSpanningForest.treeCostSquare.impl signedProblem).2 :=
  Prim.Observation.kruskal_cost_agreement signedProblem

theorem signed_forest_agreement :
    (Prim.Observation.costSquare.impl signedProblem).2 =
      (MinimumSpanningForest.costSquare.impl signedProblem.forest).2 :=
  Prim.Observation.forest_cost_agreement signedProblem

theorem signed_residual :
    primState signedGraph = some (([90,-4,10],[(-4,90,-7),(10,-4,2)]),
      [(90,90,-100),(10,-4,2),(10,90,9)]) := by
  simp +decide [signedGraph, primState, startP, untilP, visited, gstepP, addP, nodes, edges, target, weight, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, List.mergeSort]

theorem signed_first_hit :
    ∃ s, startP signedGraph = some s ∧
      Iteration.UntilSpec (doneP 3) stepTotal s
        (([90,-4,10],[(-4,90,-7),(10,-4,2)]),[(90,90,-100),(10,-4,2),(10,90,9)]) :=
  primState_first_hit _ _ signed_residual

def tiedGraph : Graph := ([1,2,3],[(2,3,0),(1,3,0),(1,2,0)])

theorem tied_valid : (nodes tiedGraph).Nodup ∧ EndpointsIn (nodes tiedGraph) (edges tiedGraph) := by
  constructor
  · decide
  · simp [EndpointsIn, tiedGraph, nodes, edges, source, target]

theorem tied_exact :
    primState tiedGraph = some (([2,3,1],[(2,3,0),(1,3,0)]),[(1,2,0)]) ∧
    ForestKruskalSource.kruskal1 tiedGraph = some ([1,2,3],[(1,3,0),(2,3,0)]) := by
  simp +decide [tiedGraph, primState, startP, untilP, visited, gstepP, addP, nodes, edges, source, target, weight, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, List.mergeSort,
    ForestKruskalSource.kruskal1, ForestKruskalSource.startSorted, ForestKruskalSource.apply,
    ForestKruskalSource.gstep, ForestKruskalSource.find, ForestKruskalSource.merge, ForestKruskalSource.extract]

def tiedProblem : MinimumSpanningForest.TreeProblem :=
  ⟨tiedGraph, tied_valid.1, by decide +kernel, tied_valid.2,
    (prim_defined_iff_connected tied_valid.1 (by decide +kernel) tied_valid.2).mp
      ⟨([2,3,1],[(2,3,0),(1,3,0)]), by rw [prim, tied_exact.1]; rfl⟩⟩

theorem tied_witness_order_differs :
    edges (Prim.Observation.selectedRawTree tiedProblem) ≠
      edges (MinimumSpanningForest.selectedRawTree tiedProblem) := by
  simp [Prim.Observation.selectedRawTree, MinimumSpanningForest.selectedRawTree, tiedProblem,
    prim, tied_exact, edges]

theorem tied_cost_agreement :
    (Prim.Observation.costSquare.impl tiedProblem).2 =
      (MinimumSpanningForest.treeCostSquare.impl tiedProblem).2 :=
  Prim.Observation.kruskal_cost_agreement tiedProblem

theorem duplicate_branches :
    stepsP (([1],[]),[(1,2,0),(1,2,0)]) =
      [(([2,1],[(1,2,0)]),[(1,2,0)]), (([2,1],[(1,2,0)]),[(1,2,0)])] := by decide +kernel

theorem branch_boundary :
    untilBranches 0 2 [(([1],[]),[(1,2,0)])] = [(([1],[]),[(1,2,0)])] ∧
    branchP 0 [(([1],[]),[(1,2,0)])] = [(([1],[]),[(1,2,0)])] := by simp [untilBranches, branchP, visited, nodes]

theorem branch_fixed :
    spatsP tiedGraph = (startP0 tiedGraph).map (fun s => (branchP 2 [s]).map Prod.fst) :=
  spatsP_fixed tiedGraph

theorem empty_singleton :
    prim ([],[]) = none ∧ spatsP ([],[]) = none ∧
    prim ([-20],[]) = some ([-20],[]) ∧ spatsP ([-20],[]) = some [([-20],[])] :=
  ⟨empty_boundary.1, empty_boundary.2, (singleton_boundary (-20)).1, (singleton_boundary (-20)).2⟩

def disconnected : Graph := ([1,9],[(1,1,-8)])

theorem disconnected_failure : prim disconnected = none ∧ spatsP disconnected = some [] := by decide +kernel

theorem disconnected_not_connected : ¬ ConnectedGraph disconnected := by
  intro hc
  obtain ⟨t, ht, _⟩ := prim_exists_minimum (g := disconnected) (by decide) (by decide)
    (by simp [EndpointsIn, disconnected, nodes, edges, source, target]) hc
  rw [disconnected_failure.1] at ht
  cases ht

theorem raw_boundaries :
    untilP 0 1 (([1],[]),[]) = some (([1],[]),[]) ∧
    untilP 0 2 (([1],[]),[(1,2,0)]) = none ∧
    applyP 0 (([1],[]),[]) = some (([1],[]),[]) ∧
    applyP 1 (([1],[]),[]) = none ∧
    untilP 3 0 (([1],[]),[]) = none := by simp [untilP, applyP, gstepP, visited, nodes]

theorem signed_guarded_fixed : prim signedGraph = prim1 signedGraph := prim_eq_prim1 _

theorem signed_extra_step_fails :
    (startP signedGraph).bind (applyP 3) = none ∧
    (startP signedGraph).bind (applyP 2) = primState signedGraph := by
  simp +decide [signedGraph, applyP, primState, startP, untilP, visited, gstepP, addP, nodes, edges, target, weight, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, List.mergeSort]

end Examples.Prim
