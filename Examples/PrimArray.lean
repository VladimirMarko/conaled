import Applications.Prim.ArrayObservation
import Examples.Dijkstra

/-! Checked source illustrations, overwrite boundaries and actual composed MST clients. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.PrimArray
open Kruskal Prim.Array Prim.ArrayOptimality Prim.ArrayObservation

example : (Prim.Weights.index (1 : Fin 3) (2 : Fin 3)).val = 5 :=
  Prim.Weights.index_value _ _

example : Prim.Weights.weightsP ([] : List (Prim.Weights.FEdge 0 Int)) = #v[] := rfl

example : Prim.Weights.view (Prim.Weights.weightsD ([(0,1,3),(0,1,7)] :
    List (Prim.Weights.FEdge 2 Int))) 0 1 = some 7 ∧
    Prim.Weights.view (Prim.Weights.weightsD ([(0,1,3),(0,1,7)] :
    List (Prim.Weights.FEdge 2 Int))) 1 0 = none := by decide +kernel

example :
    Prim.Weights.view (Prim.Weights.weightsP ([(0,1,3),(1,0,7)] :
      List (Prim.Weights.FEdge 2 Nat))) 0 1 = some 7 ∧
    Prim.Weights.view (Prim.Weights.weightsP ([(0,1,3),(1,0,7)] :
      List (Prim.Weights.FEdge 2 Nat))) 1 0 = some 3 :=
  Prim.Weights.reverse_conflict_counterexample

/-- Interleaving the reverse writes changes the conflicting reverse cell to 7. -/
theorem interleaving_differs :
    let es : List (Prim.Weights.FEdge 2 Int) := [(0,1,3),(1,0,7)]
    Prim.Weights.view (Prim.Weights.weightsP es) 1 0 = some 3 ∧
    Prim.Weights.view (Prim.Weights.weightsD ([(0,1,3),(1,0,3),(1,0,7),(0,1,7)] : List (Prim.Weights.FEdge 2 Int))) 1 0 = some 7 := by
  decide +kernel

def primDiagram : State 8 :=
  ⟨Vector.ofFn (fun v => match v.val with
    | 0 => (0,some 0) | 1 => (0,some 7) | 2 => (0,some 15)
    | 3 => (2,some 11) | 4 => (2,some 4) | 5 => (3,some 2)
    | 6 => (4,some 5) | _ => (7,none)),[5,6,7]⟩

theorem prim_diagram_arrays :
    (List.finRange 8).map (fun v => (parent primDiagram v).val+1)=[1,1,1,3,3,4,5,8] ∧
    (List.finRange 8).map (distance primDiagram)=
      [some 0,some 7,some 15,some 11,some 4,some 2,some 5,none] ∧
    choose primDiagram=some 5 := by decide +kernel

theorem prim_diagram_first : Optimization.FirstMinimum (score primDiagram) primDiagram.fresh 5 :=
  (choose_first _ _).mp prim_diagram_arrays.2.2

def figureEdges : List (Prim.Weights.FEdge 6 Nat) :=
  [(0,1,7),(0,2,10),(1,2,2),(1,3,9),(2,3,11),(2,4,4),
    (2,5,1),(3,0,2),(4,3,1),(5,3,6),(5,4,1)]

theorem figure_matrix : ∀ u v, Prim.Weights.view (Prim.Weights.weightsD figureEdges) u v =
    Examples.Dijkstra.figureWeights u v := by decide +kernel

theorem constructed_figure_shortest (v : Fin 6) :
    Dijkstra.Core.Shortest (Prim.Weights.view (Prim.Weights.weightsD figureEdges)) 0 v
      (Examples.Dijkstra.figureDistance v) := by
  have he := funext (fun u => funext (figure_matrix u))
  rw [he]
  exact Examples.Dijkstra.figure_all_shortest v

def signedEdges : List (Prim.Weights.FEdge 3 Int) :=
  [(2,2,-100),(1,2,-7),(0,1,2),(0,1,2),(0,2,9)]

theorem signed_coherent : Prim.Weights.Coherent signedEdges := by
  simp +decide [Prim.Weights.Coherent]

def signedWeights : Weights 3 := Prim.Weights.view (Prim.Weights.weightsP signedEdges)

theorem signed_result : prim2 signedWeights 1 = some ([1,2,3],[(2,1,2),(2,3,-7)]) := by
  decide +kernel

theorem signed_ordinary_result : Prim.Core.prim (bidirectedGraph signedEdges) =
    some ([3,2,1],[(2,3,-7),(1,2,2)]) := by
  change Prim.Core.prim ([1,2,3], [(3,3,-100),(2,3,-7),(1,2,2),(1,2,2),(1,3,9),
    (3,3,-100),(3,2,-7),(2,1,2),(2,1,2),(3,1,9)]) = _
  simp +decide [Prim.Core.prim, Prim.Core.primState,
    Prim.Core.startP, Prim.Core.untilP, Prim.Core.visited, Prim.Core.gstepP, Prim.Core.addP,
    nodes, edges, target, weight, sortEdges, Applications.Sorting.sortOn,
    Applications.Sorting.sortBy, List.mergeSort]

theorem signed_connected : ConnectedGraph (bidirectedGraph signedEdges) :=
  (Prim.Correctness.prim_defined_iff_connected (g := bidirectedGraph signedEdges) (labels_nodup 3)
    (List.ne_nil_of_mem (mem_labels (0 : Fin 3))) (bidirected_endpoints signedEdges)).mp
    ⟨_, signed_ordinary_result⟩

def signedProblem : EdgeProblem 3 := ⟨signedEdges, 1, signed_coherent, signed_connected⟩

theorem signed_minimum :
    MinimumSpanningTree (bidirectedGraph signedEdges) ([1,2,3],[(2,1,2),(2,3,-7)]) :=
  prim2_minimum (constructed_rep signed_coherent) signed_connected signed_result

theorem signed_consumer : (constructedTreeSquare.impl signedProblem).2 =
    ([1,2,3],[(2,1,2),(2,3,-7)]) ∧ (constructedCostSquare.impl signedProblem).2 = -5 := by
  have he : selectedTree signedProblem.problem = ([1,2,3],[(2,1,2),(2,3,-7)]) := by
    change (prim2 signedWeights 1).getD ([], []) = _
    rw [signed_result]
    rfl
  exact ⟨he, congrArg costMCST he⟩

theorem signed_cost_attained : ∃ t, MinimumSpanningTree (bidirectedGraph signedEdges) t ∧
    costMCST t = -5 := by
  have he := constructed_cost_attained signedProblem
  rw [signed_consumer.2] at he
  exact he

theorem signed_algorithms_agree :
    (costSquare.impl signedProblem.problem).2 =
      (Prim.Observation.costSquare.impl signedProblem.problem.treeProblem).2 ∧
    (costSquare.impl signedProblem.problem).2 =
      (MinimumSpanningForest.treeCostSquare.impl signedProblem.problem.treeProblem).2 :=
  ⟨prim_cost_agreement _, kruskal_cost_agreement _⟩

/-- Equal finite labels select by rank, even when fresh order is reversed. -/
def tiedState : State 3 := ⟨Vector.ofFn (fun _ => (2,some (-4))),[2,1,0]⟩
example : choose tiedState = some 0 := by decide +kernel
example : Optimization.FirstMinimum (score tiedState) tiedState.fresh 0 :=
  (choose_first _ _).mp (by decide +kernel)
example : better ((0 : Fin 3),some (-4)) (2,some (-4)) = (0,some (-4)) :=
  better_tie _ _ rfl

/-- This asymmetric column differs from its row and from an accumulated distance. -/
def asymmetric : Weights 3 := fun u v => if u=2 ∧ v=1 then some (-8) else some 9
example : distance (update asymmetric tiedState 1) 2 = some (-8) ∧
    parent (update asymmetric tiedState 1) 2 = 1 := by decide +kernel

example (wa : Weights 1) : prim2 wa 0 = some ([1],[]) := singleton_result wa
example (wa : Weights 3) : run wa 0 tiedState = some tiedState := run_zero _ _
example : step signedWeights ⟨(start (1 : Fin 3)).links, []⟩ = none := by decide +kernel

example : (prim2State signedWeights 1).map (fun s => s.fresh) = some [0] ∧
    (run signedWeights 3 (start 1)).map (fun s => s.fresh) = some [] ∧
    (prim2State signedWeights 1).map (fun s => s.links) =
      (run signedWeights 3 (start 1)).map (fun s => s.links) ∧
    (run signedWeights 3 (start 1)).bind (extractP 1) = prim2 signedWeights 1 := by decide +kernel

theorem signed_pending_contract :
    ∃ before out, run signedWeights 3 (start 1) = some out ∧
      run signedWeights 2 (start 1) = some before ∧ before.fresh.length=1 ∧ before.links=out.links := by
  obtain ⟨out, _, hr, _, _, _⟩ := full_run_minimum (constructed_rep signed_coherent) signed_connected (1 : Fin 3)
  obtain ⟨before, hb, hf, hl⟩ := final_pending_link hr
  exact ⟨before, out, hr, hb, hf, hl⟩

/-- The state loop can finish while total extraction still fails at an infinite entry. -/
example : (run (fun _ _ : Fin 2 => none) 2 (start 0)).isSome = true ∧
    prim2 (fun _ _ : Fin 2 => none) 0 = none ∧
    edgesFor 0 (start (0 : Fin 2)) [0,1] = [] ∧
    extractP 0 (start (0 : Fin 2)) = none := by decide +kernel

def tiedEdges : List (Prim.Weights.FEdge 3 Int) := [(1,2,0),(0,2,0),(0,1,0)]

theorem tied_coherent : Prim.Weights.Coherent tiedEdges := by
  simp +decide [Prim.Weights.Coherent]

theorem tied_array_result : prim2 (Prim.Weights.view (Prim.Weights.weightsP tiedEdges)) 0 =
    some ([1,2,3],[(1,2,0),(1,3,0)]) := by decide +kernel

theorem tied_ordinary_result : Prim.Core.prim (bidirectedGraph tiedEdges) =
    some ([2,3,1],[(2,3,0),(1,3,0)]) := by
  change Prim.Core.prim ([1,2,3],[(2,3,0),(1,3,0),(1,2,0),(3,2,0),(3,1,0),(2,1,0)]) = _
  simp +decide [Prim.Core.prim, Prim.Core.primState, Prim.Core.startP, Prim.Core.untilP,
    Prim.Core.visited, Prim.Core.gstepP, Prim.Core.addP, nodes, edges, target, weight,
    sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, List.mergeSort]

theorem tied_kruskal_result : ForestKruskalSource.kruskal1 (bidirectedGraph tiedEdges) =
    some ([1,2,3],[(1,3,0),(2,3,0)]) := by
  change ForestKruskalSource.kruskal1
    ([1,2,3],[(2,3,0),(1,3,0),(1,2,0),(3,2,0),(3,1,0),(2,1,0)]) = _
  simp +decide [ForestKruskalSource.kruskal1, ForestKruskalSource.startSorted,
    ForestKruskalSource.apply, ForestKruskalSource.gstep, ForestKruskalSource.find,
    ForestKruskalSource.merge, ForestKruskalSource.extract, nodes, edges, source, target,
    weight, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, List.mergeSort]

def tiedProblem : EdgeProblem 3 :=
  ⟨tiedEdges, 0, tied_coherent,
    (Prim.Correctness.prim_defined_iff_connected (g := bidirectedGraph tiedEdges)
      (labels_nodup 3) (List.ne_nil_of_mem (mem_labels (0 : Fin 3))) (bidirected_endpoints tiedEdges)).mp
      ⟨_, tied_ordinary_result⟩⟩

theorem tied_all_minimum :
    MinimumSpanningTree (bidirectedGraph tiedEdges) (selectedTree tiedProblem.problem) ∧
    MinimumSpanningTree (bidirectedGraph tiedEdges)
      (Prim.Observation.selectedTree tiedProblem.problem.treeProblem) ∧
    MinimumSpanningTree (bidirectedGraph tiedEdges)
      (MinimumSpanningForest.selectedTree tiedProblem.problem.treeProblem) :=
  ⟨selectedTree_minimum _, Prim.Observation.selectedTree_minimum _,
    MinimumSpanningForest.selectedTree_minimum _⟩

theorem tied_costs :
    (constructedCostSquare.impl tiedProblem).2 = 0 ∧
    (Prim.Observation.costSquare.impl tiedProblem.problem.treeProblem).2 = 0 ∧
    (MinimumSpanningForest.treeCostSquare.impl tiedProblem.problem.treeProblem).2 = 0 := by
  have he : (costSquare.impl tiedProblem.problem).2 = 0 := by
    change costMCST ((prim2 (Prim.Weights.view (Prim.Weights.weightsP tiedEdges)) 0).getD ([], [])) = 0
    rw [tied_array_result]
    rfl
  exact ⟨he, (prim_cost_agreement _).symm.trans he, (kruskal_cost_agreement _).symm.trans he⟩

/-- The array includes an edge absent from BOTH other tied optimum witnesses. -/
theorem tied_edge_sets_differ :
    (1,2,0) ∈ edges (selectedTree tiedProblem.problem) ∧
    (1,2,0) ∉ edges (Prim.Observation.selectedTree tiedProblem.problem.treeProblem) ∧
    (1,2,0) ∉ edges (MinimumSpanningForest.selectedTree tiedProblem.problem.treeProblem) := by
  change (1,2,0) ∈ edges ((prim2 (Prim.Weights.view (Prim.Weights.weightsP tiedEdges)) 0).getD ([], [])) ∧
    (1,2,0) ∉ edges ((Prim.Core.prim (bidirectedGraph tiedEdges)).getD ([], [])) ∧
    (1,2,0) ∉ edges ((ForestKruskalSource.kruskal1 (bidirectedGraph tiedEdges)).getD ([], []))
  rw [tied_array_result, tied_ordinary_result, tied_kruskal_result]
  decide

example : Prim.Weights.Coherent ([(0,1,-2),(1,0,-2),(0,1,-2)] :
    List (Prim.Weights.FEdge 2 Int)) := by simp +decide [Prim.Weights.Coherent]

example : MatrixRep (bidirectedGraph ([(0,1,-2),(1,0,-2),(0,1,-2)] :
    List (Prim.Weights.FEdge 2 Int)))
      (Prim.Weights.view (Prim.Weights.weightsP (n := 2) [(0,1,-2),(1,0,-2),(0,1,-2)])) :=
  constructed_rep (by simp +decide [Prim.Weights.Coherent])

end Examples.PrimArray
