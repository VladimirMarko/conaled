import Applications.Prim.ArrayOptimality
import Applications.Prim.Observation

/-! Coherent two-pass matrices represent an explicit bidirected graph. The actual
array realization and its cost retain their original matrix problem as index. -/
set_option autoImplicit false
set_option warningAsError true

namespace Prim.ArrayObservation
open Kruskal Prim.Array Prim.ArrayOptimality
variable {n : Nat}

def bidirectedGraph (es : List (Prim.Weights.FEdge n Int)) : Graph :=
  (labels n, es.map (fun e => (label e.1, label e.2.1, e.2.2)) ++
    es.map (fun e => (label e.2.1, label e.1, e.2.2)))

theorem bidirected_cell (es : List (Prim.Weights.FEdge n Int)) (u v : Fin n) (w : Int) :
    (label u, label v, w) ∈ edges (bidirectedGraph es) ↔
      (u, v, w) ∈ es ∨ (v, u, w) ∈ es := by
  simp only [bidirectedGraph, edges, List.mem_append, List.mem_map,
    Prod.exists, Prod.mk.injEq, label_eq_iff]
  simp

theorem bidirected_endpoints (es : List (Prim.Weights.FEdge n Int)) :
    EndpointsIn (nodes (bidirectedGraph es)) (edges (bidirectedGraph es)) := by
  intro e he
  rcases List.mem_append.mp he with he | he <;>
    obtain ⟨⟨u, v, w⟩, _, rfl⟩ := List.mem_map.mp he
  · exact ⟨mem_labels u, mem_labels v⟩
  · exact ⟨mem_labels v, mem_labels u⟩

theorem constructed_rep {es : List (Prim.Weights.FEdge n Int)}
    (hc : Prim.Weights.Coherent es) :
    MatrixRep (bidirectedGraph es) (Prim.Weights.view (Prim.Weights.weightsP es)) :=
  ⟨rfl, bidirected_endpoints es,
    fun u v w => (Prim.Weights.undirected_iff hc u v w).trans (bidirected_cell es u v w).symm,
    Prim.Weights.undirected_symmetric hc⟩

structure Problem (n : Nat) where
  graph : Graph
  weights : Weights n
  root : Fin n
  representation : MatrixRep graph weights
  connected : ConnectedGraph graph

def Problem.treeProblem (i : Problem n) : MinimumSpanningForest.TreeProblem :=
  ⟨i.graph, by rw [i.representation.vertices]; exact labels_nodup n,
    by rw [i.representation.vertices]; exact List.ne_nil_of_mem (mem_labels i.root),
    i.representation.endpoints, i.connected⟩

def selectedTree (i : Problem n) : Tree := (prim2 i.weights i.root).getD ([], [])

theorem selectedTree_result (i : Problem n) :
    prim2 i.weights i.root = some (selectedTree i) := by
  obtain ⟨t, ht, _⟩ := prim2_exists_minimum i.representation i.connected i.root
  simp [selectedTree, ht]

theorem selectedTree_minimum (i : Problem n) : MinimumSpanningTree i.graph (selectedTree i) :=
  prim2_minimum i.representation i.connected (selectedTree_result i)

def treeSquare : Relational.RelSquare (Optimization.inputRep (Problem n))
    (Optimization.membershipRep (I := Problem n) (id : Tree → Tree)) :=
  Optimization.selectionSquare (fun i : Problem n => {t | SpanningTree i.graph t})
    (fun _ => costMCST) id selectedTree selectedTree_minimum

def costSquare : Relational.RelSquare (Optimization.inputRep (Problem n))
    (Optimization.membershipRep (I := Problem n) (id : Int → Int)) :=
  Relational.compose (Optimization.observationSquare costMCST) treeSquare

theorem cost_attained (i : Problem n) :
    ∃ t, MinimumSpanningTree i.graph t ∧ costMCST t = (costSquare.impl i).2 :=
  (costSquare.preserves (r := i) (s := i) rfl).2

theorem cost_result (i : Problem n) :
    (prim2 i.weights i.root).map costMCST = some (costSquare.impl i).2 := by
  rw [selectedTree_result]
  rfl

theorem prim_cost_agreement (i : Problem n) :
    (costSquare.impl i).2 = (Prim.Observation.costSquare.impl i.treeProblem).2 :=
  minimum_cost_eq (selectedTree_minimum i) (Prim.Observation.selectedTree_minimum i.treeProblem)

theorem kruskal_cost_agreement (i : Problem n) :
    (costSquare.impl i).2 = (MinimumSpanningForest.treeCostSquare.impl i.treeProblem).2 :=
  (prim_cost_agreement i).trans (Prim.Observation.kruskal_cost_agreement i.treeProblem)

/-- Coherence is a representation condition; connectivity supplies feasibility. -/
structure EdgeProblem (n : Nat) where
  input : List (Prim.Weights.FEdge n Int)
  root : Fin n
  coherent : Prim.Weights.Coherent input
  connected : ConnectedGraph (bidirectedGraph input)

def EdgeProblem.problem (i : EdgeProblem n) : Problem n :=
  ⟨bidirectedGraph i.input, Prim.Weights.view (Prim.Weights.weightsP i.input),
    i.root, constructed_rep i.coherent, i.connected⟩

/-- The builder is executed inside the realization; the original edge input is retained. -/
def constructedTreeSquare : Relational.RelSquare (Optimization.inputRep (EdgeProblem n))
    (Optimization.membershipRep (I := EdgeProblem n) (id : Tree → Tree)) :=
  Optimization.selectionSquare (fun i : EdgeProblem n => {t | SpanningTree (bidirectedGraph i.input) t})
    (fun _ => costMCST) id (fun i => selectedTree i.problem)
    (fun i => selectedTree_minimum i.problem)

def constructedCostSquare : Relational.RelSquare (Optimization.inputRep (EdgeProblem n))
    (Optimization.membershipRep (I := EdgeProblem n) (id : Int → Int)) :=
  Relational.compose (Optimization.observationSquare costMCST) constructedTreeSquare

theorem constructed_result (i : EdgeProblem n) :
    prim2 (Prim.Weights.view (Prim.Weights.weightsP i.input)) i.root =
      some (constructedTreeSquare.impl i).2 := selectedTree_result i.problem

theorem constructed_cost_attained (i : EdgeProblem n) :
    ∃ t, MinimumSpanningTree (bidirectedGraph i.input) t ∧
      costMCST t = (constructedCostSquare.impl i).2 :=
  (constructedCostSquare.preserves (r := i) (s := i) rfl).2

end Prim.ArrayObservation
