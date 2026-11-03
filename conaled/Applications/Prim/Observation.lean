import Applications.Prim.Correctness
import Applications.Kruskal.ForestObservation

/-! Normalized Prim trees and attained costs on the existing arbitrary-label tree
problem. Raw vertex discovery order is retained until the explicit observation. -/
set_option autoImplicit false
set_option warningAsError true
namespace Prim.Observation
open Kruskal Prim.Core Prim.Correctness
open MinimumSpanningForest (TreeProblem)

/-- The default is unreachable on the shared connected, nonempty valid domain. -/
def selectedRawTree (i : TreeProblem) : Tree := (prim i.val).getD ([], [])

theorem selectedRawTree_result (i : TreeProblem) : prim i.val = some (selectedRawTree i) := by
  obtain ⟨t, ht, _⟩ := prim_exists_minimum i.property.1 i.property.2.1
    i.property.2.2.1 i.property.2.2.2
  simp [selectedRawTree, ht]

theorem selectedRawTree_minimum (i : TreeProblem) : SourceMinimum i.val (selectedRawTree i) :=
  prim_minimum i.property.1 i.property.2.2.1 (selectedRawTree_result i)

def selectedTree (i : TreeProblem) : Tree := normalize i.val (selectedRawTree i)

theorem selectedTree_minimum (i : TreeProblem) : MinimumSpanningTree i.val (selectedTree i) :=
  (selectedRawTree_minimum i).2

theorem selectedRawTree_vertices (i : TreeProblem) :
    (nodes (selectedRawTree i)).Perm (nodes i.val) := (selectedRawTree_minimum i).1

def treeSquare : Relational.RelSquare (Optimization.inputRep TreeProblem)
    (Optimization.membershipRep (I := TreeProblem) (id : Tree → Tree)) :=
  Optimization.selectionSquare (fun i : TreeProblem => {t | SpanningTree i.val t})
    (fun _ => costMCST) id selectedTree (fun i => selectedTree_minimum i)

def costSquare : Relational.RelSquare (Optimization.inputRep TreeProblem)
    (Optimization.membershipRep (I := TreeProblem) (id : Int → Int)) :=
  Relational.compose (Optimization.observationSquare costMCST) treeSquare

theorem cost_attained (i : TreeProblem) :
    ∃ t, MinimumSpanningTree i.val t ∧ costMCST t = (costSquare.impl i).2 :=
  (costSquare.preserves (r := i) (s := i) rfl).2

def costResult (g : Graph) : Option Int := (prim g).map costMCST

theorem costResult_exact (i : TreeProblem) : costResult i.val = some (costSquare.impl i).2 := by
  rw [costResult, selectedRawTree_result]
  rfl

/-- Actual Prim and nested Kruskal realizations attain the same signed objective. -/
theorem kruskal_cost_agreement (i : TreeProblem) :
    (costSquare.impl i).2 = (MinimumSpanningForest.treeCostSquare.impl i).2 :=
  Kruskal.minimum_cost_eq (selectedTree_minimum i) (MinimumSpanningForest.selectedTree_minimum i)

theorem forest_cost_agreement (i : TreeProblem) :
    (costSquare.impl i).2 = (MinimumSpanningForest.costSquare.impl i.forest).2 :=
  (kruskal_cost_agreement i).trans (MinimumSpanningForest.tree_forest_cost i)

end Prim.Observation
