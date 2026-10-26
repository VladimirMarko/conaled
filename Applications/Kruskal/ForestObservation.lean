import Applications.Kruskal.NestedClient
import Applications.Kruskal.Observation

/-! Forest witnesses and normalized tree witnesses use the same independent
optimization and observation constructions. Raw source results retain their order. -/
set_option autoImplicit false
set_option warningAsError true
namespace MinimumSpanningForest
open Kruskal
open ForestPartition (chosen)
open ForestKruskalSource (Forest)

abbrev Problem := {g : Graph // (nodes g).Nodup ∧ EndpointsIn (nodes g) (edges g)}

def feasible (i : Problem) : Set (List Edge) := {fs | SpanningForest i.val fs}

theorem minimum_iff_minimizer (i : Problem) (fs : List Edge) :
    Minimum i.val fs ↔ fs ∈ Optimization.minimizers (feasible i) cost := Iff.rfl

/-- The fallback is unreachable on the valid graph domain, including empty graphs. -/
def selectedForest (i : Problem) : Forest := (ForestKruskalSource.mcsf i.val).getD []

theorem selectedForest_result (i : Problem) :
    ForestKruskalSource.mcsf i.val = some (selectedForest i) := by
  obtain ⟨ts, ht, _, _⟩ := mcsf_correct i.val i.property.1 i.property.2
  simp [selectedForest, ht]

theorem selectedForest_rep (i : Problem) : Rep (nodes i.val) (selectedForest i) := by
  obtain ⟨ts, ht, hr, _⟩ := mcsf_correct i.val i.property.1 i.property.2
  simpa [selectedForest, ht] using hr

theorem selectedForest_minimum (i : Problem) : Minimum i.val (chosen (selectedForest i)) :=
  mcsf_result_minimum i.property.1 i.property.2 (selectedForest_result i)

def forestSquare : Relational.RelSquare (Optimization.inputRep Problem)
    (Optimization.membershipRep (I := Problem) (id : List Edge → List Edge)) :=
  Optimization.selectionSquare feasible (fun _ => cost) id (fun i => chosen (selectedForest i))
    (fun i => (minimum_iff_minimizer i _).mp (selectedForest_minimum i))

def costSquare : Relational.RelSquare (Optimization.inputRep Problem)
    (Optimization.membershipRep (I := Problem) (id : Int → Int)) :=
  Relational.compose (Optimization.observationSquare cost) forestSquare

theorem minimum_cost_eq {g : Graph} {fs gs : List Edge}
    (hf : Minimum g fs) (hg : Minimum g gs) : cost fs = cost gs :=
  le_antisymm (hf.2 gs hg.1) (hg.2 fs hf.1)

theorem selected_cost_attained (i : Problem) :
    ∃ fs, Minimum i.val fs ∧ cost fs = (costSquare.impl i).2 := by
  obtain ⟨fs, hf, he⟩ := (costSquare.preserves (r := i) (s := i) rfl).2
  exact ⟨fs, (minimum_iff_minimizer i fs).mpr hf, he⟩

theorem selected_cost_eq (i : Problem) (fs : List Edge) (hf : Minimum i.val fs) :
    (costSquare.impl i).2 = cost fs :=
  minimum_cost_eq (selectedForest_minimum i) hf

def costResult (g : Graph) : Option Int := (ForestKruskalSource.mcsf g).map (cost ∘ chosen)

theorem costResult_selected (i : Problem) : costResult i.val = some (costSquare.impl i).2 := by
  rw [costResult, selectedForest_result]
  rfl

/-- The independent forest and tree problems agree on connected nonempty graphs. -/
theorem minimum_tree_iff {g : Graph} {fs : List Edge} (hne : nodes g ≠ [])
    (hend : EndpointsIn (nodes g) (edges g)) (hc : ConnectedGraph g) :
    MinimumSpanningTree g (nodes g, fs) ↔ Minimum g fs := by
  constructor
  · intro ht
    exact ⟨ForestKruskalClient.spanningTree_forest hend ht.1,
      fun gs hg => ht.2 (nodes g, gs) (connected_spanningForest hg hne hc)⟩
  · intro hf
    exact ⟨connected_spanningForest hf.1 hne hc,
      fun t ht => hf.2 (edges t) (ForestKruskalClient.spanningTree_forest hend ht)⟩

abbrev TreeProblem := {g : Graph // (nodes g).Nodup ∧ nodes g ≠ [] ∧
  EndpointsIn (nodes g) (edges g) ∧ ConnectedGraph g}

def TreeProblem.forest (i : TreeProblem) : Problem := ⟨i.val, i.property.1, i.property.2.2.1⟩

/-- Source component vertex/edge order, before the explicit vertex normalization. -/
def selectedRawTree (i : TreeProblem) : Tree :=
  (ForestKruskalSource.kruskal1 i.val).getD ([], [])

theorem selectedRawTree_result (i : TreeProblem) :
    ForestKruskalSource.kruskal1 i.val = some (selectedRawTree i) := by
  obtain ⟨t, ht, _, _⟩ := ForestKruskalClient.kruskal1_exists i.property.1
    i.property.2.1 i.property.2.2.1 i.property.2.2.2
  simp [selectedRawTree, ht]

def selectedTree (i : TreeProblem) : Tree := (nodes i.val, edges (selectedRawTree i))

theorem selectedTree_minimum (i : TreeProblem) : MinimumSpanningTree i.val (selectedTree i) :=
  (ForestKruskalClient.kruskal1_result_minimum i.property.1 i.property.2.1
    i.property.2.2.1 (selectedRawTree_result i)).2

theorem selectedRawTree_vertices (i : TreeProblem) :
    (nodes (selectedRawTree i)).Perm (nodes i.val) :=
  (ForestKruskalClient.kruskal1_result_minimum i.property.1 i.property.2.1
    i.property.2.2.1 (selectedRawTree_result i)).1

def treeSquare : Relational.RelSquare (Optimization.inputRep TreeProblem)
    (Optimization.membershipRep (I := TreeProblem) (id : Tree → Tree)) :=
  Optimization.selectionSquare (fun i : TreeProblem => {t | SpanningTree i.val t})
    (fun _ => costMCST) id selectedTree (fun i => selectedTree_minimum i)

def treeCostSquare : Relational.RelSquare (Optimization.inputRep TreeProblem)
    (Optimization.membershipRep (I := TreeProblem) (id : Int → Int)) :=
  Relational.compose (Optimization.observationSquare costMCST) treeSquare

theorem tree_cost_attained (i : TreeProblem) :
    ∃ t, MinimumSpanningTree i.val t ∧ costMCST t = (treeCostSquare.impl i).2 :=
  (treeCostSquare.preserves (r := i) (s := i) rfl).2

theorem tree_forest_cost (i : TreeProblem) :
    (treeCostSquare.impl i).2 = (costSquare.impl i.forest).2 := by
  exact minimum_cost_eq
    ((minimum_tree_iff i.property.2.1 i.property.2.2.1 i.property.2.2.2).mp
      (selectedTree_minimum i)) (selectedForest_minimum i.forest)

/-- Before normalization, connected consumers agree on the entire singleton forest. -/
theorem selected_tree_forest (i : TreeProblem) :
    selectedForest i.forest = [selectedRawTree i] := by
  have h := (ForestKruskalClient.kruskal1_forest_result i.property.1 i.property.2.2.1
    (selectedRawTree_result i)).1
  exact Option.some.inj ((selectedForest_result i.forest).symm.trans h)

def numberedProblem (i : Kruskal.Problem) : TreeProblem :=
  ⟨i.val, (Kruskal.start_invariant i.property.1).1.1.1, i.property.1.1,
    i.property.1.2.2, i.property.2⟩

/-- Both actual realizations attain the same optimum, without equating tied trees. -/
theorem numbered_cost_agreement (i : Kruskal.Problem) :
    (treeCostSquare.impl (numberedProblem i)).2 = (Kruskal.costSquare.impl i).2 :=
  Kruskal.minimum_cost_eq (selectedTree_minimum (numberedProblem i)) (Kruskal.selectedTree_minimum i)

end MinimumSpanningForest
