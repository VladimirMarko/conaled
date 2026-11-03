import Applications.Kruskal.Correctness
import Applications.Optimization.Relations

/-! Total consumers on the justified numbered, nonempty connected domain. -/
set_option autoImplicit false
set_option warningAsError true
namespace Kruskal

abbrev Problem := {g : Graph // NumberedGraph g ∧ ConnectedGraph g}

def feasible (i : Problem) : Set Tree := {t | SpanningTree i.val t}

def objective (_ : Problem) : Tree → Int := costMCST

theorem minimum_iff_minimizer (i : Problem) (t : Tree) :
    MinimumSpanningTree i.val t ↔ t ∈ Optimization.minimizers (feasible i) (objective i) := by
  rfl

/-- The fallback is unreachable on this domain; the chosen source tree is retained. -/
def selectedTree (i : Problem) : Tree := (kruskal i.val).getD ([], [])

theorem selectedTree_result (i : Problem) : kruskal i.val = some (selectedTree i) := by
  obtain ⟨t, ht, _⟩ := kruskal_exists_minimum i.property.1 i.property.2
  simp [selectedTree, ht]

theorem selectedTree_minimum (i : Problem) : MinimumSpanningTree i.val (selectedTree i) :=
  kruskal_minimum i.property.1 (selectedTree_result i)

def treeSquare : Relational.RelSquare (Optimization.inputRep Problem)
    (Optimization.membershipRep (I := Problem) (id : Tree → Tree)) :=
  Optimization.selectionSquare feasible objective id selectedTree
    (fun i => (minimum_iff_minimizer i _).mp (selectedTree_minimum i))

def costSquare : Relational.RelSquare (Optimization.inputRep Problem)
    (Optimization.membershipRep (I := Problem) (id : Int → Int)) :=
  Relational.compose (Optimization.observationSquare costMCST) treeSquare

theorem selected_cost_attained (i : Problem) :
    ∃ t, MinimumSpanningTree i.val t ∧ costMCST t = (costSquare.impl i).2 := by
  obtain ⟨t, ht, he⟩ := (costSquare.preserves (r := i) (s := i) rfl).2
  exact ⟨t, (minimum_iff_minimizer i t).mpr ht, he⟩

theorem selected_cost_eq (i : Problem) (t : Tree) (h : MinimumSpanningTree i.val t) :
    (costSquare.impl i).2 = costMCST t := by
  obtain ⟨s, hs, he⟩ := selected_cost_attained i
  exact he.symm.trans (minimum_cost_eq hs h)

def costResult (g : Graph) : Option Int := (kruskal g).map costMCST

theorem costResult_selected (i : Problem) : costResult i.val = some (costSquare.impl i).2 := by
  rw [costResult, selectedTree_result]
  rfl

theorem costResult_correct {g : Graph} (hg : NumberedGraph g) {c : Int}
    (h : costResult g = some c) : ∃ t, kruskal g = some t ∧ MinimumSpanningTree g t ∧ costMCST t = c := by
  obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp h
  exact ⟨t, ht, kruskal_minimum hg ht, he⟩

theorem costResult_none_iff {g : Graph} (hg : NumberedGraph g) :
    costResult g = none ↔ ¬ ConnectedGraph g := by
  rw [← kruskal_defined_iff_connected hg]
  cases h : kruskal g with
  | none => simp [costResult, h]
  | some t =>
    rcases t with ⟨vs, es⟩
    simp [costResult, h]

/-- Input permutations can alter witnesses while preserving the optimum cost. -/
theorem costResult_perm {g h : Graph} (hg : NumberedGraph g) (hh : NumberedGraph h)
    (hn : nodes g = nodes h) (he : (edges g).Perm (edges h)) : costResult g = costResult h := by
  have connected : ConnectedGraph g ↔ ConnectedGraph h := by
    constructor
    · intro hc u hu v hv
      rw [← hn] at hu hv
      exact hn ▸ reach_mono he.subset (hc u hu v hv)
    · intro hc u hu v hv
      rw [hn] at hu hv
      exact hn.symm ▸ reach_mono he.symm.subset (hc u hu v hv)
  by_cases hc : ConnectedGraph g
  · obtain ⟨t, ht, _⟩ := kruskal_exists_minimum hg hc
    obtain ⟨s, hs, _⟩ := kruskal_exists_minimum hh (connected.mp hc)
    simp only [costResult, ht, hs, Option.map_some]
    exact congrArg some (perm_input_edges_equal_optimal_value hn he hg hh ht hs)
  · rw [(costResult_none_iff hg).mpr hc,
      (costResult_none_iff hh).mpr (fun h => hc (connected.mpr h))]
end Kruskal
