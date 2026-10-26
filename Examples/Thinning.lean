import Applications.Optimization.NetworkThinning
import Applications.Optimization.KnapsackThinning
import Applications.Optimization.ThinningRelations

/-! # Checked thinning applications and representation composition -/
namespace Examples.Thinning
open Optimization Optimization.Thinning

/-- Reverse changes order without changing candidate origin or coverage. -/
theorem reverse_represents (xs : List Nat) : Represents (· ≤ ·) xs xs.reverse := by
  refine ⟨by intro x hx; simpa using hx, ?_⟩
  intro x hx
  exact ⟨x, by simpa using hx, le_rfl⟩

theorem reverse_not_thinning : ¬ IsThinning (· ≤ ·) [1, 2] [2, 1] := by
  intro h
  have he := List.Sublist.eq_of_length h.1 (by decide)
  contradiction

/-- An order-changing representation can still transport a minimum. -/
theorem reverse_minimum : 1 ∈ minimizers {x : Nat | x ∈ [1, 2]} id := by
  apply minimizer_of_represents (reverse_represents [1, 2]) id (fun _ _ _ _ h => h)
  exact argmin_correct id _ 1 (by decide)

/-- Coverage alone can introduce a cheaper candidate absent from the input. -/
theorem origin_required : Covers (· ≤ ·) [0] [1] ∧ ¬ Represents (· ≤ ·) [1] [0] := by
  constructor
  · intro y hy
    have : y = 1 := List.mem_singleton.mp hy
    subst y
    exact ⟨0, by simp, by decide⟩
  · intro h
    have : (0 : Nat) ∈ [1] := h.1 (by simp)
    simp at this

/-- The adjacent implementation keeps the first equal-cost label. -/
theorem adjacent_tie :
    thinBy (fun p q : Nat × Nat => p.2 ≤ q.2) [(10, 4), (20, 4)] = [(10, 4)] := by decide

theorem selector_tie : argmin Prod.snd [(10, 4), (20, 4)] = some (10, 4) :=
  argmin_first _ _ _ (by intro y hy; simp only [List.mem_singleton] at hy; subst y; exact le_rfl)

open NetworkPaths NetworkThinning in
/-- The feasibility conclusion is obtained from the public failure theorem. -/
theorem disconnected_network :
    ¬ ∃ p, Feasible [[⟨1, 2, 7⟩], [⟨3, 4, -8⟩]] p :=
  (mcp_none_iff _).mp (by decide)

open NetworkPaths NetworkThinning in
/-- A locally cheapest suffix is unusable; source-aware dominance retains the
more expensive suffix needed for the only complete path. -/
theorem network_optimum :
    Optimal [[⟨1, 2, 0⟩], [⟨3, 4, -10⟩, ⟨2, 5, 1⟩]] [⟨1, 2, 0⟩, ⟨2, 5, 1⟩] :=
  mcp_optimal _ _ single_greedy_path_insufficient.1

open KnapsackThinning in
/-- Compose fold pruning with value observation in the reversed natural order. -/
def knapsackValues (capacity : Nat) :
    Relational.RelSquare (inputRep (List (Item Nat)))
      (candidateRep (α := OrderDual Nat) (· ≤ ·)) :=
  Relational.compose
    (mapSquare objective (fun _ _ h => h.2))
    (foldSquare Dominates dominates_refl dominates_trans
      (fun i ss => ss.flatMap (extend capacity i)) (thinBy Dominates)
      (fun i _ _ h => represents_flatMap _ (extend_covers capacity i) h)
      (fun ss => (thinBy_correct Dominates dominates_refl dominates_trans ss).represents)
      [emptySelection])

open KnapsackThinning in
/-- The composed square covers every feasible value by a retained value at least
as large, and every retained value originates in the unpruned candidate list. -/
theorem knapsack_values_refinement (capacity : Nat) (items : List (Item Nat)) :
    Represents (α := OrderDual Nat) (· ≤ ·)
      ((candidates capacity items).map objective) ((frontier capacity items).map objective) :=
  (knapsackValues capacity).preserves (rfl : items = items)

open KnapsackThinning in
theorem observed_sample : ∃ v ∈ (frontier 5 sampleItems).map objective,
    (OrderDual.toDual (9 : Nat)) ≤ v ∧ v ≤ OrderDual.toDual 9 := by
  have h := knapsack_values_refinement 5 sampleItems
  have hv : (OrderDual.toDual (9 : Nat)) ∈ (candidates 5 sampleItems).map objective := by decide
  obtain ⟨v, hv, hle⟩ := h.2 (OrderDual.toDual 9) hv
  refine ⟨v, hv, ?_, hle⟩
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (h.1 hv)
  obtain ⟨chosen, hc, hw, he⟩ := (mem_candidates_iff 5 sampleItems s).mp hs
  change s.value ≤ 9
  rw [← he]
  exact sample_optimal.2 chosen hc hw

end Examples.Thinning
