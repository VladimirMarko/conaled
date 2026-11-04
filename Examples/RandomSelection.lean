import Applications.Resources.RandomSelection
import Mathlib.Tactic.NormNum

/-! Connected first-step cases for occurrence-pivot selection.
The singleton call count nine includes its entry, input and bucket lengths,
indexed pivot retrieval and one-pass partition. The duplicate probabilities
are fixed by three occurrences, not two distinct values. Whole-execution
expectation and tail conclusions require the later recursive proofs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RandomSelection
open Resources.RandomSelection
open Applications.Selection
open scoped ENNReal

theorem singleton_step :
    stepRun 0 [7] ⟨0, by decide⟩ = (Sum.inr 7, 9) := by
  rw [stepRun_eq, partition3_eq_filters]
  rfl

theorem duplicate_middle :
    stepRun 1 [0, 0, 1] ⟨1, by decide⟩ = (Sum.inr 0, 15) := by
  rw [stepRun_eq, partition3_eq_filters]
  rfl

/-- Requested rank zero takes the length-one left child. The larger side has
length three, so replacing the selected branch by the larger side changes it. -/
theorem selected_side_is_not_larger_side :
    (stepRun 0 [0, 1, 2, 3, 4] ⟨1, by decide⟩).1 =
      Sum.inl (0, [0]) ∧ max 1 3 = 3 := by
  constructor
  · rw [stepRun_eq, partition3_eq_filters]
    rfl
  · decide

theorem selected_side_valid :
    ([0] : List Nat).length < ([0, 1, 2, 3, 4] : List Nat).length ∧
      (0 < ([0, 1, 2, 3, 4] : List Nat).length → 0 < ([0] : List Nat).length) :=
  stepRun_child 0 [0, 1, 2, 3, 4] ⟨1, by decide⟩ 0 [0]
    selected_side_is_not_larger_side.1

theorem duplicate_ranked : RankedAt ([0, 0, 1] : List Nat) 1 0 :=
  stepRun_ranked 1 [0, 0, 1] ⟨1, by decide⟩ 0 (congrArg Prod.fst duplicate_middle)

/-- Source calls are bounded through the general step theorem, without
identifying an abstract comparison with a function entry. -/
theorem duplicate_source_bound :
    3 ≤ (stepRun 1 [0, 0, 1] ⟨1, by decide⟩).2 ∧
      (stepRun 1 [0, 0, 1] ⟨1, by decide⟩).2 ≤ 27 :=
  stepRun_cost_bounds 1 [0, 0, 1] ⟨1, by decide⟩

noncomputable section

theorem duplicate_zero_probability :
    PMF.map (fun a : Nat => decide (a = 0)) (pivotLaw 0 [0, 1]) true =
      (2 : ℝ≥0∞) / 3 := by
  have hc : (Finset.univ.filter (fun i : Fin 3 =>
      decide (([0, 0, 1] : List Nat)[i.val] = 0) = true)).card = 2 := by decide
  rw [pivotLaw_event, hc]
  norm_num

theorem duplicate_one_probability :
    PMF.map (fun a : Nat => decide (a = 1)) (pivotLaw 0 [0, 1]) true =
      (1 : ℝ≥0∞) / 3 := by
  have hc : (Finset.univ.filter (fun i : Fin 3 =>
      decide (([0, 0, 1] : List Nat)[i.val] = 1) = true)).card = 1 := by decide
  rw [pivotLaw_event, hc]
  norm_num

end
end Examples.RandomSelection
