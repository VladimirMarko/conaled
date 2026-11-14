import Applications.Resources.RandomSelectionDrift
import Examples.RandomSelection
import Examples.RandomSelectionMean
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Connected cases for duplicate-aware selection drift and linear expectations.

The larger-rank-side sums for sizes zero through five are 0,0,2,5,10,16.
Equal occurrences keep separate ordered rank positions and uniform probability.
On [0,0,1] at rank two, the actual next sizes are 1,1,0, with mean 2/3.
The selected-side counterexample still has next size one versus majorant three.
Generic clients combine the actual returned rank with scan and source means.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RandomSelectionDrift
open Resources.RandomSelection
open scoped BigOperators ENNReal
universe u
variable {α : Type u} [LinearOrder α]

noncomputable section

theorem rank_side_small_values :
    rankSideSum 0 = 0 ∧ rankSideSum 1 = 0 ∧ rankSideSum 2 = 2 ∧
      rankSideSum 3 = 5 ∧ rankSideSum 4 = 10 ∧ rankSideSum 5 = 16 := by
  have h2 : rankSideSum 2 = 2 := by simpa using rankSideSum_add_two 0
  have h3 : rankSideSum 3 = 5 := by simpa using rankSideSum_add_two 1
  have h4 : rankSideSum 4 = 10 := by simpa [h2] using rankSideSum_add_two 2
  have h5 : rankSideSum 5 = 16 := by simpa [h3] using rankSideSum_add_two 3
  exact ⟨rankSideSum_zero, rankSideSum_one, h2, h3, h4, h5⟩

theorem stable_duplicate_positions (x : α) :
    Resources.RandomQuickSort.occurrenceRank id [x, x] (0 : Fin 2) <
      Resources.RandomQuickSort.occurrenceRank id [x, x] (1 : Fin 2) :=
  occurrenceRank_tie [x, x] 0 1 (by
    change (0 : Fin 2) < 1
    decide) (by rfl)

theorem refined_duplicate_uniform (x : α) :
    PMF.map (Resources.RandomQuickSort.occurrenceRank id [x, x])
      (Resources.RandomQuickSort.uniformIndex 1) =
        Resources.RandomQuickSort.uniformIndex 1 :=
  occurrenceRank_uniform x [x]

/-- The valid singleton stops; the invalid extension's selected empty child
also has size zero. The general majorant establishes both at once. -/
theorem singleton_next_size (k : Nat) (x : α) (i : Fin 1) : nextSize k [x] i = 0 := by
  have hr : (Resources.RandomQuickSort.occurrenceRank id [x] i).val = 0 := by
    have hlt : (Resources.RandomQuickSort.occurrenceRank id [x] i).val < 1 :=
      (Resources.RandomQuickSort.occurrenceRank id [x] i).isLt
    omega
  have h := nextSize_le_rankSide k [x] i
  simpa [hr] using h

theorem duplicate_next_choices (i : Fin 3) :
    nextSize 2 ([0, 0, 1] : List Nat) i = if i = 2 then 0 else 1 := by
  fin_cases i <;> rw [nextSize, stepRun_eq, Applications.Selection.partition3_eq_filters] <;>
    rfl

/-- Both zero occurrences can cause the singleton continuation; their
probabilities must add, despite their equal pivot values. -/
theorem duplicate_next_expectation :
    (∑ i : Fin 3, Resources.RandomQuickSort.uniformIndex 2 i *
      (nextSize 2 ([0, 0, 1] : List Nat) i : ℝ≥0∞)) = (2 : ℝ≥0∞) / 3 := by
  have hsum : (∑ i : Fin 3, nextSize 2 ([0, 0, 1] : List Nat) i) = 2 := by
    simp [Fin.sum_univ_three, duplicate_next_choices]
  simp only [Resources.RandomQuickSort.uniformIndex_apply, ← Finset.mul_sum]
  rw [← Nat.cast_sum, hsum]
  change (3 : ℝ≥0∞)⁻¹ * 2 = 2 / 3
  rw [div_eq_mul_inv, mul_comm]

theorem duplicate_drift_bound :
    (∑ i : Fin 3, Resources.RandomQuickSort.uniformIndex 2 i *
      (nextSize 2 ([0, 0, 1] : List Nat) i : ℝ≥0∞)) ≤ (9 : ℝ≥0∞) / 4 := by
  have h := nextSize_drift 2 (0 : Nat) [0, 1]
  change (∑ i : Fin 3, Resources.RandomQuickSort.uniformIndex 2 i *
    (nextSize 2 ([0, 0, 1] : List Nat) i : ℝ≥0∞)) ≤ (3 / 4 : ℝ≥0∞) * 3 at h
  calc
    _ ≤ (3 / 4 : ℝ≥0∞) * 3 := h
    _ = _ := by
      simp only [div_eq_mul_inv]
      ring

theorem selected_branch_is_smaller :
    nextSize 0 ([0, 1, 2, 3, 4] : List Nat) ⟨1, by decide⟩ = 1 ∧ max 1 3 = 3 := by
  constructor
  · simp only [nextSize, Examples.RandomSelection.selected_side_is_not_larger_side.1,
      List.length_singleton]
  · exact Examples.RandomSelection.selected_side_is_not_larger_side.2

theorem arbitrary_expected_bounds (k : Nat) (xs : List α) :
    (xs.length : ℝ) ≤ scanMean k xs ∧ scanMean k xs ≤ 4 * (xs.length : ℝ) ∧
      (xs.length : ℝ) ≤ sourceMean k xs ∧ sourceMean k xs ≤ 36 * (xs.length : ℝ) + 2 := by
  obtain ⟨hl, hu⟩ := scanMean_linear_bounds k xs
  obtain ⟨tl, tu⟩ := sourceMean_linear_bounds k xs
  exact ⟨hl, hu, tl, tu⟩

theorem valid_selection_expected_bounds (k : Nat) (xs : List α) (hk : k < xs.length)
    (result : Outcome α) (hr : result ∈ (run k xs).support) :
    ∃ a, result.1 = some a ∧ Applications.Selection.RankedAt xs k a ∧
      (xs.length : ℝ) ≤ scanMean k xs ∧ scanMean k xs ≤ 4 * (xs.length : ℝ) ∧
        sourceMean k xs ≤ 36 * (xs.length : ℝ) + 2 := by
  obtain ⟨a, ha, hRank⟩ := run_valid k xs hk result hr
  obtain ⟨hl, hu⟩ := scanMean_linear_bounds k xs
  exact ⟨a, ha, hRank, hl, hu, (sourceMean_linear_bounds k xs).2⟩

/-- Empty worker expectations satisfy the linear bounds. This is not a
non-strict tail claim at zero length, whose threshold would also be zero. -/
theorem empty_expected_bounds (k : Nat) :
    scanMean k ([] : List α) = 0 ∧ sourceMean k ([] : List α) = 2 ∧
      scanMean k ([] : List α) ≤ 0 ∧ sourceMean k ([] : List α) ≤ 2 := by
  refine ⟨scanMean_nil (α := α) k, sourceMean_nil (α := α) k, ?_, ?_⟩
  · simpa only [List.length_nil, Nat.cast_zero, mul_zero] using
      scanMean_linear_le k ([] : List α)
  · simpa only [List.length_nil, Nat.cast_zero, mul_zero, zero_add] using
      (sourceMean_linear_bounds k ([] : List α)).2

end
end Examples.RandomSelectionDrift
