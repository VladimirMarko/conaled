import Applications.Resources.QuickSortMean

/-! Numerical quicksort-mean cases. The exact values and zero/one boundaries
are fixed independently of the proof. Actual execution means must separately
prove the recurrence before the generic sequence results can be applied.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.QuickSortMean
open Resources.QuickSortMean

theorem empty_mean : closedForm 0 = 1 := closedForm_zero

theorem singleton_mean : closedForm 1 = 5 := by
  have h := closedForm_succ 0
  norm_num at h
  exact h

theorem two_mean : closedForm 2 = 13 := by
  have h := closedForm_succ 1
  rw [singleton_mean] at h
  norm_num at h
  linarith

theorem three_mean : closedForm 3 = (71 : ℝ) / 3 := by
  have h := closedForm_succ 2
  rw [two_mean] at h
  norm_num at h
  linarith

/-- This is a numerical implication. An algorithm client must prove these
premises for its actual mean; they are not assumed execution laws here. -/
theorem sequence_three (A : Nat → ℝ) (hzero : A 0 = 1)
    (hrec : ∀ n : Nat, 0 < n →
      A n = (2 / (n : ℝ)) * (∑ k ∈ Finset.range n, A k) + 4 * (n : ℝ) - 1) :
    A 3 = (71 : ℝ) / 3 :=
  (eq_closedForm A hzero hrec 3).trans three_mean

/-- The empty input's positive tariff cannot satisfy an all-size `n log₂ n`
upper bound, regardless of the real constant. -/
theorem zero_log_boundary (C : ℝ) :
    ¬ closedForm 0 ≤ C * ((0 : ℝ) * Real.logb 2 0) := by
  simp

/-- The singleton gives a second necessary exclusion from a scalar bound. -/
theorem one_log_boundary (C : ℝ) :
    ¬ closedForm 1 ≤ C * ((1 : ℝ) * Real.logb 2 1) := by
  simp [singleton_mean]

/-- The binary-log estimate starts at two, where the logarithm is one. -/
theorem two_log_bound : closedForm 2 ≤ 64 := by
  have h := closedForm_le_nlogb 2 (by decide)
  norm_num [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
  exact h

/-- A sequence with the proved numerical recurrence has the standard
filter-based bound, with natural indexing and real-valued observations. -/
theorem sequence_binary_growth (A : Nat → ℝ) (hzero : A 0 = 1)
    (hrec : ∀ n : Nat, 0 < n →
      A n = (2 / (n : ℝ)) * (∑ k ∈ Finset.range n, A k) + 4 * (n : ℝ) - 1) :
    Asymptotics.IsBigO Filter.atTop A
      (fun n : Nat => (n : ℝ) * Real.logb 2 (n : ℝ)) := by
  have hA : A = closedForm := funext (eq_closedForm A hzero hrec)
  rw [hA]
  exact closedForm_isBigO_logb

end Examples.QuickSortMean
