import Applications.Resources.RoundedRecurrence
import Mathlib.Tactic.NormNum

/-! Connected boundary cases for the rounded recurrence's first source slice.

The examples retain negative offsets, the zero truncation boundary, equality
in the slope constraint, and a negative intercept. They are scalar recurrence
clients, not the median-of-medians algorithm or its resource bridge.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RoundedRecurrence
open Resources.RoundedRecurrence

/-- Dropping zero truncation would assert the false inequality 0 ≤ -1. -/
theorem negative_argument_truncation :
    ⌈(-2 : ℝ)⌉₊ = 0 ∧ ¬ (⌈(-2 : ℝ)⌉₊ : ℝ) ≤ -2 + 1 := by
  have truncated : ⌈(-2 : ℝ)⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by norm_num)
  refine ⟨truncated, ?_⟩
  rw [truncated]
  norm_num

/-- A negative offset remains allowed in the individual source threshold. -/
theorem signed_offset_descent (n : Nat) (large : 2 < n) :
    ⌈(1 / 4 : ℝ) * (n : ℝ) + (-7)⌉₊ < n := by
  exact ceil_affine_lt_of_threshold (1 / 4) (-7) 2 n
    (by norm_num) (by norm_num) (by norm_num) large

/-- The combined cutoff gives both exact child decreases for signed offsets. -/
theorem combined_signed_descent (n : Nat) (large : 5 < n) :
    ⌈(1 / 4 : ℝ) * (n : ℝ) + (-7)⌉₊ < n ∧
      ⌈(1 / 4 : ℝ) * (n : ℝ) + (-2)⌉₊ < n := by
  exact ceil_children_lt (1 / 4) (-7) (1 / 4) (-2) 5 n
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) large

/-- The admissible zero recurrence has the exact two rounded child arguments. -/
theorem zero_recurrence (n : Nat) :
    (fun _ : Nat => (0 : ℝ)) n =
      (fun _ : Nat => (0 : ℝ)) ⌈(1 / 4 : ℝ) * (n : ℝ) + 0⌉₊ +
      (fun _ : Nat => (0 : ℝ)) ⌈(1 / 4 : ℝ) * (n : ℝ) + 0⌉₊ + 0 * (n : ℝ) + 0 := by
  simp

/-- With a=c=1/4 and N=5, all cutoff/zero-toll conditions hold, but the
printed maximum gives C3=0 and therefore does not satisfy a strict slope. -/
theorem strict_slope_choice_counterexample :
    (0 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) + 1 / 4 < 1 ∧
      (2 : ℝ) / (1 - 1 / 4 - 1 / 4) < 5 ∧
      max ((0 : ℝ) / (1 - 1 / 4 - 1 / 4))
        ((0 * 5 + 0 + 0) / ((1 - 1 / 4 - 1 / 4) * 5 - 0 - 0 - 2)) = 0 ∧
      ¬ (0 : ℝ) / (1 - 1 / 4 - 1 / 4) < 0 := by
  norm_num

/-- Equality in the slope constraint still supports the actual one-step law. -/
theorem zero_recurrence_bound_step (n : Nat) (large : 5 ≤ n) :
    (0 : ℝ) ≤ 0 * (n : ℝ) + 0 := by
  exact recurrence_step_le (fun _ => 0) (1 / 4) 0 (1 / 4) 0 0 0 0 0 5 n
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) large (zero_recurrence n)
    (by simp) (by simp)

/-- The constant function -3 satisfies the recurrence with toll 3. Its sharp
intercept may remain -3; the public result does not require replacing it by 0. -/
theorem negative_intercept_bound_step (n : Nat) (large : 5 ≤ n) :
    (-3 : ℝ) ≤ 0 * (n : ℝ) + (-3) := by
  exact recurrence_step_le (fun _ => -3) (1 / 4) (-7) (1 / 4) (-2) 0 3 0 (-3) 5 n
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) large
    (by norm_num) (by simp) (by simp)

/-- Both the constant toll and intercept can be negative in the sharp algebra. -/
theorem negative_toll_and_intercept (n : Nat) (large : 5 ≤ n) :
    (0 * ((1 / 4 : ℝ) * (n : ℝ) + max 0 (-7) + 1) + (-3)) +
      (0 * ((1 / 4 : ℝ) * (n : ℝ) + max 0 (-2) + 1) + (-3)) + 0 * (n : ℝ) + (-10) ≤
        0 * (n : ℝ) + (-3) := by
  exact sharp_affine_absorption (1 / 4) (-7) (1 / 4) (-2) 0 (-10) 0 (-3) 5 n
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) large

end Examples.RoundedRecurrence
