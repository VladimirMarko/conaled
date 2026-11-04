import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The numerical mean recurrence for the two-filter quicksort tariff.
This module contains no probability model or algorithm assumption. Each
execution client must prove its own base and recurrence before applying
the generic solution. Harmonic numbers and asymptotics use Mathlib's APIs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.QuickSortMean

/-- The exact real expression for the numerical recurrence's solution.
Its interpretation as an execution mean requires a separate transport. -/
noncomputable def closedForm (n : Nat) : ℝ :=
  8 * ((n : ℝ) + 1) * (harmonic n : ℝ) - 12 * (n : ℝ) + 1

@[simp] theorem closedForm_zero : closedForm 0 = 1 := by
  simp [closedForm]

/-- Successor form avoids both predecessor subtraction and division at zero. -/
theorem closedForm_succ (n : Nat) :
    ((n : ℝ) + 1) * closedForm (n + 1) =
      ((n : ℝ) + 2) * closedForm n + 8 * (n : ℝ) + 3 := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [closedForm, harmonic_succ, Rat.cast_add, Rat.cast_inv,
    Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
  field_simp [hn]
  ring

/-- At zero this is only the empty-sum identity `0 = 0`; the base value
is supplied separately by `closedForm_zero`. -/
theorem closedForm_scaled_sum (n : Nat) :
    (n : ℝ) * closedForm n =
      2 * (∑ k ∈ Finset.range n, closedForm k) + 4 * (n : ℝ) ^ 2 - (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := closedForm_succ n
      simp only [Finset.sum_range_succ, Nat.cast_succ]
      nlinarith

/-- The exact positive-size averaging recurrence, verified for the closed
expression rather than postulated about any algorithm. -/
theorem closedForm_recurrence (n : Nat) (hn : 0 < n) :
    closedForm n = (2 / (n : ℝ)) * (∑ k ∈ Finset.range n, closedForm k) +
      4 * (n : ℝ) - 1 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  apply mul_left_cancel₀ hnR
  rw [closedForm_scaled_sum]
  field_simp [hnR]

private theorem scaled_of_recurrence (A : Nat → ℝ)
    (hrec : ∀ n : Nat, 0 < n →
      A n = (2 / (n : ℝ)) * (∑ k ∈ Finset.range n, A k) + 4 * (n : ℝ) - 1)
    (n : Nat) :
    (n : ℝ) * A n = 2 * (∑ k ∈ Finset.range n, A k) + 4 * (n : ℝ) ^ 2 - (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [hrec n (Nat.pos_of_ne_zero hn)]
    field_simp [hnR]

/-- Subtract successive scaled sums. The statement needs no base value;
the positive-size recurrence alone relates consecutive terms. -/
theorem step_of_recurrence (A : Nat → ℝ)
    (hrec : ∀ n : Nat, 0 < n →
      A n = (2 / (n : ℝ)) * (∑ k ∈ Finset.range n, A k) + 4 * (n : ℝ) - 1)
    (n : Nat) :
    ((n : ℝ) + 1) * A (n + 1) = ((n : ℝ) + 2) * A n + 8 * (n : ℝ) + 3 := by
  have hs := scaled_of_recurrence A hrec (n + 1)
  have hp := scaled_of_recurrence A hrec n
  simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one] at hs
  nlinarith

/-- The requested predecessor form is restricted to positive sizes. -/
theorem difference_of_recurrence (A : Nat → ℝ)
    (hrec : ∀ n : Nat, 0 < n →
      A n = (2 / (n : ℝ)) * (∑ k ∈ Finset.range n, A k) + 4 * (n : ℝ) - 1)
    (n : Nat) (hn : 0 < n) :
    (n : ℝ) * A n = ((n : ℝ) + 1) * A (n - 1) + 8 * (n : ℝ) - 5 := by
  cases n with
  | zero => exact (Nat.not_lt_zero 0 hn).elim
  | succ n =>
      have hs := step_of_recurrence A hrec n
      simp only [Nat.cast_succ, Nat.succ_sub_one]
      nlinarith

/-- A numerical sequence with the given base and recurrence is uniquely
determined. The hypotheses must be proved for each actual execution mean. -/
theorem eq_closedForm (A : Nat → ℝ) (hzero : A 0 = 1)
    (hrec : ∀ n : Nat, 0 < n →
      A n = (2 / (n : ℝ)) * (∑ k ∈ Finset.range n, A k) + 4 * (n : ℝ) - 1)
    (n : Nat) : A n = closedForm n := by
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      apply mul_left_cancel₀ hn
      calc
        ((n : ℝ) + 1) * A (n + 1) =
            ((n : ℝ) + 2) * A n + 8 * (n : ℝ) + 3 := step_of_recurrence A hrec n
        _ = ((n : ℝ) + 2) * closedForm n + 8 * (n : ℝ) + 3 := by rw [ih]
        _ = ((n : ℝ) + 1) * closedForm (n + 1) := (closedForm_succ n).symm

/-- Nonnegativity is derived, so no extra sign assumption is needed when
the real expression is placed inside the norms of a Big-O statement. -/
theorem closedForm_nonneg (n : Nat) : 0 ≤ closedForm n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprod : 0 ≤ ((n : ℝ) + 1) * closedForm (n + 1) := by
        rw [closedForm_succ]
        positivity
      exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < (n : ℝ) + 1)).mp hprod

/-- An explicit positive-size estimate using the natural logarithm. -/
theorem closedForm_le_log (n : Nat) (hn : 1 ≤ n) :
    closedForm n ≤ 16 * (n : ℝ) * (1 + Real.log (n : ℝ)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hmul := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n)
    (show (0 : ℝ) ≤ 8 * ((n : ℝ) + 1) by positivity)
  calc
    closedForm n ≤ 8 * ((n : ℝ) + 1) * (1 + Real.log (n : ℝ)) - 12 * (n : ℝ) + 1 := by
      dsimp only [closedForm]
      linarith
    _ ≤ 8 * ((n : ℝ) + 1) * (1 + Real.log (n : ℝ)) := by linarith
    _ ≤ 16 * (n : ℝ) * (1 + Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)

/-- A real `n log n` bound from size two onwards. The logarithm at zero
and one cannot absorb the positive base tariffs. -/
theorem closedForm_le_nlog (n : Nat) (hn : 2 ≤ n) :
    closedForm n ≤ (16 * (1 + 1 / Real.log 2)) * ((n : ℝ) * Real.log (n : ℝ)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogs : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) hnR
  have hdiv : (1 : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
    have h := (div_le_div_iff_of_pos_right htwo).mpr hlogs
    simpa [htwo.ne'] using h
  have hfactor : 1 + Real.log (n : ℝ) ≤
      (1 + 1 / Real.log 2) * Real.log (n : ℝ) := by
    calc
      1 + Real.log (n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 + Real.log (n : ℝ) := by
        linarith
      _ = (1 + 1 / Real.log 2) * Real.log (n : ℝ) := by ring
  calc
    closedForm n ≤ 16 * (n : ℝ) * (1 + Real.log (n : ℝ)) :=
      closedForm_le_log n (by omega)
    _ ≤ 16 * (n : ℝ) * ((1 + 1 / Real.log 2) * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = (16 * (1 + 1 / Real.log 2)) * ((n : ℝ) * Real.log (n : ℝ)) := by ring

/-- The book's binary logarithm with a concrete constant and explicit domain. -/
theorem closedForm_le_nlogb (n : Nat) (hn : 2 ≤ n) :
    closedForm n ≤ 32 * ((n : ℝ) * Real.logb 2 (n : ℝ)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo_le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogb : 1 ≤ Real.logb 2 (n : ℝ) := by
    calc
      1 = Real.logb 2 (2 : ℝ) := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 (n : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num) (by norm_num) hnR
  have hchange : Real.log (n : ℝ) = Real.log 2 * Real.logb 2 (n : ℝ) := by
    rw [Real.logb]
    field_simp [htwo.ne']
  have hlog_le : Real.log (n : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    rw [hchange]
    simpa using mul_le_mul_of_nonneg_right htwo_le
      (show 0 ≤ Real.logb 2 (n : ℝ) by linarith)
  have hfactor : 1 + Real.log (n : ℝ) ≤ 2 * Real.logb 2 (n : ℝ) := by linarith
  calc
    closedForm n ≤ 16 * (n : ℝ) * (1 + Real.log (n : ℝ)) :=
      closedForm_le_log n (by omega)
    _ ≤ 16 * (n : ℝ) * (2 * Real.logb 2 (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = 32 * ((n : ℝ) * Real.logb 2 (n : ℝ)) := by ring

theorem closedForm_isBigO_log :
    Asymptotics.IsBigO Filter.atTop closedForm
      (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨16 * (1 + 1 / Real.log 2), Filter.eventually_atTop.mpr ⟨2, fun n hn => ?_⟩⟩
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (closedForm_nonneg n),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hlog)]
  exact closedForm_le_nlog n hn

theorem closedForm_isBigO_logb :
    Asymptotics.IsBigO Filter.atTop closedForm
      (fun n : Nat => (n : ℝ) * Real.logb 2 (n : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨32, Filter.eventually_atTop.mpr ⟨2, fun n hn => ?_⟩⟩
  have hlog : 0 ≤ Real.logb 2 (n : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (closedForm_nonneg n),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hlog)]
  exact closedForm_le_nlogb n hn

end Resources.QuickSortMean
