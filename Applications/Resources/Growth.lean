import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Natural measured counts use the standard asymptotic interface after real casting. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources

/-- An explicit natural bound gives the same eventual bound on real-cast counts. -/
theorem isBigO_of_nat_bound (f g : Nat → Nat) (C N : Nat)
    (bound : ∀ n, N ≤ n → f n ≤ C * g n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (f n : ℝ)) (fun n => (g n : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨(C : ℝ), Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
  simpa using (Nat.cast_le (α := ℝ)).mpr (bound n hn)

/-- The natural ceiling log has at most twice the real binary log once `n ≥ 2`.
The lower bound on `n` supplies the unit of slack needed for ceiling. -/
theorem clog_two_cast_le_two_logb (n : Nat) (hn : 2 ≤ n) :
    (Nat.clog 2 n : ℝ) ≤ 2 * Real.logb 2 n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 ≤ Real.logb 2 n := by
    calc
      1 = Real.logb 2 (2 : ℝ) := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 n := Real.logb_le_logb_of_le (by norm_num) (by norm_num) hn'
  have hceil : (Nat.clog 2 n : ℝ) < Real.logb 2 n + 1 := by
    rw [← Real.natCeil_logb_natCast 2 n]
    exact Nat.ceil_lt_add_one (by linarith)
  linarith

/-- A proved ceiling-log count bound yields the ordinary real `O(n log₂ n)`
statement. This numerical bridge makes no claim about compiled execution. -/
theorem isBigO_of_clog_two_bound (f : Nat → Nat) (C N : Nat)
    (bound : ∀ n, N ≤ n → f n ≤ C * (n * Nat.clog 2 n)) :
    Asymptotics.IsBigO Filter.atTop (fun n => (f n : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨2 * (C : ℝ), Filter.eventually_atTop.mpr ⟨max N 2, fun n hn => ?_⟩⟩
  have hN : N ≤ n := (Nat.le_max_left _ _).trans hn
  have htwo : 2 ≤ n := (Nat.le_max_right _ _).trans hn
  have hlog : 0 ≤ Real.logb 2 n :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega))
  have hb : (f n : ℝ) ≤ (C : ℝ) * ((n : ℝ) * (Nat.clog 2 n : ℝ)) := by
    exact_mod_cast bound n hN
  have hc := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (clog_two_cast_le_two_logb n htwo)
      (Nat.cast_nonneg n)) (Nat.cast_nonneg C)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hlog)]
  calc
    (f n : ℝ) ≤ (C : ℝ) * ((n : ℝ) * (Nat.clog 2 n : ℝ)) := hb
    _ ≤ (C : ℝ) * ((n : ℝ) * (2 * Real.logb 2 n)) := hc
    _ = 2 * (C : ℝ) * ((n : ℝ) * Real.logb 2 n) := by ring

end Resources
