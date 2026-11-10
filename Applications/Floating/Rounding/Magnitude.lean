import Applications.Floating.Rounding.Normalize
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Magnitude bounds for the actual rounding unit

An inclusive power-of-two upper bound gives a total-exponent bound with one
additional bit. The subnormal floor and incoming alignment remain explicit.
Integer-power order comparisons use the existing ordered-field theorems.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Floating.Rounding

open Float.Model Float.Model.UnpackedFloat
open Floating.Observation (dyadicValue dyadicValue_eq)

theorem dyadic_lower_power (m : Nat) (e : Int) (k : Nat) (lower : 2 ^ k ≤ m) :
    (2 : Rat) ^ ((k : Int) + e) ≤ dyadicValue m e := by
  have castLower := Nat.cast_le (α := Rat).mpr lower
  simp only [Nat.cast_pow, Nat.cast_ofNat] at castLower
  have scaled := mul_le_mul_of_nonneg_right castLower
    (le_of_lt (zpow_pos (by norm_num : (0 : Rat) < 2) e))
  rw [dyadicValue_eq, zpow_add₀ (by norm_num : (2 : Rat) ≠ 0), zpow_natCast]
  exact scaled

theorem totalExponent_le_of_value_le (m : Nat) (e : Int) (positive : 0 < m)
    (k : Int) (upper : dyadicValue m e ≤ (2 : Rat) ^ k) : totalExponent m e ≤ k + 1 := by
  have lower := dyadic_lower_power m e m.log2 (Nat.log2_self_le (by omega))
  have exponent := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : Rat) < 2)).mp
    (lower.trans upper)
  simp only [totalExponent]
  omega

theorem shift_exponent_bound (format : Format) (m : Nat) (e : Int) (a : Accuracy)
    (x : Rat) (k : Int) (represented : AccuracyRep m a x) (aligned : Aligned format m e)
    (upper : x * (2 : Rat) ^ e ≤ (2 : Rat) ^ k) :
    (shiftToTargetExponent format m e a).2 ≤
      max (k + 1 - (format.mantissaBits : Int)) format.minExponent := by
  have bits : 2 ≤ format.mantissaBits := by
    have := format.hm
    simp only [Format.mantissaBits]
    omega
  have interval := represented.bounds
  have mantissa : dyadicValue m e ≤ (2 : Rat) ^ k := by
    have scaled := mul_le_mul_of_nonneg_right interval.1
      (le_of_lt (zpow_pos (by norm_num : (0 : Rat) < 2) e))
    rw [← dyadicValue_eq] at scaled
    exact scaled.trans upper
  have current : e ≤ max (k + 1 - (format.mantissaBits : Int)) format.minExponent := by
    rcases aligned with floor | normal
    · omega
    · have lower := dyadic_lower_power m e (format.mantissaBits - 1) normal
      have exponent := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : Rat) < 2)).mp
        (lower.trans mantissa)
      omega
  have target : format.targetExponent (totalExponent m e) ≤
      max (k + 1 - (format.mantissaBits : Int)) format.minExponent := by
    by_cases zero : m = 0
    · have floor : e ≤ format.minExponent := by
        have power := Nat.two_pow_pos (format.mantissaBits - 1)
        rcases aligned with floor | normal <;> omega
      simp only [zero, totalExponent, Nat.log2_zero, Format.targetExponent]
      omega
    · have exponent := totalExponent_le_of_value_le m e (by omega) k mantissa
      simp only [Format.targetExponent]
      omega
  change (shiftToExponent m e a (format.targetExponent (totalExponent m e))).2 ≤ _
  rw [shiftToExponent_exponent]
  omega

/-- A strict upper power saves the bit present in the inclusive bound. -/
theorem totalExponent_le_of_value_lt (m : Nat) (e : Int) (positive : 0 < m)
    (k : Int) (upper : dyadicValue m e < (2 : Rat) ^ k) : totalExponent m e ≤ k := by
  have lower := dyadic_lower_power m e m.log2 (Nat.log2_self_le (Nat.ne_of_gt positive))
  have exponent := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : Rat) < 2)).mp
    (lower.trans_lt upper)
  simp only [totalExponent]
  omega

/-- Bound the actual first shift using a strict represented upper power. -/
theorem shift_exponent_bound_strict (format : Format) (m : Nat) (e : Int) (a : Accuracy)
    (x : Rat) (k : Int) (represented : AccuracyRep m a x) (aligned : Aligned format m e)
    (upper : x * (2 : Rat) ^ e < (2 : Rat) ^ k) :
    (shiftToTargetExponent format m e a).2 ≤
      max (k - (format.mantissaBits : Int)) format.minExponent := by
  have bits : 2 ≤ format.mantissaBits := by
    have := format.hm
    simp only [Format.mantissaBits]
    omega
  have interval := represented.bounds
  have mantissa : dyadicValue m e < (2 : Rat) ^ k := by
    have scaled := mul_le_mul_of_nonneg_right interval.1
      (le_of_lt (zpow_pos (by norm_num : (0 : Rat) < 2) e))
    rw [← dyadicValue_eq] at scaled
    exact scaled.trans_lt upper
  have current : e ≤ max (k - (format.mantissaBits : Int)) format.minExponent := by
    rcases aligned with floor | normal
    · omega
    · have lower := dyadic_lower_power m e (format.mantissaBits - 1) normal
      have exponent := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : Rat) < 2)).mp
        (lower.trans_lt mantissa)
      omega
  have target : format.targetExponent (totalExponent m e) ≤
      max (k - (format.mantissaBits : Int)) format.minExponent := by
    by_cases zero : m = 0
    · have floor : e ≤ format.minExponent := by
        have power := Nat.two_pow_pos (format.mantissaBits - 1)
        rcases aligned with floor | normal <;> omega
      simp only [zero, totalExponent, Nat.log2_zero, Format.targetExponent]
      omega
    · have exponent := totalExponent_le_of_value_lt m e (by omega) k mantissa
      simp only [Format.targetExponent]
      omega
  change (shiftToExponent m e a (format.targetExponent (totalExponent m e))).2 ≤ _
  rw [shiftToExponent_exponent]
  omega

end Floating.Rounding
