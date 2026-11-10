import Applications.Floating.Rounding.Magnitude

/-!
# Closed ranges for actual rounded values

Natural endpoints lie exactly on every binary grid whose exponent is at most
zero. The nearest-even endpoint law therefore gives a closed range as well as
the half-unit error bound. Canonicality retains its separate alignment premise.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Floating.Rounding

open Float.Model Float.Model.UnpackedFloat
open Floating.Observation (dyadicValue dyadicValue_eq)
open Floating.Packing (Canonical)

theorem grid_integer_endpoint (b : Nat) (e : Int) (nonpositive : e ≤ 0) :
    ((b * 2 ^ (-e).toNat : Nat) : Rat) * (2 : Rat) ^ e = (b : Rat) := by
  have exponent : e = -(((-e).toNat : Nat) : Int) := by omega
  have inverse : (2 : Rat) ^ e = ((2 : Rat) ^ (-e).toNat)⁻¹ := by
    calc
      (2 : Rat) ^ e = (2 : Rat) ^ (-(((-e).toNat : Nat) : Int)) :=
        congrArg (fun n : Int => (2 : Rat) ^ n) exponent
      _ = ((2 : Rat) ^ (-e).toNat)⁻¹ := by rw [zpow_neg, zpow_natCast]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [inverse, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : Rat) ≠ 0)),
    mul_one]

/-- The closed interval contract needs no alignment or positive-mantissa premise. -/
theorem roundWithAccuracy_interval (format : Format) (m : Nat) (e : Int)
    (a : Accuracy) (x : Rat) (b : Nat) (represented : AccuracyRep m a x)
    (upper : x * (2 : Rat) ^ e ≤ (b : Rat))
    (unitBound : (shiftToTargetExponent format m e a).2 ≤ 0) :
    ∃ value, Observation.unpack (roundWithAccuracy format .positive m e a) = some value ∧
      0 ≤ value ∧ value ≤ (b : Rat) := by
  let target := format.targetExponent (totalExponent m e)
  let n := (target - e).toNat
  let shifted := shiftToTargetExponent format m e a
  let endpoint := b * 2 ^ (-shifted.2).toNat
  have shiftedRep := shiftToExponent_rep m e a target x represented
  have preserved := rescaled_value x e n
  change (x / (2 : Rat) ^ n) * (2 : Rat) ^ shifted.2 = x * (2 : Rat) ^ e at preserved
  have endpointValue := grid_integer_endpoint b shifted.2 unitBound
  have unitPositive : (0 : Rat) < (2 : Rat) ^ shifted.2 := zpow_pos (by norm_num) _
  have scaledUpper : x / (2 : Rat) ^ n ≤ (endpoint : Rat) := by
    apply (mul_le_mul_iff_left₀ unitPositive).mp
    change (x / (2 : Rat) ^ n) * (2 : Rat) ^ shifted.2 ≤
      (endpoint : Rat) * (2 : Rat) ^ shifted.2
    rw [preserved, endpointValue]
    exact upper
  have roundedUpper := AccuracyRep.round_upper endpoint shiftedRep scaledUpper
  have castUpper := Rat.natCast_le_natCast.mpr roundedUpper
  have scaled := mul_le_mul_of_nonneg_right castUpper (le_of_lt unitPositive)
  refine ⟨dyadicValue shifted.1.roundedMantissa shifted.2,
    roundWithAccuracy_positive_value format m e a, ?_, ?_⟩
  · rw [dyadicValue_eq]
    exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt unitPositive)
  · rw [dyadicValue_eq]
    change (shifted.1.roundedMantissa : Rat) * (2 : Rat) ^ shifted.2 ≤ _ at scaled
    rw [endpointValue] at scaled
    exact scaled

theorem rounded_bounds (format : Format) (m : Nat) (e : Int) (a : Accuracy)
    (x : Rat) (b : Nat) (E : Int) (represented : AccuracyRep m a x)
    (aligned : Aligned format m e) (upper : x * (2 : Rat) ^ e ≤ (b : Rat))
    (unitBound : (shiftToTargetExponent format m e a).2 ≤ E) (nonpositive : E ≤ 0) :
    ∃ value, Observation.unpack (roundWithAccuracy format .positive m e a) = some value ∧
      0 ≤ value ∧ value ≤ (b : Rat) ∧ |value - x * (2 : Rat) ^ e| ≤ (2 : Rat) ^ E / 2 ∧
      Canonical format (roundWithAccuracy format .positive m e a) := by
  obtain ⟨value, observed, lower, bound⟩ :=
    roundWithAccuracy_interval format m e a x b represented upper (unitBound.trans nonpositive)
  obtain ⟨other, otherObserved, error⟩ := roundWithAccuracy_error format m e a x represented
  have same : other = value := Option.some.inj (otherObserved.symm.trans observed)
  subst other
  have power := zpow_le_zpow_right₀ (by norm_num : (1 : Rat) ≤ 2) unitBound
  have halfUnit := div_le_div_of_nonneg_right power (by norm_num : (0 : Rat) ≤ 2)
  exact ⟨value, observed, lower, bound, error.trans halfUnit,
    roundWithAccuracy_canonical format .positive m e a aligned⟩

/-- Full round establishes alignment before using the strict magnitude bound. -/
theorem round_bounds (format : Format) (m : Nat) (e : Int) (positive : 0 < m)
    (b : Nat) (k E : Int) (upper : dyadicValue m e ≤ (b : Rat))
    (endpoint : (b : Rat) < (2 : Rat) ^ k)
    (exponentBound : max (k - (format.mantissaBits : Int)) format.minExponent ≤ E)
    (nonpositive : E ≤ 0) :
    ∃ value, Observation.unpack (round format .positive m e) = some value ∧
      0 ≤ value ∧ value ≤ (b : Rat) ∧ |value - dyadicValue m e| ≤ (2 : Rat) ^ E / 2 ∧
      Canonical format (round format .positive m e) := by
  let target := format.targetExponent (totalExponent m e)
  let decreased := decreaseExponent m e target
  have preserved := decreaseExponent_value m e target
  have aligned := decreaseExponent_aligned format m e positive
  have represented : AccuracyRep decreased.1 .exact (decreased.1 : Rat) := rfl
  have original : (decreased.1 : Rat) * (2 : Rat) ^ decreased.2 = dyadicValue m e := by
    rw [← dyadicValue_eq]
    exact preserved
  have decreasedUpper : (decreased.1 : Rat) * (2 : Rat) ^ decreased.2 ≤ (b : Rat) := by
    rw [original]
    exact upper
  have strict : (decreased.1 : Rat) * (2 : Rat) ^ decreased.2 < (2 : Rat) ^ k := by
    rw [original]
    exact upper.trans_lt endpoint
  have shifted := shift_exponent_bound_strict format decreased.1 decreased.2 .exact
    (decreased.1 : Rat) k represented aligned strict
  have result := rounded_bounds format decreased.1 decreased.2 .exact (decreased.1 : Rat)
    b E represented aligned decreasedUpper (shifted.trans exponentBound) nonpositive
  rw [original] at result
  simpa only [round] using result

end Floating.Rounding
