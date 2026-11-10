import Applications.Floating.Rounding

/-!
# Residual-bit shifts and their numerical meaning

The actual core extended mantissa preserves the independent represented value
under right shift. Rounding after an exponent shift reuses the common accuracy
law, including targets below the current exponent, where no shift occurs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Floating.Rounding

open Float.Model Float.Model.UnpackedFloat

theorem shiftRightOne_rep {extended : ExtendedMantissa} {x : Rat}
    (h : ExtendedRep extended x) : ExtendedRep extended.shiftRightOne (x / 2) := by
  rcases extended with ⟨m, r, s⟩
  have parity : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have division : m = 2 * (m / 2) + m % 2 := by omega
  have rational := congrArg (fun n : Nat => (n : Rat)) division
  simp only [Rat.natCast_add, Rat.natCast_mul, Rat.natCast_ofNat] at rational
  rcases parity with parity | parity <;> cases r <;> cases s <;>
    simp [ExtendedRep, ExtendedMantissa.shiftRightOne, ExtendedMantissa.accuracy,
      AccuracyRep, parity] at * <;> grind

theorem shiftRight_rep (extended : ExtendedMantissa) (n : Nat) (x : Rat)
    (h : ExtendedRep extended x) : ExtendedRep (extended >>> n) (x / (2 : Rat) ^ n) := by
  induction n generalizing extended x with
  | zero =>
    change ExtendedRep extended (x / 1)
    simpa only [div_one] using h
  | succ n ih =>
    change ExtendedRep (ExtendedMantissa.shiftRightOne (extended >>> n)) _
    have shifted := shiftRightOne_rep (ih extended x h)
    have power : (x / (2 : Rat) ^ n) / 2 = x / (2 : Rat) ^ (n + 1) := by
      rw [pow_succ, div_div]
    simpa only [power] using shifted

theorem shiftToExponent_rep (m : Nat) (e : Int) (accuracy : Accuracy)
    (target : Int) (x : Rat) (h : AccuracyRep m accuracy x) :
    ExtendedRep (shiftToExponent m e accuracy target).1
      (x / (2 : Rat) ^ (target - e).toNat) :=
  shiftRight_rep _ _ _ (ofMantissaAndAccuracy_rep h)

theorem shiftToExponent_exponent (m : Nat) (e : Int) (accuracy : Accuracy) (target : Int) :
    (shiftToExponent m e accuracy target).2 = max e target := by
  simp only [shiftToExponent]
  omega

theorem rescaled_value (x : Rat) (e : Int) (n : Nat) :
    (x / (2 : Rat) ^ n) * (2 : Rat) ^ (e + (n : Int)) = x * (2 : Rat) ^ e := by
  have nonzero : (2 : Rat) ^ n ≠ 0 := Rat.ne_of_gt (Rat.pow_pos (by decide))
  rw [Rat.zpow_add (by decide), Rat.zpow_natCast]
  grind

theorem shiftToExponent_error (m : Nat) (e : Int) (accuracy : Accuracy)
    (target : Int) (x : Rat) (h : AccuracyRep m accuracy x) :
    let result := shiftToExponent m e accuracy target
    |(result.1.roundedMantissa : Rat) * (2 : Rat) ^ result.2 - x * (2 : Rat) ^ e| ≤
      (2 : Rat) ^ result.2 / 2 := by
  have shifted := shiftToExponent_rep m e accuracy target x h
  let n := (target - e).toNat
  have value := rescaled_value x e n
  have positive : (0 : Rat) < (2 : Rat) ^ (e + (n : Int)) := Rat.zpow_pos (by decide)
  have bound := AccuracyRep.round_scaled shifted ((2 : Rat) ^ (e + (n : Int)))
    (le_of_lt positive)
  change |((shiftToExponent m e accuracy target).1.roundedMantissa : Rat) *
    (2 : Rat) ^ (e + (n : Int)) -
      (x / (2 : Rat) ^ n) * (2 : Rat) ^ (e + (n : Int))| ≤ _ at bound
  rw [value] at bound
  exact bound

theorem shiftToTargetExponent_error (format : Format) (m : Nat) (e : Int)
    (accuracy : Accuracy) (x : Rat) (h : AccuracyRep m accuracy x) :
    let result := shiftToTargetExponent format m e accuracy
    |(result.1.roundedMantissa : Rat) * (2 : Rat) ^ result.2 - x * (2 : Rat) ^ e| ≤
      (2 : Rat) ^ result.2 / 2 :=
  shiftToExponent_error m e accuracy _ x h

theorem shiftRight_mantissa (extended : ExtendedMantissa) (n : Nat) :
    (extended >>> n).mantissa = extended.mantissa / 2 ^ n := by
  induction n with
  | zero => change extended.mantissa = extended.mantissa / 1; omega
  | succ n ih =>
    change (extended >>> n).mantissa / 2 = extended.mantissa / 2 ^ (n + 1)
    rw [ih, Nat.div_div_eq_div_mul, Nat.pow_succ]

theorem shiftToExponent_mantissa (m : Nat) (e : Int) (accuracy : Accuracy) (target : Int) :
    (shiftToExponent m e accuracy target).1.mantissa = m / 2 ^ (target - e).toNat := by
  simp only [shiftToExponent, shiftRight_mantissa]
  cases accuracy with
  | exact => rfl
  | inexact relative => cases relative <;> rfl

end Floating.Rounding
