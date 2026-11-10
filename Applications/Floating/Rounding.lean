import Applications.Floating.Rounding.Accuracy

/-!
# Quotient and exponent bridges for the actual floating core

These results concern the pinned model's quotient/remainder classification and
first mantissa rounding. Later normalization, packing and overflow proofs are
separate obligations. The quotient wrapper names an existing model computation;
it does not replace Float division by rational execution.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Floating.Rounding

open Float.Model Float.Model.UnpackedFloat
open Floating.Observation (dyadicValue dyadicValue_eq)

theorem accuracyOfFraction_rep (m num den : Nat) (positive : 0 < den) (proper : num < den) :
    AccuracyRep m (accuracyOfFraction num den) ((m : Rat) + (num : Rat) / (den : Rat)) := by
  have hd : (0 : Rat) < (den : Rat) := Rat.natCast_lt_natCast.mpr positive
  have hn : (num : Rat) < (den : Rat) := Rat.natCast_lt_natCast.mpr proper
  have cancel := Rat.div_mul_cancel (a := (num : Rat)) (Rat.ne_of_gt hd)
  unfold accuracyOfFraction
  split
  · rename_i zero
    subst num
    simp only [AccuracyRep]
    grind
  · rename_i nonzero
    have hp : (0 : Rat) < (num : Rat) :=
      Rat.natCast_lt_natCast.mpr (Nat.pos_of_ne_zero nonzero)
    cases relation : compare (2 * num) den with
    | lt =>
      have bound := Rat.natCast_lt_natCast.mpr (Nat.compare_eq_lt.mp relation)
      simp only [Rat.natCast_mul, Rat.natCast_ofNat] at bound
      simp only [AccuracyRep]
      constructor
      · apply Rat.lt_of_mul_lt_mul_right (c := (den : Rat)) ?_ (Rat.le_of_lt hd)
        grind
      · apply Rat.lt_of_mul_lt_mul_right (c := (den : Rat)) ?_ (Rat.le_of_lt hd)
        grind
    | eq =>
      have bound := congrArg (fun n : Nat => (n : Rat)) (Nat.compare_eq_eq.mp relation)
      simp only [Rat.natCast_mul, Rat.natCast_ofNat] at bound
      simp only [AccuracyRep]
      grind
    | gt =>
      have bound := Rat.natCast_lt_natCast.mpr (Nat.compare_eq_gt.mp relation)
      simp only [Rat.natCast_mul, Rat.natCast_ofNat] at bound
      simp only [AccuracyRep]
      constructor
      · apply Rat.lt_of_mul_lt_mul_right (c := (den : Rat)) ?_ (Rat.le_of_lt hd)
        grind
      · apply Rat.lt_of_mul_lt_mul_right (c := (den : Rat)) ?_ (Rat.le_of_lt hd)
        grind

theorem quotient_accuracy_rep (num den : Nat) (positive : 0 < den) :
    AccuracyRep (num / den) (accuracyOfFraction (num % den) den)
      ((num : Rat) / (den : Rat)) := by
  have h := accuracyOfFraction_rep (num / den) (num % den) den positive (Nat.mod_lt _ positive)
  have hd : (den : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_lt_natCast.mpr positive)
  have division := congrArg (fun n : Nat => (n : Rat)) (Nat.div_add_mod num den)
  simp only [Rat.natCast_add, Rat.natCast_mul] at division
  have value : ((num / den : Nat) : Rat) + ((num % den : Nat) : Rat) / (den : Rat) =
      (num : Rat) / (den : Rat) := by grind
  rwa [value] at h

/-- Integral, denominator-scaled view of the model's half-unit error. -/
theorem fraction_round_scaled_bound (m num den : Nat) (proper : num < den) :
    2 * (m * den + num) ≤ 2 * (accuracyOfFraction num den).roundToNearestEven m * den + den ∧
      2 * (accuracyOfFraction num den).roundToNearestEven m * den ≤
        2 * (m * den + num) + den := by
  unfold accuracyOfFraction
  split
  · subst num
    simp only [Accuracy.roundToNearestEven, Nat.add_zero, Nat.mul_assoc]
    omega
  · cases relation : compare (2 * num) den with
    | lt =>
      have bound := Nat.compare_eq_lt.mp relation
      simp only [Accuracy.roundToNearestEven, Nat.mul_add, Nat.mul_assoc]
      omega
    | eq =>
      have bound := Nat.compare_eq_eq.mp relation
      have parity : m % 2 = 0 ∨ m % 2 = 1 := by omega
      rcases parity with parity | parity <;>
        simp only [Accuracy.roundToNearestEven, parity, Nat.add_zero,
          Nat.mul_add, Nat.add_mul, Nat.mul_assoc] <;> omega
    | gt =>
      have bound := Nat.compare_eq_gt.mp relation
      simp only [Accuracy.roundToNearestEven, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
      omega

def quotientMantissa (num den : Nat) : Nat :=
  (accuracyOfFraction (num % den) den).roundToNearestEven (num / den)

theorem quotientMantissa_scaled_bound (num den : Nat) (positive : 0 < den) :
    2 * num ≤ 2 * quotientMantissa num den * den + den ∧
      2 * quotientMantissa num den * den ≤ 2 * num + den := by
  have h := fraction_round_scaled_bound (num / den) (num % den) den (Nat.mod_lt _ positive)
  have value : num / den * den + num % den = num := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod num den
  simpa only [quotientMantissa, value] using h

theorem quotientMantissa_error (num den : Nat) (positive : 0 < den) :
    |(quotientMantissa num den : Rat) - (num : Rat) / (den : Rat)| ≤ 1 / 2 :=
  (quotient_accuracy_rep num den positive).round_abs

theorem quotientMantissa_scaled_error (num den : Nat) (positive : 0 < den)
    (unit : Rat) (nonnegative : 0 ≤ unit) :
    |(quotientMantissa num den : Rat) * unit - (num : Rat) / (den : Rat) * unit| ≤ unit / 2 :=
  (quotient_accuracy_rep num den positive).round_scaled unit nonnegative

theorem quotientMantissa_exact (num den : Nat) (divides : num % den = 0) :
    quotientMantissa num den = num / den := by
  simp [quotientMantissa, divides, accuracyOfFraction, Accuracy.roundToNearestEven]

theorem quotientMantissa_adjacent (num den : Nat) :
    num / den ≤ quotientMantissa num den ∧ quotientMantissa num den ≤ num / den + 1 :=
  nearestEven_adjacent _ _

theorem divCore_rounding (format : Format) (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) :
    let target := min (e₁ - e₂)
      (format.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂))
    let numerator := m₁ <<< (e₁ - e₂ - target).toNat
    let result := divCore format m₁ e₁ m₂ e₂
    result.2.2.roundToNearestEven result.1 = quotientMantissa numerator m₂ := by
  rfl

theorem divCore_rounding_scaled_bound (format : Format) (m₁ : Nat) (e₁ : Int)
    (m₂ : Nat) (positive : 0 < m₂) (e₂ : Int) :
    let target := min (e₁ - e₂)
      (format.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂))
    let numerator := m₁ <<< (e₁ - e₂ - target).toNat
    let result := divCore format m₁ e₁ m₂ e₂
    let rounded := result.2.2.roundToNearestEven result.1
    2 * numerator ≤ 2 * rounded * m₂ + m₂ ∧ 2 * rounded * m₂ ≤ 2 * numerator + m₂ :=
  quotientMantissa_scaled_bound _ _ positive

theorem divCore_rounding_error (format : Format) (m₁ : Nat) (e₁ : Int)
    (m₂ : Nat) (positive : 0 < m₂) (e₂ : Int) :
    let target := min (e₁ - e₂)
      (format.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂))
    let numerator := m₁ <<< (e₁ - e₂ - target).toNat
    let result := divCore format m₁ e₁ m₂ e₂
    let rounded := result.2.2.roundToNearestEven result.1
    let unit : Rat := (2 : Rat) ^ result.2.1
    |(rounded : Rat) * unit - (numerator : Rat) / (m₂ : Rat) * unit| ≤ unit / 2 :=
  quotientMantissa_scaled_error _ _ positive _ (Rat.le_of_lt (Rat.zpow_pos (by decide)))

theorem dyadic_shiftLeft (m : Nat) (e : Int) (n : Nat) :
    dyadicValue (m <<< n) (e - (n : Int)) = dyadicValue m e := by
  rw [dyadicValue_eq, dyadicValue_eq, Nat.shiftLeft_eq]
  simp only [Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_ofNat]
  have power := Rat.zpow_add (q := (2 : Rat)) (by decide) (n : Int) (e - (n : Int))
  have exponent : (n : Int) + (e - (n : Int)) = e := by omega
  rw [exponent, Rat.zpow_natCast] at power
  rw [Rat.mul_assoc, ← power]

theorem decreaseExponent_value (m : Nat) (e target : Int) :
    dyadicValue (decreaseExponent m e target).1 (decreaseExponent m e target).2 = dyadicValue m e :=
  dyadic_shiftLeft m e (e - target).toNat

private theorem dyadic_div (m₁ m₂ : Nat) (e₁ e₂ : Int) (positive : 0 < m₂) :
    dyadicValue m₁ (e₁ - e₂) / (m₂ : Rat) = dyadicValue m₁ e₁ / dyadicValue m₂ e₂ := by
  simp only [dyadicValue_eq]
  have power := Rat.zpow_add (q := (2 : Rat)) (by decide) (e₁ - e₂) e₂
  have exponent : e₁ - e₂ + e₂ = e₁ := by omega
  rw [exponent] at power
  have hm : (m₂ : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_lt_natCast.mpr positive)
  have hp : (2 : Rat) ^ e₂ ≠ 0 := Rat.ne_of_gt (Rat.zpow_pos (by decide))
  grind

theorem divCore_unrounded_value (format : Format) (m₁ : Nat) (e₁ : Int)
    (m₂ : Nat) (positive : 0 < m₂) (e₂ : Int) :
    let target := min (e₁ - e₂)
      (format.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂))
    let numerator := m₁ <<< (e₁ - e₂ - target).toNat
    (numerator : Rat) / (m₂ : Rat) * (2 : Rat) ^ target = dyadicValue m₁ e₁ / dyadicValue m₂ e₂ := by
  dsimp
  let target := min (e₁ - e₂)
    (format.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂))
  have target_le : target ≤ e₁ - e₂ := Int.min_le_left _ _
  have shift : ((e₁ - e₂ - target).toNat : Int) = e₁ - e₂ - target := by omega
  have exponent : e₁ - e₂ - ((e₁ - e₂ - target).toNat : Int) = target := by omega
  have shifted := dyadic_shiftLeft m₁ (e₁ - e₂) (e₁ - e₂ - target).toNat
  rw [exponent] at shifted
  have quotient := dyadic_div m₁ m₂ e₁ e₂ positive
  rw [dyadicValue_eq] at shifted
  change ((m₁ <<< (e₁ - e₂ - target).toNat : Nat) : Rat) / (m₂ : Rat) * (2 : Rat) ^ target = _
  grind

theorem divCore_initial_round_error (format : Format) (m₁ : Nat) (e₁ : Int)
    (m₂ : Nat) (positive : 0 < m₂) (e₂ : Int) :
    let result := divCore format m₁ e₁ m₂ e₂
    let rounded := result.2.2.roundToNearestEven result.1
    |dyadicValue rounded result.2.1 - dyadicValue m₁ e₁ / dyadicValue m₂ e₂| ≤
      (2 : Rat) ^ result.2.1 / 2 := by
  have rounded := divCore_rounding_error format m₁ e₁ m₂ positive e₂
  have value := divCore_unrounded_value format m₁ e₁ m₂ positive e₂
  simp only [divCore] at rounded ⊢
  rw [value] at rounded
  simpa only [dyadicValue_eq] using rounded

theorem divCore_accuracy_rep (format : Format) (m₁ : Nat) (e₁ : Int)
    (m₂ : Nat) (positive : 0 < m₂) (e₂ : Int) :
    let result := divCore format m₁ e₁ m₂ e₂
    AccuracyRep result.1 result.2.2
      ((dyadicValue m₁ e₁ / dyadicValue m₂ e₂) / (2 : Rat) ^ result.2.1) := by
  have representation := quotient_accuracy_rep
    (m₁ <<< (e₁ - e₂ - min (e₁ - e₂)
      (format.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂))).toNat) m₂ positive
  have value := divCore_unrounded_value format m₁ e₁ m₂ positive e₂
  dsimp only at value
  simp only [divCore]
  have unit : (2 : Rat) ^ min (e₁ - e₂)
      (format.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂)) ≠ 0 :=
    Rat.ne_of_gt (Rat.zpow_pos (by decide))
  have rescaled : (dyadicValue m₁ e₁ / dyadicValue m₂ e₂) /
      (2 : Rat) ^ min (e₁ - e₂)
        (format.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂)) =
      ((m₁ <<< (e₁ - e₂ - min (e₁ - e₂)
        (format.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂))).toNat : Nat) : Rat) /
        (m₂ : Rat) := by grind
  rwa [rescaled]

end Floating.Rounding
