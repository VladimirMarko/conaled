import Applications.Floating.Rounding.Shift

/-!
# Exact values supplied to floating rounding

These bridges expose finite nonnegative operands, exponent-aligned positive
addition, and the actual division core's precision invariant. They concern the
input to rounding; formatted arithmetic and packing have further obligations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Floating.ArithmeticCore

open Float.Model Float.Model.UnpackedFloat
open Floating.Observation (dyadicValue dyadicValue_eq)

theorem dyadic_positive (m : Nat) (positive : 0 < m) (e : Int) : 0 < dyadicValue m e := by
  rw [dyadicValue_eq]
  exact Rat.mul_pos (Rat.natCast_lt_natCast.mpr positive) (Rat.zpow_pos (by decide))

theorem nonnegative_unpacked_cases (value : UnpackedFloat) (q : Rat)
    (observed : Observation.unpack value = some q) (nonnegative : 0 ≤ q) :
    (∃ sign, value = .zero sign ∧ q = 0) ∨
      (∃ (m : Nat) (e : Int) (positive : 0 < m),
        value = .finite .positive m e positive ∧ q = dyadicValue m e) := by
  cases value with
  | notANumber => simp [Observation.unpack] at observed
  | infinity sign => simp [Observation.unpack] at observed
  | zero sign =>
    have same : q = 0 := (Option.some.inj observed).symm
    exact Or.inl ⟨sign, rfl, same⟩
  | finite sign m e positive =>
    cases sign with
    | positive => exact Or.inr ⟨m, e, positive, rfl, (Option.some.inj observed).symm⟩
    | negative =>
      have same : q = -dyadicValue m e := (Option.some.inj observed).symm
      have strictlyPositive := dyadic_positive m positive e
      linarith

theorem aligned_positive_sum_value (m₁ m₂ : Nat) (e₁ e₂ : Int) :
    let exponent := min e₁ e₂
    let left := decreaseExponent m₁ e₁ exponent
    let right := decreaseExponent m₂ e₂ exponent
    dyadicValue (left.1 + right.1) exponent = dyadicValue m₁ e₁ + dyadicValue m₂ e₂ := by
  dsimp only
  have left := Rounding.decreaseExponent_value m₁ e₁ (min e₁ e₂)
  have right := Rounding.decreaseExponent_value m₂ e₂ (min e₁ e₂)
  have leftExponent : (decreaseExponent m₁ e₁ (min e₁ e₂)).2 = min e₁ e₂ := by
    have := Int.min_le_left e₁ e₂
    simp only [decreaseExponent]
    omega
  have rightExponent : (decreaseExponent m₂ e₂ (min e₁ e₂)).2 = min e₁ e₂ := by
    have := Int.min_le_right e₁ e₂
    simp only [decreaseExponent]
    omega
  rw [leftExponent] at left
  rw [rightExponent] at right
  simp only [dyadicValue_eq, Nat.cast_add, add_mul] at *
  rw [left, right]

/-- Actual positive addition rounds the exact sum at the common input exponent. -/
theorem positive_add_formula (format : Format) (m₁ m₂ : Nat) (e₁ e₂ : Int)
    (positive₁ : 0 < m₁) (positive₂ : 0 < m₂) :
    UnpackedFloat.add format (.finite .positive m₁ e₁ positive₁)
      (.finite .positive m₂ e₂ positive₂) =
      round format .positive
        ((decreaseExponent m₁ e₁ (min e₁ e₂)).1 +
          (decreaseExponent m₂ e₂ (min e₁ e₂)).1) (min e₁ e₂) := by
  have shiftedPositive : 0 < (decreaseExponent m₁ e₁ (min e₁ e₂)).1 := by
    simp only [decreaseExponent, Nat.shiftLeft_eq]
    exact Nat.mul_pos positive₁ (Nat.two_pow_pos _)
  have sumPositive : (0 : Int) < ((decreaseExponent m₁ e₁ (min e₁ e₂)).1 : Int) +
      ((decreaseExponent m₂ e₂ (min e₁ e₂)).1 : Int) := by omega
  simp only [UnpackedFloat.add, Sign.apply, normalize]
  rw [Int.compare_eq_gt.mpr sumPositive, ← Int.natCast_add, Int.toNat_natCast]

/-- The actual division shift supplies enough bits above the subnormal floor. -/
theorem divCore_precision (format : Format) (m₁ : Nat) (positive₁ : 0 < m₁) (e₁ : Int)
    (m₂ : Nat) (positive₂ : 0 < m₂) (e₂ : Int) :
    let result := divCore format m₁ e₁ m₂ e₂
    result.2.1 ≤ format.minExponent ∨ 2 ^ (format.mantissaBits - 1) ≤ result.1 := by
  let target := min (e₁ - e₂)
    (format.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂))
  let shift := (e₁ - e₂ - target).toNat
  change target ≤ format.minExponent ∨ 2 ^ (format.mantissaBits - 1) ≤ (m₁ <<< shift) / m₂
  by_cases atFloor : target ≤ format.minExponent
  · exact Or.inl atFloor
  · apply Or.inr
    have targetLeft : target ≤ e₁ - e₂ := Int.min_le_left _ _
    have targetRight : target ≤ format.targetExponent
        (totalExponent m₁ e₁ - totalExponent m₂ e₂) := Int.min_le_right _ _
    have castShift : (shift : Int) = e₁ - e₂ - target := by dsimp only [shift]; omega
    have bitsPositive : 0 < format.mantissaBits := by simp only [Format.mantissaBits]; omega
    have enough : format.mantissaBits + m₂.log2 ≤ m₁.log2 + shift := by
      simp only [Format.targetExponent, totalExponent] at targetRight
      omega
    have lower : 2 ^ m₁.log2 ≤ m₁ := Nat.log2_self_le (by omega)
    have upper : m₂ < 2 ^ (m₂.log2 + 1) := Nat.lt_log2_self
    have numerator : 2 ^ (format.mantissaBits + m₂.log2) ≤ m₁ * 2 ^ shift := by
      calc
        _ ≤ 2 ^ (m₁.log2 + shift) := Nat.pow_le_pow_right (by decide) enough
        _ = 2 ^ m₁.log2 * 2 ^ shift := Nat.pow_add _ _ _
        _ ≤ m₁ * 2 ^ shift := Nat.mul_le_mul_right _ lower
    have power : 2 ^ (format.mantissaBits - 1) * 2 ^ (m₂.log2 + 1) =
        2 ^ (format.mantissaBits + m₂.log2) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have scaled : 2 ^ (format.mantissaBits - 1) * m₂ ≤ m₁ * 2 ^ shift := by
      calc
        _ ≤ 2 ^ (format.mantissaBits - 1) * 2 ^ (m₂.log2 + 1) :=
          Nat.mul_le_mul_left _ (Nat.le_of_lt upper)
        _ = 2 ^ (format.mantissaBits + m₂.log2) := power
        _ ≤ m₁ * 2 ^ shift := numerator
    rw [Nat.shiftLeft_eq]
    exact (Nat.le_div_iff_mul_le positive₂).mpr scaled

end Floating.ArithmeticCore
