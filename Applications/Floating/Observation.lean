import Init.Data.Dyadic.Basic
import Init.Data.Float

/-!
# Finite observations of the pinned floating model

Core `Dyadic` supplies exact signed powers of two. The observation below interprets
the actual logical Float/Float32 unpacking, identifying signed zeros numerically
and rejecting NaN and infinities. It makes no native or NaN-payload preservation
claim. The selected source correspondence belongs to local ticket 1012.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Floating.Observation

open Float.Model

/-- Core precision has the opposite sign from a mantissa's binary exponent. -/
def dyadicValue (mantissa : Nat) (exponent : Int) : Rat :=
  (Dyadic.ofIntWithPrec (mantissa : Int) (-exponent)).toRat

theorem dyadicValue_eq (mantissa : Nat) (exponent : Int) :
    dyadicValue mantissa exponent = (mantissa : Rat) * (2 : Rat) ^ exponent := by
  rw [dyadicValue, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
  simp only [Int.neg_neg, Rat.intCast_natCast]

theorem dyadicValue_ofNat (mantissa exponent : Nat) :
    dyadicValue mantissa (.ofNat exponent) = (mantissa : Rat) * (2 : Rat) ^ exponent := by
  rw [dyadicValue_eq]
  rfl

theorem dyadicValue_negSucc (mantissa exponent : Nat) :
    dyadicValue mantissa (.negSucc exponent) =
      (mantissa : Rat) / (2 : Rat) ^ (exponent + 1) := by
  rw [dyadicValue_eq]
  rfl

def unpack : UnpackedFloat → Option Rat
  | .infinity _ => none
  | .notANumber => none
  | .zero _ => some 0
  | .finite sign mantissa exponent _ =>
      some (match sign with
        | .positive => dyadicValue mantissa exponent
        | .negative => -(dyadicValue mantissa exponent))

def decode64 (value : Float) : Option Rat := unpack value.toModel.unpack

def decode32 (value : Float32) : Option Rat := unpack value.toModel.unpack

theorem unpack_isSome (value : UnpackedFloat) :
    (unpack value).isSome = value.isFinite := by
  cases value <;> rfl

theorem decode64_isFinite (value : Float) :
    (decode64 value).isSome = value.isFinite := unpack_isSome value.toModel.unpack

theorem decode32_isFinite (value : Float32) :
    (decode32 value).isSome = value.isFinite := unpack_isSome value.toModel.unpack

theorem decode64_isSome_iff (value : Float) :
    (decode64 value).isSome = true ↔ value.isFinite = true := by rw [decode64_isFinite]

theorem decode32_isSome_iff (value : Float32) :
    (decode32 value).isSome = true ↔ value.isFinite = true := by rw [decode32_isFinite]

theorem unpack_none_iff (value : UnpackedFloat) :
    unpack value = none ↔ value.isNaN = true ∨ value.isInf = true := by
  cases value <;> simp [unpack, UnpackedFloat.isNaN, UnpackedFloat.isInf]

theorem decode64_none_iff (value : Float) :
    decode64 value = none ↔ value.isNaN = true ∨ value.isInf = true :=
  unpack_none_iff value.toModel.unpack

theorem decode32_none_iff (value : Float32) :
    decode32 value = none ↔ value.isNaN = true ∨ value.isInf = true :=
  unpack_none_iff value.toModel.unpack

theorem decode64_zero : decode64 (0 : Float) = some 0 := by decide +kernel

theorem decode32_zero : decode32 (0 : Float32) = some 0 := by decide +kernel

/-- The source division constant is exact in both formats. -/
theorem decode64_ten : decode64 (10 : Float) = some 10 := by decide +kernel

theorem decode32_ten : decode32 (10 : Float32) = some 10 := by decide +kernel

/-- The ten source digits are exact; arbitrary Nat conversions need not be. -/
theorem decode64_digit (digit : Nat) (proper : digit < 10) :
    decode64 digit.toFloat = some (digit : Rat) := by
  have checked : ∀ i : Fin 10, decode64 i.val.toFloat = some (i.val : Rat) := by
    decide +kernel
  exact checked ⟨digit, proper⟩

theorem decode32_digit (digit : Nat) (proper : digit < 10) :
    decode32 digit.toFloat32 = some (digit : Rat) := by
  have checked : ∀ i : Fin 10, decode32 i.val.toFloat32 = some (i.val : Rat) := by
    decide +kernel
  exact checked ⟨digit, proper⟩

theorem signed_zero64 :
    decode64 (0 : Float) = some 0 ∧ decode64 (-(0 : Float)) = some 0 ∧
    (0 : Float) ≠ -(0 : Float) ∧ ((0 : Float) == -(0 : Float)) = true := by
  decide +kernel

theorem signed_zero32 :
    decode32 (0 : Float32) = some 0 ∧ decode32 (-(0 : Float32)) = some 0 ∧
    (0 : Float32) ≠ -(0 : Float32) ∧ ((0 : Float32) == -(0 : Float32)) = true := by
  decide +kernel

theorem exceptional_values64 :
    decode64 ((0 : Float) / 0) = none ∧ decode64 ((1 : Float) / 0) = none ∧
    decode64 ((-1 : Float) / 0) = none := by
  decide +kernel

theorem exceptional_values32 :
    decode32 ((0 : Float32) / 0) = none ∧ decode32 ((1 : Float32) / 0) = none ∧
    decode32 ((-1 : Float32) / 0) = none := by
  decide +kernel

end Floating.Observation
