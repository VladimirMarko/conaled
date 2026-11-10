import Applications.Floating.Packing

/-!
# Exact carry normalization after nearest-even rounding

The existing core first shifts and rounds an extended mantissa, then performs
one further exact shift if rounding carried into a new bit. That second shift
preserves the first rounded dyadic value. Canonicality needs the incoming
alignment invariant; the positive-value and numerical-error laws do not.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Floating.Rounding

open Float.Model Float.Model.UnpackedFloat
open Floating.Observation (dyadicValue dyadicValue_eq)
open Floating.Packing (Canonical)

/-- The input has enough significant bits unless it is at the subnormal floor. -/
def Aligned (format : Format) (m : Nat) (e : Int) : Prop :=
  e ≤ format.minExponent ∨ 2 ^ (format.mantissaBits - 1) ≤ m

theorem target_shift_exponent (format : Format) (m : Nat) (e : Int) (a : Accuracy) :
    (shiftToTargetExponent format m e a).2 =
      max e (max (m.log2 + 1 + e - (format.mantissaBits : Int)) format.minExponent) :=
  shiftToExponent_exponent m e a _

theorem target_shift_mantissa (format : Format) (m : Nat) (e : Int) (a : Accuracy) :
    (shiftToTargetExponent format m e a).1.mantissa =
      m / 2 ^ (format.targetExponent (totalExponent m e) - e).toNat :=
  shiftToExponent_mantissa m e a _

theorem target_shift_width (format : Format) (m : Nat) (e : Int) (a : Accuracy) :
    (shiftToTargetExponent format m e a).1.mantissa < 2 ^ format.mantissaBits := by
  rw [target_shift_mantissa]
  let n := (format.targetExponent (totalExponent m e) - e).toNat
  have enough : m.log2 + 1 ≤ format.mantissaBits + n := by
    dsimp [n, Format.targetExponent, totalExponent]
    omega
  have mantissa := Nat.lt_log2_self (n := m)
  have power := Nat.pow_le_pow_right (by decide : 0 < 2) enough
  have upper : m < 2 ^ format.mantissaBits * 2 ^ n := by
    rw [← Nat.pow_add]
    exact Nat.lt_of_lt_of_le mantissa power
  exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2))).mpr upper

theorem target_shift_min (format : Format) (m : Nat) (e : Int) (a : Accuracy) :
    format.minExponent ≤ (shiftToTargetExponent format m e a).2 := by
  rw [target_shift_exponent]
  omega

theorem target_shift_normal_lower (format : Format) (m : Nat) (e : Int) (a : Accuracy)
    (aligned : Aligned format m e)
    (aboveFloor : format.minExponent < (shiftToTargetExponent format m e a).2) :
    2 ^ (format.mantissaBits - 1) ≤ (shiftToTargetExponent format m e a).1.mantissa := by
  let n := (format.targetExponent (totalExponent m e) - e).toNat
  have bits : 2 ≤ format.mantissaBits := by
    have := format.hm
    simp only [Format.mantissaBits]
    omega
  rw [target_shift_mantissa]
  change _ ≤ m / 2 ^ n
  rw [target_shift_exponent] at aboveFloor
  by_cases zero : n = 0
  · have exponent : format.minExponent < e := by
      dsimp [n, Format.targetExponent, totalExponent] at zero
      omega
    rcases aligned with floor | lower
    · omega
    · simpa only [zero, Nat.pow_zero, Nat.div_one] using lower
  · have shift : n + format.mantissaBits - 1 = m.log2 := by
      dsimp [n, Format.targetExponent, totalExponent] at *
      omega
    have nonzero : m ≠ 0 := by
      intro zero
      simp only [zero, Nat.log2_zero] at shift
      omega
    apply (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide : 0 < 2))).mpr
    have exponent : format.mantissaBits - 1 + n = m.log2 := by omega
    rw [← Nat.pow_add, exponent]
    exact Nat.log2_self_le nonzero

theorem target_shift_of_width (format : Format) (m : Nat) (e : Int) (a : Accuracy)
    (width : m < 2 ^ format.mantissaBits) (floor : format.minExponent ≤ e) :
    shiftToTargetExponent format m e a = (ExtendedMantissa.ofMantissaAndAccuracy m a, e) := by
  have bits : 2 ≤ format.mantissaBits := by
    have := format.hm
    simp only [Format.mantissaBits]
    omega
  have mantissa : m.log2 + 1 ≤ format.mantissaBits := by
    by_cases zero : m = 0
    · simp only [zero, Nat.log2_zero]; omega
    · have := (Nat.log2_lt zero).mpr width
      omega
  have shift : (format.targetExponent (totalExponent m e) - e).toNat = 0 := by
    simp only [Format.targetExponent, totalExponent]
    omega
  simp only [shiftToTargetExponent, shiftToExponent, shift]
  change (ExtendedMantissa.ofMantissaAndAccuracy m a, e + 0) = _
  rw [Int.add_zero]

theorem target_shift_carry (format : Format) (e : Int) (floor : format.minExponent ≤ e) :
    shiftToTargetExponent format (2 ^ format.mantissaBits) e .exact =
      (⟨2 ^ (format.mantissaBits - 1), false, false⟩, e + 1) := by
  have bits : 2 ≤ format.mantissaBits := by
    have := format.hm
    simp only [Format.mantissaBits]
    omega
  have shift : (format.targetExponent (totalExponent (2 ^ format.mantissaBits) e) - e).toNat = 1 := by
    simp only [Format.targetExponent, totalExponent, Nat.log2_two_pow]
    omega
  have power : 2 ^ format.mantissaBits = 2 ^ (format.mantissaBits - 1) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  simp only [shiftToTargetExponent, shiftToExponent, shift]
  change (ExtendedMantissa.shiftRightOne ⟨2 ^ format.mantissaBits, false, false⟩, e + 1) = _
  simp [ExtendedMantissa.shiftRightOne, power]

/-- The actual second shift is exact, including the carry into a new mantissa bit. -/
theorem carry_shift_value (format : Format) (m : Nat) (e : Int)
    (width : m ≤ 2 ^ format.mantissaBits) (floor : format.minExponent ≤ e) :
    dyadicValue (shiftToTargetExponent format m e .exact).1.mantissa
      (shiftToTargetExponent format m e .exact).2 = dyadicValue m e := by
  rcases Nat.eq_or_lt_of_le width with carry | below
  · rw [carry, target_shift_carry format e floor]
    have bits : 2 ≤ format.mantissaBits := by
      have := format.hm
      simp only [Format.mantissaBits]
      omega
    have shift : (2 ^ (format.mantissaBits - 1)) <<< 1 = 2 ^ format.mantissaBits := by
      rw [Nat.shiftLeft_eq, ← Nat.pow_add]
      congr 1
      omega
    have value := dyadic_shiftLeft (2 ^ (format.mantissaBits - 1)) (e + 1) 1
    have exponent : e + 1 - (1 : Nat) = e := by omega
    rw [shift, exponent] at value
    exact value.symm
  · rw [target_shift_of_width format m e .exact below floor]
    rfl

theorem canonical_of_width (format : Format) (m : Nat) (e : Int)
    (positive : 0 < m) (width : m < 2 ^ format.mantissaBits) (floor : format.minExponent ≤ e)
    (normal : format.minExponent < e → 2 ^ (format.mantissaBits - 1) ≤ m) :
    e = format.targetExponent (totalExponent m e) := by
  have upper := (Nat.log2_lt (by omega : m ≠ 0)).mpr width
  have bits : 2 ≤ format.mantissaBits := by
    have := format.hm
    simp only [Format.mantissaBits]
    omega
  by_cases atFloor : e = format.minExponent
  · simp only [Format.targetExponent, totalExponent]
    omega
  · have lower := (Nat.le_log2 (by omega : m ≠ 0)).mpr (normal (by omega))
    simp only [Format.targetExponent, totalExponent]
    omega

theorem carry_shift_canonical (format : Format) (m : Nat) (e : Int)
    (width : m ≤ 2 ^ format.mantissaBits) (floor : format.minExponent ≤ e)
    (normal : format.minExponent < e → 2 ^ (format.mantissaBits - 1) ≤ m)
    (positive : 0 < (shiftToTargetExponent format m e .exact).1.mantissa) :
    (shiftToTargetExponent format m e .exact).2 =
      format.targetExponent (totalExponent (shiftToTargetExponent format m e .exact).1.mantissa
        (shiftToTargetExponent format m e .exact).2) := by
  rcases Nat.eq_or_lt_of_le width with carry | below
  · rw [carry, target_shift_carry format e floor]
    simp only [Format.targetExponent, totalExponent, Nat.log2_two_pow]
    have bits : 2 ≤ format.mantissaBits := by
      have := format.hm
      simp only [Format.mantissaBits]
      omega
    omega
  · rw [target_shift_of_width format m e .exact below floor] at positive ⊢
    exact canonical_of_width format m e positive below floor normal

theorem rounded_shift_width (format : Format) (m : Nat) (e : Int) (a : Accuracy) :
    (shiftToTargetExponent format m e a).1.roundedMantissa ≤ 2 ^ format.mantissaBits := by
  have width := target_shift_width format m e a
  have rounded := nearestEven_adjacent (shiftToTargetExponent format m e a).1.mantissa
    (shiftToTargetExponent format m e a).1.accuracy
  change _ ≤ _ ∧ (shiftToTargetExponent format m e a).1.roundedMantissa ≤ _ at rounded
  omega

theorem rounded_shift_normal_lower (format : Format) (m : Nat) (e : Int) (a : Accuracy)
    (aligned : Aligned format m e)
    (aboveFloor : format.minExponent < (shiftToTargetExponent format m e a).2) :
    2 ^ (format.mantissaBits - 1) ≤ (shiftToTargetExponent format m e a).1.roundedMantissa := by
  have lower := target_shift_normal_lower format m e a aligned aboveFloor
  have rounded := nearestEven_adjacent (shiftToTargetExponent format m e a).1.mantissa
    (shiftToTargetExponent format m e a).1.accuracy
  change (shiftToTargetExponent format m e a).1.mantissa ≤
    (shiftToTargetExponent format m e a).1.roundedMantissa ∧ _ at rounded
  omega

theorem roundWithAccuracy_canonical (format : Format) (sign : Sign) (m : Nat) (e : Int)
    (a : Accuracy) (aligned : Aligned format m e) :
    Canonical format (roundWithAccuracy format sign m e a) := by
  have width := rounded_shift_width format m e a
  have floor := target_shift_min format m e a
  have normal := rounded_shift_normal_lower format m e a aligned
  cases firstShift : shiftToTargetExponent format m e a with
  | mk extended exponent =>
    simp only [firstShift] at width floor normal
    have canonical := carry_shift_canonical format extended.roundedMantissa exponent width floor normal
    cases secondShift : shiftToTargetExponent format extended.roundedMantissa exponent .exact with
    | mk finalExtended finalExponent =>
      simp only [secondShift] at canonical
      simp only [roundWithAccuracy, firstShift, secondShift]
      split
      · trivial
      · rename_i nonzero
        exact canonical (Nat.pos_of_ne_zero nonzero)

theorem roundWithAccuracy_positive_value (format : Format) (m : Nat) (e : Int) (a : Accuracy) :
    Observation.unpack (roundWithAccuracy format .positive m e a) =
      some (dyadicValue (shiftToTargetExponent format m e a).1.roundedMantissa
        (shiftToTargetExponent format m e a).2) := by
  have width := rounded_shift_width format m e a
  have floor := target_shift_min format m e a
  have value := carry_shift_value format _ _ width floor
  cases firstShift : shiftToTargetExponent format m e a with
  | mk extended exponent =>
    simp only [firstShift] at value
    cases secondShift : shiftToTargetExponent format extended.roundedMantissa exponent .exact with
    | mk finalExtended finalExponent =>
      simp only [secondShift] at value
      simp only [roundWithAccuracy, firstShift, secondShift]
      split
      · rename_i zero
        rw [zero, dyadicValue_eq] at value
        have observedZero : dyadicValue extended.roundedMantissa exponent = 0 := by
          change (0 : Rat) * (2 : Rat) ^ finalExponent =
            dyadicValue extended.roundedMantissa exponent at value
          rw [zero_mul] at value
          exact value.symm
        simp only [Observation.unpack, observedZero]
      · simp only [Observation.unpack, value]

theorem roundWithAccuracy_error (format : Format) (m : Nat) (e : Int)
    (a : Accuracy) (x : Rat) (represented : AccuracyRep m a x) :
    ∃ value, Observation.unpack (roundWithAccuracy format .positive m e a) = some value ∧
      |value - x * (2 : Rat) ^ e| ≤ (2 : Rat) ^ (shiftToTargetExponent format m e a).2 / 2 := by
  refine ⟨_, roundWithAccuracy_positive_value format m e a, ?_⟩
  rw [dyadicValue_eq]
  exact shiftToTargetExponent_error format m e a x represented

theorem decreaseExponent_aligned (format : Format) (m : Nat) (e : Int) (positive : 0 < m) :
    Aligned format (decreaseExponent m e (format.targetExponent (totalExponent m e))).1
      (decreaseExponent m e (format.targetExponent (totalExponent m e))).2 := by
  let target := format.targetExponent (totalExponent m e)
  let shift := (e - target).toNat
  change e - (shift : Int) ≤ format.minExponent ∨
    2 ^ (format.mantissaBits - 1) ≤ m <<< shift
  by_cases atFloor : e - (shift : Int) ≤ format.minExponent
  · exact Or.inl atFloor
  · right
    have bits : 2 ≤ format.mantissaBits := by
      have := format.hm
      simp only [Format.mantissaBits]
      omega
    have enough : format.mantissaBits - 1 ≤ m.log2 + shift := by
      dsimp [shift, target, Format.targetExponent, totalExponent] at *
      omega
    have lower := Nat.log2_self_le (Nat.ne_of_gt positive)
    have power := Nat.pow_le_pow_right (by decide : 0 < 2) enough
    rw [Nat.pow_add] at power
    rw [Nat.shiftLeft_eq]
    exact Nat.le_trans power (Nat.mul_le_mul_right _ lower)

theorem round_canonical_of_pos (format : Format) (sign : Sign) (m : Nat) (e : Int)
    (positive : 0 < m) : Canonical format (round format sign m e) := by
  have aligned := decreaseExponent_aligned format m e positive
  unfold round
  cases decreased : decreaseExponent m e (format.targetExponent (totalExponent m e)) with
  | mk mantissa exponent =>
    simp only [decreased] at aligned
    simp only [decreased]
    exact roundWithAccuracy_canonical format sign mantissa exponent .exact aligned

theorem round_positive_value (format : Format) (m : Nat) (e : Int) :
    let target := format.targetExponent (totalExponent m e)
    let decreased := decreaseExponent m e target
    Observation.unpack (round format .positive m e) =
      some (dyadicValue (shiftToTargetExponent format decreased.1 decreased.2 .exact).1.roundedMantissa
        (shiftToTargetExponent format decreased.1 decreased.2 .exact).2) := by
  simp only [round]
  cases decreased : decreaseExponent m e (format.targetExponent (totalExponent m e)) with
  | mk mantissa exponent => exact roundWithAccuracy_positive_value format mantissa exponent .exact

theorem round_error (format : Format) (m : Nat) (e : Int) :
    let target := format.targetExponent (totalExponent m e)
    let decreased := decreaseExponent m e target
    ∃ value, Observation.unpack (round format .positive m e) = some value ∧
      |value - dyadicValue m e| ≤
        (2 : Rat) ^ (shiftToTargetExponent format decreased.1 decreased.2 .exact).2 / 2 := by
  have value := decreaseExponent_value m e (format.targetExponent (totalExponent m e))
  cases decreased : decreaseExponent m e (format.targetExponent (totalExponent m e)) with
  | mk mantissa exponent =>
    simp only [decreased] at value
    have represented : AccuracyRep mantissa .exact (mantissa : Rat) := rfl
    have error := roundWithAccuracy_error format mantissa exponent .exact (mantissa : Rat) represented
    rw [← dyadicValue_eq, value] at error
    simpa only [round, decreased] using error

end Floating.Rounding
