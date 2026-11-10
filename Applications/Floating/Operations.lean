import Applications.Floating.Rounding.Bounds

/-!
# Bounded actual floating addition and division by ten

The public format specializations require a proper digit and successful input
observation in the stated range. Alignment, canonicality, the rounding unit and
absence of overflow follow from the actual pinned operations. Closed ranges
include both signed zeros and subnormal values.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Floating.Operations

open Float.Model Float.Model.UnpackedFloat
open Floating.Observation (dyadicValue)
open Floating.Rounding Floating.Packing Floating.ArithmeticCore

theorem unpacked_add_bounds (format : Format) (left right : UnpackedFloat) (qa qb : Rat)
    (observedLeft : Observation.unpack left = some qa)
    (observedRight : Observation.unpack right = some qb)
    (nonnegativeLeft : 0 ≤ qa) (nonnegativeRight : 0 ≤ qb) (upper : qa + qb ≤ 10)
    (canonicalLeft : Canonical format left) (canonicalRight : Canonical format right)
    (E : Int) (exponentBound : max (4 - (format.mantissaBits : Int)) format.minExponent ≤ E)
    (nonpositive : E ≤ 0) :
    ∃ value, Observation.unpack (UnpackedFloat.add format left right) = some value ∧
      0 ≤ value ∧ value ≤ 10 ∧ |value - (qa + qb)| ≤ (2 : Rat) ^ E / 2 ∧
      Canonical format (UnpackedFloat.add format left right) := by
  have halfUnit : (0 : Rat) ≤ (2 : Rat) ^ E / 2 :=
    div_nonneg (le_of_lt (zpow_pos (by norm_num : (0 : Rat) < 2) E)) (by norm_num)
  rcases nonnegative_unpacked_cases left qa observedLeft nonnegativeLeft with
    ⟨leftSign, rfl, rfl⟩ | ⟨leftM, leftE, leftPositive, rfl, rfl⟩
  · rcases nonnegative_unpacked_cases right qb observedRight nonnegativeRight with
      ⟨rightSign, rfl, rfl⟩ | ⟨rightM, rightE, rightPositive, rfl, rfl⟩
    · refine ⟨0, ?_, by norm_num, by norm_num, ?_, ?_⟩
      · simp only [UnpackedFloat.add]
        split <;> rfl
      · simpa only [zero_add, sub_self, abs_zero] using halfUnit
      · simp only [UnpackedFloat.add]
        split <;> trivial
    · refine ⟨dyadicValue rightM rightE, rfl, nonnegativeRight, ?_, ?_, canonicalRight⟩
      · simpa only [zero_add] using upper
      · simpa only [zero_add, sub_self, abs_zero] using halfUnit
  · rcases nonnegative_unpacked_cases right qb observedRight nonnegativeRight with
      ⟨rightSign, rfl, rfl⟩ | ⟨rightM, rightE, rightPositive, rfl, rfl⟩
    · refine ⟨dyadicValue leftM leftE, rfl, nonnegativeLeft, ?_, ?_, canonicalLeft⟩
      · simpa only [add_zero] using upper
      · simpa only [add_zero, sub_self, abs_zero] using halfUnit
    · let m := (decreaseExponent leftM leftE (min leftE rightE)).1 +
        (decreaseExponent rightM rightE (min leftE rightE)).1
      have positive : 0 < m := by
        have shifted : 0 < (decreaseExponent leftM leftE (min leftE rightE)).1 := by
          simp only [decreaseExponent, Nat.shiftLeft_eq]
          exact Nat.mul_pos leftPositive (Nat.two_pow_pos _)
        dsimp only [m]
        omega
      have preserved := aligned_positive_sum_value leftM rightM leftE rightE
      change dyadicValue m (min leftE rightE) =
        dyadicValue leftM leftE + dyadicValue rightM rightE at preserved
      have result := round_bounds format m (min leftE rightE) positive 10 4 E
        (by rw [preserved]; exact upper) (by norm_num) exponentBound nonpositive
      rw [positive_add_formula format leftM rightM leftE rightE leftPositive rightPositive]
      rw [preserved] at result
      exact result

/-- Division constructs its own alignment; operand canonicality is unnecessary. -/
theorem unpacked_divTen_bounds (format : Format) (numerator denominator : UnpackedFloat)
    (q : Rat) (observedNumerator : Observation.unpack numerator = some q)
    (observedTen : Observation.unpack denominator = some 10) (nonnegative : 0 ≤ q)
    (upper : q ≤ 10) (E : Int)
    (exponentBound : max (1 - (format.mantissaBits : Int)) format.minExponent ≤ E)
    (nonpositive : E ≤ 0) :
    ∃ value, Observation.unpack (UnpackedFloat.div format numerator denominator) = some value ∧
      0 ≤ value ∧ value ≤ 1 ∧ |value - q / 10| ≤ (2 : Rat) ^ E / 2 ∧
      Canonical format (UnpackedFloat.div format numerator denominator) := by
  have halfUnit : (0 : Rat) ≤ (2 : Rat) ^ E / 2 :=
    div_nonneg (le_of_lt (zpow_pos (by norm_num : (0 : Rat) < 2) E)) (by norm_num)
  rcases nonnegative_unpacked_cases denominator 10 observedTen (by norm_num) with
    ⟨sign, same, zero⟩ | ⟨denM, denE, denPositive, rfl, ten⟩
  · norm_num at zero
  · rcases nonnegative_unpacked_cases numerator q observedNumerator nonnegative with
      ⟨sign, rfl, rfl⟩ | ⟨numM, numE, numPositive, rfl, rfl⟩
    · refine ⟨0, rfl, by norm_num, by norm_num, ?_, ?_⟩
      · simpa only [zero_div, sub_self, abs_zero] using halfUnit
      · trivial
    · let result := divCore format numM numE denM denE
      let x := (dyadicValue numM numE / dyadicValue denM denE) / (2 : Rat) ^ result.2.1
      have represented : AccuracyRep result.1 result.2.2 x :=
        divCore_accuracy_rep format numM numE denM denPositive denE
      have aligned : Aligned format result.1 result.2.1 :=
        divCore_precision format numM numPositive numE denM denPositive denE
      have unitNonzero : (2 : Rat) ^ result.2.1 ≠ 0 :=
        ne_of_gt (zpow_pos (by norm_num : (0 : Rat) < 2) _)
      have original : x * (2 : Rat) ^ result.2.1 = dyadicValue numM numE / 10 := by
        dsimp only [x]
        rw [div_mul_cancel₀ _ unitNonzero, ← ten]
      have quotientUpper : x * (2 : Rat) ^ result.2.1 ≤ (1 : Nat) := by
        rw [original]
        apply (div_le_iff₀ (by norm_num : (0 : Rat) < 10)).mpr
        simpa only [Nat.cast_one, one_mul] using upper
      have shifted := shift_exponent_bound format result.1 result.2.1 result.2.2 x 0
        represented aligned (by simpa only [zpow_zero, Nat.cast_one] using quotientUpper)
      have rounded := rounded_bounds format result.1 result.2.1 result.2.2 x 1 E
        represented aligned quotientUpper (by omega) nonpositive
      rw [original] at rounded
      exact rounded

/-- Actual binary64 digit addition, with all representation obligations discharged. -/
theorem add64_bounds (digit : Nat) (tail : Float) (q : Rat) (proper : digit < 10)
    (observed : Observation.decode64 tail = some q) (nonnegative : 0 ≤ q) (upper : q ≤ 1) :
    ∃ sum, Observation.decode64 (digit.toFloat + tail) = some sum ∧
      0 ≤ sum ∧ sum ≤ 10 ∧ |sum - ((digit : Rat) + q)| ≤ (2 : Rat) ^ (-50 : Int) := by
  have digitObserved := Observation.decode64_digit digit proper
  have digitUpper : (digit : Rat) ≤ 9 := Rat.natCast_le_natCast.mpr (show digit ≤ 9 by omega)
  have digitCanonical := model64_unpack_canonical digit.toFloat.toModel (digit : Rat) digitObserved
  have tailCanonical := model64_unpack_canonical tail.toModel q observed
  obtain ⟨sum, sumObserved, sumNonnegative, sumUpper, error, canonical⟩ :=
    unpacked_add_bounds Format.binary64 digit.toFloat.toModel.unpack tail.toModel.unpack
      (digit : Rat) q digitObserved observed (Nat.cast_nonneg _) nonnegative (by linarith)
      digitCanonical tailCanonical (-49) (by decide +kernel) (by decide)
  refine ⟨sum, model64_pack_numeric _ sum canonical sumObserved sumNonnegative sumUpper,
    sumNonnegative, sumUpper, ?_⟩
  have halfUnit : (2 : Rat) ^ (-49 : Int) / 2 = (2 : Rat) ^ (-50 : Int) := by decide +kernel
  rwa [halfUnit] at error

/-- Actual binary32 digit addition, retaining its own conversion and operation. -/
theorem add32_bounds (digit : Nat) (tail : Float32) (q : Rat) (proper : digit < 10)
    (observed : Observation.decode32 tail = some q) (nonnegative : 0 ≤ q) (upper : q ≤ 1) :
    ∃ sum, Observation.decode32 (digit.toFloat32 + tail) = some sum ∧
      0 ≤ sum ∧ sum ≤ 10 ∧ |sum - ((digit : Rat) + q)| ≤ (2 : Rat) ^ (-21 : Int) := by
  have digitObserved := Observation.decode32_digit digit proper
  have digitUpper : (digit : Rat) ≤ 9 := Rat.natCast_le_natCast.mpr (show digit ≤ 9 by omega)
  have digitCanonical := model32_unpack_canonical digit.toFloat32.toModel (digit : Rat) digitObserved
  have tailCanonical := model32_unpack_canonical tail.toModel q observed
  obtain ⟨sum, sumObserved, sumNonnegative, sumUpper, error, canonical⟩ :=
    unpacked_add_bounds Format.binary32 digit.toFloat32.toModel.unpack tail.toModel.unpack
      (digit : Rat) q digitObserved observed (Nat.cast_nonneg _) nonnegative (by linarith)
      digitCanonical tailCanonical (-20) (by decide +kernel) (by decide)
  refine ⟨sum, model32_pack_numeric _ sum canonical sumObserved sumNonnegative sumUpper,
    sumNonnegative, sumUpper, ?_⟩
  have halfUnit : (2 : Rat) ^ (-20 : Int) / 2 = (2 : Rat) ^ (-21 : Int) := by decide +kernel
  rwa [halfUnit] at error

/-- Actual binary64 division by exact ten, including zero and subnormal results. -/
theorem divideTen64_bounds (value : Float) (q : Rat)
    (observed : Observation.decode64 value = some q) (nonnegative : 0 ≤ q) (upper : q ≤ 10) :
    ∃ result, Observation.decode64 (value / 10) = some result ∧
      0 ≤ result ∧ result ≤ 1 ∧ |result - q / 10| ≤ (2 : Rat) ^ (-53 : Int) := by
  obtain ⟨result, resultObserved, resultNonnegative, resultUpper, error, canonical⟩ :=
    unpacked_divTen_bounds Format.binary64 value.toModel.unpack (10 : Float).toModel.unpack
      q observed Observation.decode64_ten nonnegative upper (-52) (by decide +kernel) (by decide)
  refine ⟨result, model64_pack_numeric _ result canonical resultObserved resultNonnegative
    (by linarith), resultNonnegative, resultUpper, ?_⟩
  have halfUnit : (2 : Rat) ^ (-52 : Int) / 2 = (2 : Rat) ^ (-53 : Int) := by decide +kernel
  rwa [halfUnit] at error

/-- Actual binary32 division by exact ten, including zero and subnormal results. -/
theorem divideTen32_bounds (value : Float32) (q : Rat)
    (observed : Observation.decode32 value = some q) (nonnegative : 0 ≤ q) (upper : q ≤ 10) :
    ∃ result, Observation.decode32 (value / 10) = some result ∧
      0 ≤ result ∧ result ≤ 1 ∧ |result - q / 10| ≤ (2 : Rat) ^ (-24 : Int) := by
  obtain ⟨result, resultObserved, resultNonnegative, resultUpper, error, canonical⟩ :=
    unpacked_divTen_bounds Format.binary32 value.toModel.unpack (10 : Float32).toModel.unpack
      q observed Observation.decode32_ten nonnegative upper (-23) (by decide +kernel) (by decide)
  refine ⟨result, model32_pack_numeric _ result canonical resultObserved resultNonnegative
    (by linarith), resultNonnegative, resultUpper, ?_⟩
  have halfUnit : (2 : Rat) ^ (-23 : Int) / 2 = (2 : Rat) ^ (-24 : Int) := by decide +kernel
  rwa [halfUnit] at error

end Floating.Operations
