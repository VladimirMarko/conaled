import Applications.Floating.ArithmeticCore
import Applications.Floating.Intervals

/-!
# Actual rounding followed by an interval consumer

The source cases retain ties, unequal exponents, and nonzero sticky information.
The composed consumer shifts the actual residual-bit record, releases an
enclosure around the actual nearest-even mantissa, and squares that enclosure.
Its semantic result is the square of the independently represented input in
shifted mantissa units. This is not a whole formatted division theorem.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.FloatingRounding

open Float.Model Float.Model.UnpackedFloat
open Floating.Rounding Floating.ArithmeticCore Floating.Observation

@[reducible] def representation : Relational.RelRep := ⟨ExtendedMantissa, Rat, ExtendedRep⟩

def shiftSquare (n : Nat) : Relational.RelSquare representation representation where
  impl extended := extended >>> n
  spec x := x / (2 : Rat) ^ n
  preserves := shiftRight_rep _ n _

def roundInterval (extended : ExtendedMantissa) : IntervalAnalysis.Interval :=
  ⟨(extended.roundedMantissa : Rat) - 1 / 2,
    (extended.roundedMantissa : Rat) + 1 / 2⟩

def roundSquare : Relational.RelSquare representation IntervalAnalysis.representation where
  impl := roundInterval
  spec := id
  preserves := AccuracyRep.round_bounds

def shiftRoundSquare (n : Nat) := Relational.compose roundSquare (shiftSquare n)

def squaredConsumer (n : Nat) :=
  Relational.compose Floating.Intervals.squareConsumer (shiftRoundSquare n)

theorem shifted_round_enclosure (extended : ExtendedMantissa) (x : Rat) (n : Nat)
    (h : ExtendedRep extended x) :
    IntervalAnalysis.Contains ((shiftRoundSquare n).impl extended) (x / (2 : Rat) ^ n) := by
  simpa only [shiftRoundSquare, Relational.compose, Function.comp, roundSquare,
    shiftSquare, id_eq, IntervalAnalysis.representation] using (shiftRoundSquare n).preserves h

theorem squared_enclosure (extended : ExtendedMantissa) (x : Rat) (n : Nat)
    (h : ExtendedRep extended x) :
    IntervalAnalysis.Contains ((squaredConsumer n).impl extended)
      ((x / (2 : Rat) ^ n) * (x / (2 : Rat) ^ n)) := by
  simpa only [squaredConsumer, shiftRoundSquare, Floating.Intervals.squareConsumer,
    Relational.compose, Relational.pair, Relational.identity, Function.comp,
    roundSquare, shiftSquare, id_eq, IntervalAnalysis.mulSquare,
    IntervalAnalysis.representation] using (squaredConsumer n).preserves h

theorem quotient_five_halves : quotientMantissa 5 2 = 2 := by decide +kernel
theorem quotient_seven_halves : quotientMantissa 7 2 = 4 := by decide +kernel
theorem quotient_seven_thirds : quotientMantissa 7 3 = 2 := by decide +kernel
theorem quotient_eight_thirds : quotientMantissa 8 3 = 3 := by decide +kernel

theorem opposite_ties_even : quotientMantissa 5 2 % 2 = 0 ∧ quotientMantissa 7 2 % 2 = 0 := by
  constructor
  · exact nearestEven_tie_even 2
  · exact nearestEven_tie_even 3

theorem quotient_five_halves_error : |(quotientMantissa 5 2 : Rat) - 5 / 2| ≤ 1 / 2 :=
  quotientMantissa_error 5 2 (by decide)

theorem decreased_exponent_case :
    decreaseExponent 3 5 (-2) = (384, -2) ∧
    dyadicValue (decreaseExponent 3 5 (-2)).1 (decreaseExponent 3 5 (-2)).2 = 96 := by
  constructor
  · decide +kernel
  · rw [decreaseExponent_value]
    decide +kernel

theorem unchanged_exponent_case :
    decreaseExponent 3 (-2) 5 = (3, -2) ∧
    dyadicValue (decreaseExponent 3 (-2) 5).1 (decreaseExponent 3 (-2) 5).2 = 3 / 4 := by
  constructor
  · decide +kernel
  · rw [decreaseExponent_value]
    decide +kernel

theorem exact_five_rep : ExtendedRep ⟨5, false, false⟩ 5 := rfl

theorem exact_five_shifted :
    ExtendedRep (ExtendedMantissa.shiftRightOne ⟨5, false, false⟩) (5 / 2) :=
  shiftRightOne_rep exact_five_rep

theorem sticky_nineteen_fourths : ExtendedRep ⟨4, true, true⟩ (19 / 4) := by
  change 2 * (4 : Rat) + 1 < 2 * (19 / 4) ∧ 19 / 4 < (4 : Rat) + 1
  norm_num

theorem sticky_shifted :
    ExtendedRep (ExtendedMantissa.shiftRightOne ⟨4, true, true⟩) (19 / 8) := by
  have h := shiftRightOne_rep sticky_nineteen_fourths
  norm_num at h ⊢
  exact h

theorem classified_two_and_half : AccuracyRep 2 (accuracyOfFraction 1 2) (5 / 2) := by
  have h := accuracyOfFraction_rep 2 1 2 (by decide) (by decide)
  norm_num at h ⊢
  exact h

theorem aligned_sum_case :
    dyadicValue ((decreaseExponent 3 2 (-1)).1 + (decreaseExponent 1 (-1) (-1)).1) (-1) =
      25 / 2 := by
  have h := aligned_positive_sum_value 3 1 2 (-1)
  change dyadicValue ((decreaseExponent 3 2 (-1)).1 +
    (decreaseExponent 1 (-1) (-1)).1) (-1) = _ at h
  rw [h]
  decide +kernel

theorem five_interval_value :
    (shiftRoundSquare 1).impl ⟨5, false, false⟩ = ⟨3 / 2, 5 / 2⟩ := by
  change (⟨(2 : Rat) - 1 / 2, 2 + 1 / 2⟩ : IntervalAnalysis.Interval) = _
  norm_num

theorem five_interval_contains :
    IntervalAnalysis.Contains ((shiftRoundSquare 1).impl ⟨5, false, false⟩) (5 / 2) := by
  simpa only [pow_one] using shifted_round_enclosure _ _ 1 exact_five_rep

theorem five_squared_value :
    (squaredConsumer 1).impl ⟨5, false, false⟩ = ⟨9 / 4, 25 / 4⟩ := by
  change IntervalAnalysis.mul ((shiftRoundSquare 1).impl ⟨5, false, false⟩)
    ((shiftRoundSquare 1).impl ⟨5, false, false⟩) = _
  rw [five_interval_value]
  norm_num [IntervalAnalysis.mul]

theorem five_squared_contains :
    IntervalAnalysis.Contains ((squaredConsumer 1).impl ⟨5, false, false⟩) (25 / 4) := by
  have h := squared_enclosure _ _ 1 exact_five_rep
  norm_num at h ⊢
  exact h

theorem below_current_exponent :
    (shiftToExponent 5 3 .exact (-2)).1 = ⟨5, false, false⟩ ∧
      (shiftToExponent 5 3 .exact (-2)).2 = 3 := by
  constructor
  · rfl
  · exact shiftToExponent_exponent 5 3 .exact (-2)

end Examples.FloatingRounding
