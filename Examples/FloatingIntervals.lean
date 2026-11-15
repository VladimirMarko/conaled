import Applications.Floating.Intervals
import Examples.FloatingAlgebraLimits

/-! Actual binary observations feeding the existing rational interval consumer. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.FloatingIntervals

open Floating.Observation Floating.Intervals

theorem negative_three_halves64 : decode64 (-1.5 : Float) = some (-3 / 2) := by
  decide +kernel

theorem negative_three_halves32 : decode32 (-1.5 : Float32) = some (-3 / 2) := by
  decide +kernel

theorem negative_square_rational : (-3 / 2 : Rat) * (-3 / 2) = 9 / 4 := by
  norm_num

theorem negative_square64 :
    square64.impl (-1.5 : Float) = some (IntervalAnalysis.singleton (9 / 4)) := by
  rw [square64_value _ _ negative_three_halves64, negative_square_rational]

theorem negative_square32 :
    square32.impl (-1.5 : Float32) = some (IntervalAnalysis.singleton (9 / 4)) := by
  rw [square32_value _ _ negative_three_halves32, negative_square_rational]

theorem negative_square_contains64 :
    ∃ interval, square64.impl (-1.5 : Float) = some interval ∧
      IntervalAnalysis.Contains interval (9 / 4) := by
  have h := square64_sound _ _ negative_three_halves64
  rw [negative_square_rational] at h
  exact h

theorem negative_square_contains32 :
    ∃ interval, square32.impl (-1.5 : Float32) = some interval ∧
      IntervalAnalysis.Contains interval (9 / 4) := by
  have h := square32_sound _ _ negative_three_halves32
  rw [negative_square_rational] at h
  exact h

theorem eighth64 : decode64 (0.125 : Float) = some (1 / 8) := by decide +kernel
theorem eighth32 : decode32 (0.125 : Float32) = some (1 / 8) := by decide +kernel

theorem eighth_square_rational : (1 / 8 : Rat) * (1 / 8) = 1 / 64 := by norm_num

/-- Finite observation includes the least positive binary32 subnormal. -/
theorem smallest_subnormal32 :
    decode32 (Float32.ofBits 1) = some ((1 : Rat) / 2 ^ (149 : Nat)) := by
  decide +kernel

theorem eighth_square64 :
    square64.impl (0.125 : Float) = some (IntervalAnalysis.singleton (1 / 64)) := by
  rw [square64_value _ _ eighth64, eighth_square_rational]

theorem eighth_square32 :
    square32.impl (0.125 : Float32) = some (IntervalAnalysis.singleton (1 / 64)) := by
  rw [square32_value _ _ eighth32, eighth_square_rational]

theorem signed_zero_same_interval64 :
    square64.impl (0 : Float) = some (IntervalAnalysis.singleton 0) ∧
    square64.impl (-(0 : Float)) = some (IntervalAnalysis.singleton 0) := by
  constructor
  · simpa only [mul_zero] using square64_value _ _ decode64_zero
  · simpa only [mul_zero] using square64_value _ _ signed_zero64.2.1

theorem signed_zero_same_interval32 :
    square32.impl (0 : Float32) = some (IntervalAnalysis.singleton 0) ∧
    square32.impl (-(0 : Float32)) = some (IntervalAnalysis.singleton 0) := by
  constructor
  · simpa only [mul_zero] using square32_value _ _ decode32_zero
  · simpa only [mul_zero] using square32_value _ _ signed_zero32.2.1

theorem nonfinite_rejection64 :
    square64.impl ((0 : Float) / 0) = none ∧
    square64.impl ((1 : Float) / 0) = none ∧ square64.impl ((-1 : Float) / 0) = none := by
  exact ⟨(adapt_none_iff decode64 squareConsumer _).2 exceptional_values64.1,
    (adapt_none_iff decode64 squareConsumer _).2 exceptional_values64.2.1,
    (adapt_none_iff decode64 squareConsumer _).2 exceptional_values64.2.2⟩

theorem nonfinite_rejection32 :
    square32.impl ((0 : Float32) / 0) = none ∧
    square32.impl ((1 : Float32) / 0) = none ∧ square32.impl ((-1 : Float32) / 0) = none := by
  exact ⟨(adapt_none_iff decode32 squareConsumer _).2 exceptional_values32.1,
    (adapt_none_iff decode32 squareConsumer _).2 exceptional_values32.2.1,
    (adapt_none_iff decode32 squareConsumer _).2 exceptional_values32.2.2⟩

end Examples.FloatingIntervals
