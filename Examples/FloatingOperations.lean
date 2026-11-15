import Applications.Floating.Operations
import Applications.Floating.Intervals
import Applications.Numerals.FloatingError
import Examples.FloatingNumeralsValues

/-!
# Consuming the error enclosure of an actual floating digit step

The existing rational residual meanings combine the two actual operation bounds.
The interval consumer encloses the independent rational step and its square.
Successful decoding remains explicit, including at zero and closed endpoints.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.FloatingOperations

open _root_.Floating.Observation
open _root_.Floating.Operations
open Numerals.FloatingError

def step64 (digit : Nat) (tail : Float) : Float := (digit.toFloat + tail) / 10
def step32 (digit : Nat) (tail : Float32) : Float32 := (digit.toFloat32 + tail) / 10

def radius64 : Rat := (2 : Rat) ^ (-50 : Int) / 10 + (2 : Rat) ^ (-53 : Int)
def radius32 : Rat := (2 : Rat) ^ (-21 : Int) / 10 + (2 : Rat) ^ (-24 : Int)

/-- The observed fields reuse the independent step residual specification. -/
theorem step_error (s : Step) (additionEps divisionEps : Rat)
    (converted : s.convertedValue = (s.digit : Rat))
    (addition : |s.additionError| ≤ additionEps) (division : |s.divisionError| ≤ divisionEps) :
    |s.outputValue - ((s.digit : Rat) + s.tailValue) / 10| ≤ additionEps / 10 + divisionEps := by
  have conversionError : s.conversionError = 0 := by
    simp only [Step.conversionError, converted, sub_self]
  have operations : s.operationBound ≤ additionEps / 10 + divisionEps := by
    dsimp only [Step.operationBound]
    rw [conversionError, abs_zero, zero_add]
    exact add_le_add (div_le_div_of_nonneg_right addition (by norm_num)) division
  have residual : s.outputValue - ((s.digit : Rat) + s.tailValue) / 10 = s.localError := by
    rw [step_decomposition]
    ring
  rw [residual]
  exact (localError_abs_le_operationBound s).trans operations

theorem step64_bounds (digit : Nat) (tail : Float) (q : Rat) (proper : digit < 10)
    (observed : decode64 tail = some q) (nonnegative : 0 ≤ q) (upper : q ≤ 1) :
    ∃ sum value, decode64 (digit.toFloat + tail) = some sum ∧
      decode64 (step64 digit tail) = some value ∧ 0 ≤ sum ∧ sum ≤ 10 ∧
      0 ≤ value ∧ value ≤ 1 ∧ |value - ((digit : Rat) + q) / 10| ≤ radius64 := by
  obtain ⟨sum, sumObserved, sumNonnegative, sumUpper, addition⟩ :=
    add64_bounds digit tail q proper observed nonnegative upper
  obtain ⟨value, valueObserved, valueNonnegative, valueUpper, division⟩ :=
    divideTen64_bounds (digit.toFloat + tail) sum sumObserved sumNonnegative sumUpper
  have error := step_error ⟨digit, q, (digit : Rat), sum, value⟩
    ((2 : Rat) ^ (-50 : Int)) ((2 : Rat) ^ (-53 : Int)) rfl addition division
  exact ⟨sum, value, sumObserved, valueObserved, sumNonnegative, sumUpper,
    valueNonnegative, valueUpper, error⟩

theorem step32_bounds (digit : Nat) (tail : Float32) (q : Rat) (proper : digit < 10)
    (observed : decode32 tail = some q) (nonnegative : 0 ≤ q) (upper : q ≤ 1) :
    ∃ sum value, decode32 (digit.toFloat32 + tail) = some sum ∧
      decode32 (step32 digit tail) = some value ∧ 0 ≤ sum ∧ sum ≤ 10 ∧
      0 ≤ value ∧ value ≤ 1 ∧ |value - ((digit : Rat) + q) / 10| ≤ radius32 := by
  obtain ⟨sum, sumObserved, sumNonnegative, sumUpper, addition⟩ :=
    add32_bounds digit tail q proper observed nonnegative upper
  obtain ⟨value, valueObserved, valueNonnegative, valueUpper, division⟩ :=
    divideTen32_bounds (digit.toFloat32 + tail) sum sumObserved sumNonnegative sumUpper
  have error := step_error ⟨digit, q, (digit : Rat), sum, value⟩
    ((2 : Rat) ^ (-21 : Int)) ((2 : Rat) ^ (-24 : Int)) rfl addition division
  exact ⟨sum, value, sumObserved, valueObserved, sumNonnegative, sumUpper,
    valueNonnegative, valueUpper, error⟩

def consume {α : Type} (read : α → Option Rat) (actual : α) (radius : Rat)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    Option IntervalAnalysis.Interval :=
  (read actual).map (fun value => consumer.impl ⟨value - radius, value + radius⟩)

theorem consume_none_iff {α : Type} (read : α → Option Rat) (actual : α) (radius : Rat)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    consume read actual radius consumer = none ↔ read actual = none := by
  change (read actual).map _ = none ↔ read actual = none
  cases read actual <;> simp

theorem consume_sound {α : Type} (read : α → Option Rat) (actual : α) (radius : Rat)
    (value original : Rat) (observed : read actual = some value) (error : |value - original| ≤ radius)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    ∃ result, consume read actual radius consumer = some result ∧
      IntervalAnalysis.Contains result (consumer.spec original) := by
  refine ⟨consumer.impl ⟨value - radius, value + radius⟩, ?_, consumer.preserves ?_⟩
  · simp only [consume, observed, Option.map_some]
  · have bounds := abs_le.mp error
    change value - radius ≤ original ∧ original ≤ value + radius
    constructor <;> linarith

def consumeStep64 (digit : Nat) (tail : Float)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    Option IntervalAnalysis.Interval := consume decode64 (step64 digit tail) radius64 consumer

def consumeStep32 (digit : Nat) (tail : Float32)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    Option IntervalAnalysis.Interval := consume decode32 (step32 digit tail) radius32 consumer

theorem consumeStep64_sound (digit : Nat) (tail : Float) (q : Rat) (proper : digit < 10)
    (observed : decode64 tail = some q) (nonnegative : 0 ≤ q) (upper : q ≤ 1)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    ∃ value result, decode64 (step64 digit tail) = some value ∧
      consumeStep64 digit tail consumer = some result ∧
      IntervalAnalysis.Contains result (consumer.spec (((digit : Rat) + q) / 10)) := by
  obtain ⟨sum, value, sumObserved, valueObserved, sumNonnegative, sumUpper,
    valueNonnegative, valueUpper, error⟩ := step64_bounds digit tail q proper observed nonnegative upper
  obtain ⟨result, consumed, contained⟩ := consume_sound decode64 (step64 digit tail) radius64
    value (((digit : Rat) + q) / 10) valueObserved error consumer
  exact ⟨value, result, valueObserved, consumed, contained⟩

theorem consumeStep32_sound (digit : Nat) (tail : Float32) (q : Rat) (proper : digit < 10)
    (observed : decode32 tail = some q) (nonnegative : 0 ≤ q) (upper : q ≤ 1)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    ∃ value result, decode32 (step32 digit tail) = some value ∧
      consumeStep32 digit tail consumer = some result ∧
      IntervalAnalysis.Contains result (consumer.spec (((digit : Rat) + q) / 10)) := by
  obtain ⟨sum, value, sumObserved, valueObserved, sumNonnegative, sumUpper,
    valueNonnegative, valueUpper, error⟩ := step32_bounds digit tail q proper observed nonnegative upper
  obtain ⟨result, consumed, contained⟩ := consume_sound decode32 (step32 digit tail) radius32
    value (((digit : Rat) + q) / 10) valueObserved error consumer
  exact ⟨value, result, valueObserved, consumed, contained⟩

def squareStep64 (digit : Nat) (tail : Float) : Option IntervalAnalysis.Interval :=
  consumeStep64 digit tail _root_.Floating.Intervals.squareConsumer

def squareStep32 (digit : Nat) (tail : Float32) : Option IntervalAnalysis.Interval :=
  consumeStep32 digit tail _root_.Floating.Intervals.squareConsumer

theorem squareStep64_sound (digit : Nat) (tail : Float) (q : Rat) (proper : digit < 10)
    (observed : decode64 tail = some q) (nonnegative : 0 ≤ q) (upper : q ≤ 1) :
    ∃ value result, decode64 (step64 digit tail) = some value ∧
      squareStep64 digit tail = some result ∧
      IntervalAnalysis.Contains result ((((digit : Rat) + q) / 10) * (((digit : Rat) + q) / 10)) :=
  consumeStep64_sound digit tail q proper observed nonnegative upper
    _root_.Floating.Intervals.squareConsumer

theorem squareStep32_sound (digit : Nat) (tail : Float32) (q : Rat) (proper : digit < 10)
    (observed : decode32 tail = some q) (nonnegative : 0 ≤ q) (upper : q ≤ 1) :
    ∃ value result, decode32 (step32 digit tail) = some value ∧
      squareStep32 digit tail = some result ∧
      IntervalAnalysis.Contains result ((((digit : Rat) + q) / 10) * (((digit : Rat) + q) / 10)) :=
  consumeStep32_sound digit tail q proper observed nonnegative upper
    _root_.Floating.Intervals.squareConsumer

/-- Every conjunct of the source's closed-endpoint case is retained. -/
theorem endpoint_values :
    decode64 ((9 : Float) + 1) = some 10 ∧ decode64 ((10 : Float) / 10) = some 1 ∧
    decode32 ((9 : Float32) + 1) = some 10 ∧ decode32 ((10 : Float32) / 10) = some 1 := by
  decide +kernel

theorem endpoint64_step : decode64 (step64 9 1) = some 1 := by decide +kernel
theorem endpoint32_step : decode32 (step32 9 1) = some 1 := by decide +kernel

theorem endpoint64_square :
    ∃ result, squareStep64 9 1 = some result ∧ IntervalAnalysis.Contains result 1 := by
  obtain ⟨value, result, observed, consumed, contained⟩ :=
    squareStep64_sound 9 1 1 (by decide) (by decide +kernel) (by norm_num) (by norm_num)
  refine ⟨result, consumed, ?_⟩
  norm_num at contained
  exact contained

theorem endpoint32_square :
    ∃ result, squareStep32 9 1 = some result ∧ IntervalAnalysis.Contains result 1 := by
  obtain ⟨value, result, observed, consumed, contained⟩ :=
    squareStep32_sound 9 1 1 (by decide) (by decide +kernel) (by norm_num) (by norm_num)
  refine ⟨result, consumed, ?_⟩
  norm_num at contained
  exact contained

theorem least_subnormal_division :
    decode64 ((Float.ofBits 1) / 10) = some 0 ∧
    decode32 ((Float32.ofBits 1) / 10) = some 0 := by
  decide +kernel

theorem least_subnormal_inputs :
    decode64 (Float.ofBits 1) = some ((2 : Rat) ^ (-1074 : Int)) ∧
    decode32 (Float32.ofBits 1) = some ((2 : Rat) ^ (-149 : Int)) := by
  decide +kernel

theorem least_subnormal64_error :
    |(2 : Rat) ^ (-1074 : Int) / 10| ≤ (2 : Rat) ^ (-53 : Int) := by
  have positive := zpow_pos (by norm_num : (0 : Rat) < 2) (-1074 : Int)
  have upper : (2 : Rat) ^ (-1074 : Int) ≤ 10 :=
    (zpow_le_one_of_nonpos₀ (by norm_num : (1 : Rat) ≤ 2) (by decide : (-1074 : Int) ≤ 0)).trans
      (by norm_num)
  obtain ⟨value, observed, lower, bound, error⟩ := divideTen64_bounds (Float.ofBits 1)
    ((2 : Rat) ^ (-1074 : Int)) least_subnormal_inputs.1 (le_of_lt positive) upper
  have same : value = 0 := Option.some.inj (observed.symm.trans least_subnormal_division.1)
  simpa only [same, zero_sub, abs_neg] using error

theorem least_subnormal32_error :
    |(2 : Rat) ^ (-149 : Int) / 10| ≤ (2 : Rat) ^ (-24 : Int) := by
  have positive := zpow_pos (by norm_num : (0 : Rat) < 2) (-149 : Int)
  have upper : (2 : Rat) ^ (-149 : Int) ≤ 10 :=
    (zpow_le_one_of_nonpos₀ (by norm_num : (1 : Rat) ≤ 2) (by decide : (-149 : Int) ≤ 0)).trans
      (by norm_num)
  obtain ⟨value, observed, lower, bound, error⟩ := divideTen32_bounds (Float32.ofBits 1)
    ((2 : Rat) ^ (-149 : Int)) least_subnormal_inputs.2 (le_of_lt positive) upper
  have same : value = 0 := Option.some.inj (observed.symm.trans least_subnormal_division.2)
  simpa only [same, zero_sub, abs_neg] using error

theorem negative_zero_division :
    decode64 ((-(0 : Float)) / 10) = some 0 ∧
    decode32 ((-(0 : Float32)) / 10) = some 0 := by
  decide +kernel

theorem negative_zero64_bound :
    ∃ value, decode64 ((-(0 : Float)) / 10) = some value ∧
      0 ≤ value ∧ value ≤ 1 ∧ |value| ≤ (2 : Rat) ^ (-53 : Int) := by
  simpa only [zero_div, sub_zero] using
    divideTen64_bounds (-(0 : Float)) 0 (by decide +kernel) (by norm_num) (by norm_num)

theorem negative_zero32_bound :
    ∃ value, decode32 ((-(0 : Float32)) / 10) = some value ∧
      0 ≤ value ∧ value ≤ 1 ∧ |value| ≤ (2 : Rat) ^ (-24 : Int) := by
  simpa only [zero_div, sub_zero] using
    divideTen32_bounds (-(0 : Float32)) 0 (by decide +kernel) (by norm_num) (by norm_num)

theorem tenth64_observation :
    decode64 (step64 1 0) = some (3602879701896397 / 36028797018963968 : Rat) ∧
    decode64 (step64 1 0) ≠ some (1 / 10 : Rat) :=
  Examples.FloatingNumerals.fraction64_tenth.2

theorem tenth32_observation :
    decode32 (step32 1 0) = some (13421773 / 134217728 : Rat) ∧
    decode32 (step32 1 0) ≠ some (1 / 10 : Rat) :=
  Examples.FloatingNumerals.fraction32_tenth.2

/-- The actual nonexact tenth is used to enclose the exact original square. -/
theorem tenth64_original_square :
    ∃ result, squareStep64 1 0 = some result ∧ IntervalAnalysis.Contains result (1 / 100) := by
  obtain ⟨value, result, observed, consumed, contained⟩ :=
    squareStep64_sound 1 0 0 (by decide) decode64_zero (by norm_num) (by norm_num)
  refine ⟨result, consumed, ?_⟩
  norm_num at contained
  exact contained

theorem tenth32_original_square :
    ∃ result, squareStep32 1 0 = some result ∧ IntervalAnalysis.Contains result (1 / 100) := by
  obtain ⟨value, result, observed, consumed, contained⟩ :=
    squareStep32_sound 1 0 0 (by decide) decode32_zero (by norm_num) (by norm_num)
  refine ⟨result, consumed, ?_⟩
  norm_num at contained
  exact contained

end Examples.FloatingOperations
