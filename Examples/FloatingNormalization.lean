import Applications.Floating.Rounding.Magnitude
import Applications.Floating.Intervals

/-!
# Enclosing original values after actual normalization

The interval is centered at the actual normalized observation, with the radius
proved for its first rounding shift. It therefore contains the represented
original value. The existing interval-square consumer acts on that enclosure.
The carry and underflow cases preserve their distinct original values.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.FloatingNormalization

open Float.Model Float.Model.UnpackedFloat
open _root_.Floating.Rounding

def radius (format : Format) (m : Nat) (e : Int) (a : Accuracy) : Rat :=
  (2 : Rat) ^ (shiftToTargetExponent format m e a).2 / 2

def interval (format : Format) (m : Nat) (e : Int) (a : Accuracy) :
    Option IntervalAnalysis.Interval :=
  (_root_.Floating.Observation.unpack (roundWithAccuracy format .positive m e a)).map
    (fun value => ⟨value - radius format m e a, value + radius format m e a⟩)

theorem interval_value (format : Format) (m : Nat) (e : Int) (a : Accuracy) (value : Rat)
    (observed : _root_.Floating.Observation.unpack (roundWithAccuracy format .positive m e a) =
      some value) :
    interval format m e a = some ⟨value - radius format m e a, value + radius format m e a⟩ := by
  simp only [interval, observed, Option.map_some]

/-- Raw positive normalization always has an exact finite observation, before packing. -/
theorem interval_isSome (format : Format) (m : Nat) (e : Int) (a : Accuracy) :
    (interval format m e a).isSome = true := by
  simp only [interval, roundWithAccuracy_positive_value, Option.map_some, Option.isSome_some]

theorem interval_encloses (format : Format) (m : Nat) (e : Int) (a : Accuracy) (x : Rat)
    (represented : AccuracyRep m a x) :
    ∃ result, interval format m e a = some result ∧
      IntervalAnalysis.Contains result (x * (2 : Rat) ^ e) := by
  obtain ⟨value, observed, error⟩ := roundWithAccuracy_error format m e a x represented
  refine ⟨⟨value - radius format m e a, value + radius format m e a⟩,
    interval_value format m e a value observed, ?_⟩
  have bounds : -radius format m e a ≤ value - x * (2 : Rat) ^ e ∧
      value - x * (2 : Rat) ^ e ≤ radius format m e a := abs_le.mp error
  change value - radius format m e a ≤ x * (2 : Rat) ^ e ∧
    x * (2 : Rat) ^ e ≤ value + radius format m e a
  constructor <;> linarith

def consume (format : Format) (m : Nat) (e : Int) (a : Accuracy)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    Option IntervalAnalysis.Interval :=
  (interval format m e a).map consumer.impl

theorem consume_sound (format : Format) (m : Nat) (e : Int) (a : Accuracy) (x : Rat)
    (represented : AccuracyRep m a x)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    ∃ result, consume format m e a consumer = some result ∧
      IntervalAnalysis.Contains result (consumer.spec (x * (2 : Rat) ^ e)) := by
  obtain ⟨enclosure, observed, contained⟩ := interval_encloses format m e a x represented
  refine ⟨consumer.impl enclosure, ?_, consumer.preserves contained⟩
  simp only [consume, observed, Option.map_some]

def square (format : Format) (m : Nat) (e : Int) (a : Accuracy) :
    Option IntervalAnalysis.Interval :=
  consume format m e a _root_.Floating.Intervals.squareConsumer

theorem square_sound (format : Format) (m : Nat) (e : Int) (a : Accuracy) (x : Rat)
    (represented : AccuracyRep m a x) :
    ∃ result, square format m e a = some result ∧
      IntervalAnalysis.Contains result ((x * (2 : Rat) ^ e) * (x * (2 : Rat) ^ e)) := by
  simpa only [square, _root_.Floating.Intervals.squareConsumer, Relational.compose,
    Relational.pair, Relational.identity, IntervalAnalysis.mulSquare, Function.comp, id_eq] using
    consume_sound format m e a x represented _root_.Floating.Intervals.squareConsumer

theorem carry_result :
    roundWithAccuracy Format.binary32 .positive (2 ^ 24 - 1) (-23) (.inexact .gt) =
      .finite .positive (2 ^ 23) (-22) (by decide) := by
  have first := target_shift_of_width Format.binary32 (2 ^ 24 - 1) (-23) (.inexact .gt)
    (by decide) (by decide)
  have rounded :
      (ExtendedMantissa.ofMantissaAndAccuracy (2 ^ 24 - 1) (.inexact .gt)).roundedMantissa = 2 ^ 24 := by
    simp only [ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.roundedMantissa,
      ExtendedMantissa.accuracy, Accuracy.roundToNearestEven]
    omega
  have second := target_shift_carry Format.binary32 (-23) (by decide)
  rw [show Format.binary32.mantissaBits = 24 from rfl] at second
  simp only [roundWithAccuracy, first, rounded, second]
  norm_num

theorem underflow_result :
    roundWithAccuracy Format.binary32 .positive 1 (-150) .exact = .zero .positive := by
  have first : shiftToTargetExponent Format.binary32 1 (-150) .exact =
      (⟨0, true, false⟩, -149) := rfl
  unfold roundWithAccuracy
  rw [first]
  change (let result := shiftToTargetExponent Format.binary32 0 (-149) .exact
    if h : result.1.mantissa = 0 then UnpackedFloat.zero .positive
    else UnpackedFloat.finite .positive result.1.mantissa result.2 (Nat.pos_of_ne_zero h)) = _
  rw [target_shift_of_width Format.binary32 0 (-149) .exact (by decide) (by decide)]
  rfl

def carryInput : Rat := ((2 ^ 24 - 1 : Nat) : Rat) + 3 / 4

theorem carry_represented : AccuracyRep (2 ^ 24 - 1) (.inexact .gt) carryInput := by
  norm_num [AccuracyRep, carryInput]

theorem carry_original : carryInput * (2 : Rat) ^ (-23 : Int) = 2 - (2 : Rat) ^ (-25 : Int) := by
  norm_num [carryInput]

theorem carry_observation :
    _root_.Floating.Observation.unpack
      (roundWithAccuracy Format.binary32 .positive (2 ^ 24 - 1) (-23) (.inexact .gt)) = some 2 := by
  rw [carry_result]
  decide +kernel

theorem carry_radius :
    radius Format.binary32 (2 ^ 24 - 1) (-23) (.inexact .gt) = (2 : Rat) ^ (-24 : Int) := by
  rw [radius, target_shift_exponent]
  decide +kernel

theorem carry_interval_value :
    interval Format.binary32 (2 ^ 24 - 1) (-23) (.inexact .gt) =
      some ⟨2 - (2 : Rat) ^ (-24 : Int), 2 + (2 : Rat) ^ (-24 : Int)⟩ := by
  rw [interval_value _ _ _ _ _ carry_observation, carry_radius]

theorem carry_original_enclosed :
    ∃ result, interval Format.binary32 (2 ^ 24 - 1) (-23) (.inexact .gt) = some result ∧
      IntervalAnalysis.Contains result (2 - (2 : Rat) ^ (-25 : Int)) := by
  simpa only [carry_original] using
    interval_encloses Format.binary32 (2 ^ 24 - 1) (-23) (.inexact .gt) carryInput carry_represented

theorem carry_squared_original_enclosed :
    ∃ result, square Format.binary32 (2 ^ 24 - 1) (-23) (.inexact .gt) = some result ∧
      IntervalAnalysis.Contains result
        ((2 - (2 : Rat) ^ (-25 : Int)) * (2 - (2 : Rat) ^ (-25 : Int))) := by
  simpa only [carry_original] using
    square_sound Format.binary32 (2 ^ 24 - 1) (-23) (.inexact .gt) carryInput carry_represented

theorem underflow_represented : AccuracyRep 1 .exact (1 : Rat) := rfl

theorem underflow_observation :
    _root_.Floating.Observation.unpack (roundWithAccuracy Format.binary32 .positive 1 (-150) .exact) =
      some 0 := by
  rw [underflow_result]
  rfl

theorem underflow_radius : radius Format.binary32 1 (-150) .exact = (2 : Rat) ^ (-150 : Int) := by
  rw [radius, target_shift_exponent]
  decide +kernel

theorem underflow_interval_value :
    interval Format.binary32 1 (-150) .exact =
      some ⟨-(2 : Rat) ^ (-150 : Int), (2 : Rat) ^ (-150 : Int)⟩ := by
  rw [interval_value _ _ _ _ _ underflow_observation, underflow_radius]
  simp only [zero_sub, zero_add]

theorem underflow_original_enclosed :
    ∃ result, interval Format.binary32 1 (-150) .exact = some result ∧
      IntervalAnalysis.Contains result ((2 : Rat) ^ (-150 : Int)) := by
  simpa only [one_mul] using interval_encloses Format.binary32 1 (-150) .exact 1 underflow_represented

theorem underflow_squared_original_enclosed :
    ∃ result, square Format.binary32 1 (-150) .exact = some result ∧
      IntervalAnalysis.Contains result ((2 : Rat) ^ (-150 : Int) * (2 : Rat) ^ (-150 : Int)) := by
  simpa only [one_mul] using square_sound Format.binary32 1 (-150) .exact 1 underflow_represented

/-- Four-corner interval multiplication retains its ordinary dependency loss. -/
theorem underflow_square_value :
    square Format.binary32 1 (-150) .exact =
      some ⟨-(2 : Rat) ^ (-300 : Int), (2 : Rat) ^ (-300 : Int)⟩ := by
  unfold square consume
  rw [underflow_interval_value]
  change some (IntervalAnalysis.mul
    ⟨-(2 : Rat) ^ (-150 : Int), (2 : Rat) ^ (-150 : Int)⟩
    ⟨-(2 : Rat) ^ (-150 : Int), (2 : Rat) ^ (-150 : Int)⟩) = _
  norm_num [IntervalAnalysis.mul]
  decide +kernel

theorem underflow_rounding_unit_bound :
    (shiftToTargetExponent Format.binary32 1 (-150) .exact).2 ≤ -149 := by
  have bound := shift_exponent_bound Format.binary32 1 (-150) .exact 1 (-150)
    underflow_represented (Or.inl (by decide)) (by simp only [one_mul, le_refl])
  exact bound

/-- Full rounding also lowers a noncanonical input exponent before normalization. -/
theorem full_round_one :
    _root_.Floating.Packing.Canonical Format.binary32 (round Format.binary32 .positive 1 0) ∧
      _root_.Floating.Observation.unpack (round Format.binary32 .positive 1 0) = some 1 := by
  refine ⟨round_canonical_of_pos Format.binary32 .positive 1 0 (by decide), ?_⟩
  have observed := round_positive_value Format.binary32 1 0
  change _root_.Floating.Observation.unpack (round Format.binary32 .positive 1 0) =
    some (_root_.Floating.Observation.dyadicValue (2 ^ 23) (-23)) at observed
  have exactValue : _root_.Floating.Observation.dyadicValue (2 ^ 23) (-23) = 1 := by
    decide +kernel
  rwa [exactValue] at observed

end Examples.FloatingNormalization
