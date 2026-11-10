import Applications.Floating.Observation
import Applications.Intervals.Arithmetic

/-!
# Interval consumers of successful floating observations

An optional observation represents a rational only when it returns that rational.
The adapter retains rejection and uses an existing interval consumer's law.
The concrete square consumer encloses a function of the represented binary value;
it makes no claim about an original decimal value or rounded multiplication.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Floating.Intervals

variable {α : Type}

def observed (read : α → Option Rat) : Relational.RelRep :=
  ⟨α, Rat, fun value q => read value = some q⟩

def successful : Relational.RelRep :=
  ⟨Option IntervalAnalysis.Interval, Rat,
    fun answer q => ∃ interval, answer = some interval ∧ IntervalAnalysis.Contains interval q⟩

/-- Execute a supplied existing interval consumer only after successful decoding. -/
def adapt (read : α → Option Rat)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    Relational.RelSquare (observed read) successful where
  impl value := (read value).map (fun q => consumer.impl (IntervalAnalysis.singleton q))
  spec := consumer.spec
  preserves := by
    intro value q h
    refine ⟨consumer.impl (IntervalAnalysis.singleton q), ?_,
      consumer.preserves (IntervalAnalysis.singleton_contains q)⟩
    change read value = some q at h
    rw [h]
    rfl

theorem adapt_none_iff (read : α → Option Rat)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation)
    (value : α) : (adapt read consumer).impl value = none ↔ read value = none := by
  change (read value).map _ = none ↔ read value = none
  cases read value <;> simp

theorem adapt_isSome (read : α → Option Rat)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation)
    (value : α) : ((adapt read consumer).impl value).isSome = (read value).isSome := by
  change ((read value).map _).isSome = (read value).isSome
  cases read value <;> rfl

theorem adapt_sound (read : α → Option Rat)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation)
    (value : α) (q : Rat) (h : read value = some q) :
    ∃ interval, (adapt read consumer).impl value = some interval ∧
      IntervalAnalysis.Contains interval (consumer.spec q) :=
  (adapt read consumer).preserves h

theorem adapt_release (read : α → Option Rat)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation)
    (value : α) (interval : IntervalAnalysis.Interval)
    (h : (adapt read consumer).impl value = some interval) :
    ∃ q, read value = some q ∧ IntervalAnalysis.Contains interval (consumer.spec q) := by
  change (read value).map (fun q => consumer.impl (IntervalAnalysis.singleton q)) = some interval at h
  obtain ⟨q, decoded, same⟩ := Option.map_eq_some_iff.mp h
  exact ⟨q, decoded, same ▸ consumer.preserves (IntervalAnalysis.singleton_contains q)⟩

def squareConsumer :=
  Relational.compose IntervalAnalysis.mulSquare
    (Relational.pair (Relational.identity IntervalAnalysis.representation)
      (Relational.identity IntervalAnalysis.representation))

theorem squareConsumer_singleton (q : Rat) :
    squareConsumer.impl (IntervalAnalysis.singleton q) =
      IntervalAnalysis.singleton (q * q) := by
  change IntervalAnalysis.mul (IntervalAnalysis.singleton q) (IntervalAnalysis.singleton q) = _
  simp [IntervalAnalysis.mul, IntervalAnalysis.singleton]

def square64 := adapt Observation.decode64 squareConsumer
def square32 := adapt Observation.decode32 squareConsumer

theorem square64_isFinite (value : Float) :
    (square64.impl value).isSome = value.isFinite := by
  rw [square64, adapt_isSome, Observation.decode64_isFinite]

theorem square32_isFinite (value : Float32) :
    (square32.impl value).isSome = value.isFinite := by
  rw [square32, adapt_isSome, Observation.decode32_isFinite]

theorem square64_none_iff (value : Float) :
    square64.impl value = none ↔ value.isNaN = true ∨ value.isInf = true := by
  rw [square64, adapt_none_iff, Observation.decode64_none_iff]

theorem square32_none_iff (value : Float32) :
    square32.impl value = none ↔ value.isNaN = true ∨ value.isInf = true := by
  rw [square32, adapt_none_iff, Observation.decode32_none_iff]

theorem square64_sound (value : Float) (q : Rat) (h : Observation.decode64 value = some q) :
    ∃ interval, square64.impl value = some interval ∧ IntervalAnalysis.Contains interval (q * q) :=
  adapt_sound _ _ _ _ h

theorem square32_sound (value : Float32) (q : Rat) (h : Observation.decode32 value = some q) :
    ∃ interval, square32.impl value = some interval ∧ IntervalAnalysis.Contains interval (q * q) :=
  adapt_sound _ _ _ _ h

theorem square64_value (value : Float) (q : Rat) (h : Observation.decode64 value = some q) :
    square64.impl value = some (IntervalAnalysis.singleton (q * q)) := by
  change (Observation.decode64 value).map _ = _
  rw [h]
  exact congrArg some (squareConsumer_singleton q)

theorem square32_value (value : Float32) (q : Rat) (h : Observation.decode32 value = some q) :
    square32.impl value = some (IntervalAnalysis.singleton (q * q)) := by
  change (Observation.decode32 value).map _ = _
  rw [h]
  exact congrArg some (squareConsumer_singleton q)

end Floating.Intervals
