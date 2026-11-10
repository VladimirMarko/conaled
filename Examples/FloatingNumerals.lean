import Examples.FloatingNumeralsValues
import Examples.FloatingNumeralCertificates
import Applications.Floating.Intervals

/-!
# Consuming accepted numeral error enclosures

The interval surrounds the decoded binary result by its certified operation
bound, so it contains the intended exact decimal. An existing interval consumer
then acts on that enclosure. Rejection remains `none`; no unconditional square
from all digit lists to successful outputs is asserted.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.FloatingNumerals

open Numerals.Floating Numerals.FloatingError
open _root_.Floating.Observation
variable {α : Type}

def enclosure (c : Certificate) : IntervalAnalysis.Interval :=
  ⟨c.value - operationBound c.steps, c.value + operationBound c.steps⟩

theorem certificate_encloses (digits : List Nat) (c : Certificate)
    (trace : Trace digits c.steps c.value) :
    IntervalAnalysis.Contains (enclosure c) (Numerals.Decimal.fractionRat digits) := by
  have bound := abs_le.mp (trace_operation_error trace)
  constructor <;> dsimp [enclosure] <;> linarith

def consume (ops : Operations α) (read : α → Option ℚ)
    (digits : List Nat) (tolerance : ℚ)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    Option IntervalAnalysis.Interval :=
  (releaseCertificate ops read digits tolerance).map (fun c => consumer.impl (enclosure c))

theorem consume_eq_some_iff (ops : Operations α) (read : α → Option ℚ)
    (digits : List Nat) (tolerance : ℚ)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation)
    (interval : IntervalAnalysis.Interval) :
    consume ops read digits tolerance consumer = some interval ↔
      ∃ c, releaseCertificate ops read digits tolerance = some c ∧
        consumer.impl (enclosure c) = interval := by
  cases released : releaseCertificate ops read digits tolerance <;> simp [consume, released]

theorem consume_isSome (ops : Operations α) (read : α → Option ℚ)
    (digits : List Nat) (tolerance : ℚ)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    (consume ops read digits tolerance consumer).isSome = certify ops read digits tolerance := by
  have h : (consume ops read digits tolerance consumer).isSome =
      (releaseCertificate ops read digits tolerance).isSome := by
    cases released : releaseCertificate ops read digits tolerance <;> simp [consume, released]
  exact h.trans (releaseCertificate_isSome ops read digits tolerance)

theorem consume_none_iff (ops : Operations α) (read : α → Option ℚ)
    (digits : List Nat) (tolerance : ℚ)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    consume ops read digits tolerance consumer = none ↔ certify ops read digits tolerance = false := by
  have h := consume_isSome ops read digits tolerance consumer
  cases result : consume ops read digits tolerance consumer <;> simp_all

/-- Successful release recovers the actual decoded value and the accepted bound. -/
theorem consume_release (ops : Operations α) (read : α → Option ℚ)
    (zero_decodes : read ops.zero = some 0) (digits : List Nat) (tolerance : ℚ)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation)
    (interval : IntervalAnalysis.Interval)
    (released : consume ops read digits tolerance consumer = some interval) :
    ∃ c, (run ops read digits).2 = some c ∧ operationBound c.steps ≤ tolerance ∧
      read (fraction ops digits) = some c.value ∧
      IntervalAnalysis.Contains interval (consumer.spec (Numerals.Decimal.fractionRat digits)) := by
  obtain ⟨c, hc, rfl⟩ := (consume_eq_some_iff ops read digits tolerance consumer interval).mp released
  obtain ⟨produced, _⟩ := (releaseCertificate_eq_some_iff ops read digits tolerance c).mp hc
  obtain ⟨decoded, trace, bound, _⟩ :=
    releaseCertificate_sound ops read zero_decodes digits tolerance c hc
  exact ⟨c, produced, bound, decoded, consumer.preserves (certificate_encloses digits c trace)⟩

def decimalSquare64 (digits : List Nat) (tolerance : ℚ) : Option IntervalAnalysis.Interval :=
  consume operations64 decode64 digits tolerance _root_.Floating.Intervals.squareConsumer

def decimalSquare32 (digits : List Nat) (tolerance : ℚ) : Option IntervalAnalysis.Interval :=
  consume operations32 decode32 digits tolerance _root_.Floating.Intervals.squareConsumer

theorem decimalSquare64_sound (digits : List Nat) (tolerance : ℚ)
    (interval : IntervalAnalysis.Interval) (h : decimalSquare64 digits tolerance = some interval) :
    ∃ value, decode64 (fraction64 digits) = some value ∧
      IntervalAnalysis.Contains interval
        (Numerals.Decimal.fractionRat digits * Numerals.Decimal.fractionRat digits) := by
  obtain ⟨c, _, _, decoded, contained⟩ :=
    consume_release operations64 decode64 decode64_zero digits tolerance
      _root_.Floating.Intervals.squareConsumer interval h
  exact ⟨c.value, decoded, contained⟩

theorem decimalSquare32_sound (digits : List Nat) (tolerance : ℚ)
    (interval : IntervalAnalysis.Interval) (h : decimalSquare32 digits tolerance = some interval) :
    ∃ value, decode32 (fraction32 digits) = some value ∧
      IntervalAnalysis.Contains interval
        (Numerals.Decimal.fractionRat digits * Numerals.Decimal.fractionRat digits) := by
  obtain ⟨c, _, _, decoded, contained⟩ :=
    consume_release operations32 decode32 decode32_zero digits tolerance
      _root_.Floating.Intervals.squareConsumer interval h
  exact ⟨c.value, decoded, contained⟩

theorem enclosure_eighth : enclosure eighthCertificate = IntervalAnalysis.singleton (1 / 8) := by
  unfold enclosure
  rw [eighth_operation_bound]
  norm_num [eighthCertificate, IntervalAnalysis.singleton]

theorem decimalSquare64_eighth :
    decimalSquare64 [1, 2, 5] 0 = some (IntervalAnalysis.singleton (1 / 64)) := by
  simp only [decimalSquare64, consume, release64_eighth, Option.map_some, enclosure_eighth,
    _root_.Floating.Intervals.squareConsumer_singleton]
  norm_num

theorem decimalSquare32_eighth :
    decimalSquare32 [1, 2, 5] 0 = some (IntervalAnalysis.singleton (1 / 64)) := by
  simp only [decimalSquare32, consume, release32_eighth, Option.map_some, enclosure_eighth,
    _root_.Floating.Intervals.squareConsumer_singleton]
  norm_num

theorem decimalSquare64_tenth :
    ∃ interval, decimalSquare64 [1] (1 / (2 : ℚ) ^ 54) = some interval ∧
      IntervalAnalysis.Contains interval (1 / 100) := by
  have accepted := certify64_single_digit 1 (by decide)
  have hs : (decimalSquare64 [1] (1 / (2 : ℚ) ^ 54)).isSome = true :=
    (consume_isSome operations64 decode64 [1] _ _).trans accepted
  cases h : decimalSquare64 [1] (1 / (2 : ℚ) ^ 54) with
  | none => rw [h] at hs; contradiction
  | some interval =>
    obtain ⟨_, _, contained⟩ := decimalSquare64_sound [1] _ interval h
    refine ⟨interval, rfl, ?_⟩
    norm_num [Numerals.Decimal.fractionRat_spec, Numerals.Decimal.positionalValue, Nat.ofDigits] at contained
    exact contained

theorem decimalSquare32_tenth :
    ∃ interval, decimalSquare32 [1] (1 / (2 : ℚ) ^ 25) = some interval ∧
      IntervalAnalysis.Contains interval (1 / 100) := by
  have accepted := certify32_single_digit 1 (by decide)
  have hs : (decimalSquare32 [1] (1 / (2 : ℚ) ^ 25)).isSome = true :=
    (consume_isSome operations32 decode32 [1] _ _).trans accepted
  cases h : decimalSquare32 [1] (1 / (2 : ℚ) ^ 25) with
  | none => rw [h] at hs; contradiction
  | some interval =>
    obtain ⟨_, _, contained⟩ := decimalSquare32_sound [1] _ interval h
    refine ⟨interval, rfl, ?_⟩
    norm_num [Numerals.Decimal.fractionRat_spec, Numerals.Decimal.positionalValue, Nat.ofDigits] at contained
    exact contained

theorem zero_tolerance_pipeline_rejects :
    decimalSquare64 [1] 0 = none ∧ decimalSquare32 [1] 0 = none := by
  exact ⟨(consume_none_iff _ _ _ _ _).mpr zero_tolerance_rejects_inexact_tenth.1,
    (consume_none_iff _ _ _ _ _).mpr zero_tolerance_rejects_inexact_tenth.2⟩

theorem overflow_pipeline_rejects (tolerance : ℚ) :
    decimalSquare64 [2 ^ 1024] tolerance = none ∧
    decimalSquare32 [2 ^ 128] tolerance = none := by
  have h64 := conversion_overflow_rejected.1
  have h32 := conversion_overflow_rejected.2
  change (run operations64 decode64 [2 ^ 1024]).2 = none at h64
  change (run operations32 decode32 [2 ^ 128]).2 = none at h32
  simp only [decimalSquare64, decimalSquare32, consume, releaseCertificate, h64, h32,
    Option.map_none, and_self]

end Examples.FloatingNumerals
