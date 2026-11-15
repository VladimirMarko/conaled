import Applications.Numerals.FloatingBounds
import Examples.FloatingNumerals
import Mathlib.Tactic.NormNum

/-!
# Exact rational step laws and their checked numeral certificates

The rational model makes the generic step-law interface concrete with both
epsilons zero. It does not discharge the later laws for formatted Float/Float32
operations. Negative weights separately exercise the finite envelope's weaker
assumptions. Released rational certificates feed the existing interval consumer.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.FloatingNumeralBounds

open Numerals.Floating Numerals.FloatingError

theorem negative_weight_boundary (s : Step) :
    propagate (fun _ => (-1 : ℚ)) [s, s] = -11 / 10 ∧
    propagate (fun _ => (-1 : ℚ)) [s, s] ≤
      (10 / 9 : ℚ) * (-1) * (1 - 1 / (10 : ℚ) ^ 2) ∧
    ¬ propagate (fun _ => (-1 : ℚ)) [s, s] ≤ (10 / 9 : ℚ) * (-1) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [propagate]
  · simpa only [List.length_cons, List.length_nil] using
      propagate_uniform_length (fun _ => (-1 : ℚ)) [s, s] (-1) (fun _ _ => le_rfl)
  · norm_num [propagate]

def rationalOperations : Operations ℚ where
  zero := 0
  convert := fun d => (d : ℚ)
  add := fun x y => x + y
  divideTen := fun x => x / 10

theorem rational_fraction (digits : List Nat) :
    fraction rationalOperations digits = Numerals.Decimal.fractionRat digits := by
  change Numerals.Decimal.fractionFold digits = _
  exact Numerals.Decimal.fractionFold_eq_fraction digits

theorem rational_step_laws : StepLaws rationalOperations some 0 0 := by
  refine ⟨le_rfl, le_rfl, ?_, ?_, ?_⟩
  · intro d _
    rfl
  · intro d x q hd decoded hq0 hq1
    have hx : x = q := Option.some.inj decoded
    subst x
    refine ⟨(d : ℚ) + q, rfl, add_nonneg (Nat.cast_nonneg d) hq0, ?_, ?_⟩
    · have hdq : (d : ℚ) ≤ 9 := by exact_mod_cast (Nat.le_of_lt_succ hd)
      calc
        (d : ℚ) + q ≤ 9 + 1 := add_le_add hdq hq1
        _ = 10 := by norm_num
    · simp
  · intro x q decoded hq0 hq10
    have hx : x = q := Option.some.inj decoded
    subst x
    refine ⟨q / 10, rfl, div_nonneg hq0 (by norm_num), ?_, ?_⟩
    · exact (div_le_iff₀ (by norm_num : (0 : ℚ) < 10)).mpr (by simpa using hq10)
    · simp

/-- Success is constructed from the laws before its exact value and radius are derived. -/
theorem rational_certificate (digits : List Nat) (hd : Numerals.Decimal.Digits digits) :
    ∃ c, (run rationalOperations some digits).2 = some c ∧
      c.value = Numerals.Decimal.fractionRat digits ∧ operationBound c.steps = 0 := by
  obtain ⟨c, hc, _⟩ := proper_run rationalOperations some rfl 0 0 rational_step_laws digits hd
  have bound : operationBound c.steps ≤ 0 := by
    simpa using proper_operation_bound_length rationalOperations some rfl 0 0
      rational_step_laws digits hd c hc
  have error : |c.value - Numerals.Decimal.fractionRat digits| ≤ 0 := by
    simpa using proper_error rationalOperations some rfl 0 0 rational_step_laws digits hd c hc
  exact ⟨c, hc, sub_eq_zero.mp (abs_nonpos_iff.mp error),
    le_antisymm bound (operationBound_nonneg c.steps)⟩

theorem rational_certify (digits : List Nat) (hd : Numerals.Decimal.Digits digits) :
    certify rationalOperations some digits 0 = true := by
  simpa using proper_certify rationalOperations some rfl 0 0 rational_step_laws digits hd

theorem rational_release (digits : List Nat) (hd : Numerals.Decimal.Digits digits) :
    ∃ c, releaseCertificate rationalOperations some digits 0 = some c ∧
      c.value = Numerals.Decimal.fractionRat digits ∧ operationBound c.steps = 0 := by
  obtain ⟨c, hc, value, radius⟩ := rational_certificate digits hd
  exact ⟨c, (releaseCertificate_eq_some_iff _ _ _ _ _).mpr ⟨hc, le_of_eq radius⟩,
    value, radius⟩

/-- Step laws construct an accepted input to any existing rational interval consumer. -/
theorem proper_consume {α : Type} (ops : Operations α) (read : α → Option ℚ)
    (zero_decodes : read ops.zero = some 0) (a b : ℚ)
    (laws : StepLaws ops read a b) (digits : List Nat) (hd : Numerals.Decimal.Digits digits)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    ∃ value interval, read (fraction ops digits) = some value ∧
      Examples.FloatingNumerals.consume ops read digits ((10 / 9 : ℚ) * (a / 10 + b)) consumer =
        some interval ∧
      IntervalAnalysis.Contains interval (consumer.spec (Numerals.Decimal.fractionRat digits)) := by
  have accepted := proper_certify ops read zero_decodes a b laws digits hd
  have hs : (Examples.FloatingNumerals.consume ops read digits
      ((10 / 9 : ℚ) * (a / 10 + b)) consumer).isSome = true :=
    (Examples.FloatingNumerals.consume_isSome ops read digits _ consumer).trans accepted
  cases released : Examples.FloatingNumerals.consume ops read digits
      ((10 / 9 : ℚ) * (a / 10 + b)) consumer with
  | none => rw [released] at hs; contradiction
  | some interval =>
    obtain ⟨c, _, _, decoded, contained⟩ :=
      Examples.FloatingNumerals.consume_release ops read zero_decodes digits _ consumer interval released
    exact ⟨c.value, interval, decoded, rfl, contained⟩

def rationalSquare (digits : List Nat) : Option IntervalAnalysis.Interval :=
  Examples.FloatingNumerals.consume rationalOperations some digits 0
    _root_.Floating.Intervals.squareConsumer

theorem rationalSquare_proper (digits : List Nat) (hd : Numerals.Decimal.Digits digits) :
    rationalSquare digits = some (IntervalAnalysis.singleton
      (Numerals.Decimal.fractionRat digits * Numerals.Decimal.fractionRat digits)) := by
  obtain ⟨c, released, value, radius⟩ := rational_release digits hd
  have singleton : Examples.FloatingNumerals.enclosure c =
      IntervalAnalysis.singleton (Numerals.Decimal.fractionRat digits) := by
    simp only [Examples.FloatingNumerals.enclosure, radius, value,
      sub_zero, add_zero, IntervalAnalysis.singleton]
  simp only [rationalSquare, Examples.FloatingNumerals.consume, released,
    Option.map_some, singleton, _root_.Floating.Intervals.squareConsumer_singleton]

theorem rationalSquare_contains (digits : List Nat) (hd : Numerals.Decimal.Digits digits) :
    ∃ interval, rationalSquare digits = some interval ∧
      IntervalAnalysis.Contains interval
        (Numerals.Decimal.fractionRat digits * Numerals.Decimal.fractionRat digits) := by
  obtain ⟨_, interval, _, released, contained⟩ :=
    proper_consume rationalOperations some rfl 0 0 rational_step_laws digits hd
      _root_.Floating.Intervals.squareConsumer
  refine ⟨interval, ?_, contained⟩
  simpa only [zero_div, zero_add, mul_zero, rationalSquare] using released

theorem rational_eighth :
    rationalSquare [1, 2, 5] = some (IntervalAnalysis.singleton (1 / 64)) := by
  have hd : Numerals.Decimal.Digits [1, 2, 5] := by
    norm_num [Numerals.Decimal.Digits]
  have h := rationalSquare_proper [1, 2, 5] hd
  norm_num [Numerals.Decimal.fractionRat_spec, Numerals.Decimal.positionalValue, Nat.ofDigits] at h
  exact h

/-- This exact value is positive even though the retained Float32 computation is zero. -/
theorem underflow_exact_fraction :
    Numerals.Decimal.fractionFold (List.replicate 45 0 ++ [1]) = 1 / (10 : ℚ) ^ 46 := by
  decide +kernel

theorem rational_underflow_certificate :
    ∃ c, (run rationalOperations some (List.replicate 45 0 ++ [1])).2 = some c ∧
      c.value = 1 / (10 : ℚ) ^ 46 ∧ operationBound c.steps = 0 ∧
      _root_.Floating.Observation.decode32 (fraction32 (List.replicate 45 0 ++ [1])) = some 0 := by
  have hd : Numerals.Decimal.Digits (List.replicate 45 0 ++ [1]) := by
    intro d h
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at h
    omega
  obtain ⟨c, hc, value, radius⟩ := rational_certificate _ hd
  have exactValue : Numerals.Decimal.fractionRat (List.replicate 45 0 ++ [1]) =
      1 / (10 : ℚ) ^ 46 :=
    (Numerals.Decimal.fractionFold_eq_fraction _).symm.trans underflow_exact_fraction
  exact ⟨c, hc, value.trans exactValue, radius, Examples.FloatingNumerals.fraction32_underflow.2⟩

end Examples.FloatingNumeralBounds
