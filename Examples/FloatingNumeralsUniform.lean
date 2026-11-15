import Applications.Numerals.FloatingUniform
import Examples.FloatingNumeralBounds

/-!
# Actual uniform numeral guarantees consumed by existing intervals

Proper digits now discharge the existing checker's acceptance condition at the
format envelope. The same certificate enclosure and interval-square consumer
therefore contain the original exact decimal's square. Boundary cases reuse
the existing logical floating calculations and retain their distinct meanings.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.FloatingNumerals

open Numerals.Floating Numerals.FloatingError
open _root_.Floating.Observation

theorem consume64_isSome (digits : List Nat) (proper : Numerals.Decimal.Digits digits)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    (consume operations64 decode64 digits ((2 : ℚ) ^ (-52 : Int)) consumer).isSome = true :=
  (consume_isSome operations64 decode64 digits _ consumer).trans (certify64_all_digits digits proper)

theorem consume32_isSome (digits : List Nat) (proper : Numerals.Decimal.Digits digits)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    (consume operations32 decode32 digits ((2 : ℚ) ^ (-23 : Int)) consumer).isSome = true :=
  (consume_isSome operations32 decode32 digits _ consumer).trans (certify32_all_digits digits proper)

/-- Specialize the existing generic consumer composition to actual binary64 arithmetic. -/
theorem consume64_proper (digits : List Nat) (proper : Numerals.Decimal.Digits digits)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    ∃ value interval, decode64 (fraction64 digits) = some value ∧
      consume operations64 decode64 digits ((2 : ℚ) ^ (-52 : Int)) consumer = some interval ∧
      IntervalAnalysis.Contains interval (consumer.spec (Numerals.Decimal.fractionRat digits)) := by
  simpa only [uniform_constant64, fraction_operations64] using
    Examples.FloatingNumeralBounds.proper_consume operations64 decode64 decode64_zero _ _
      stepLaws64 digits proper consumer

theorem consume32_proper (digits : List Nat) (proper : Numerals.Decimal.Digits digits)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :
    ∃ value interval, decode32 (fraction32 digits) = some value ∧
      consume operations32 decode32 digits ((2 : ℚ) ^ (-23 : Int)) consumer = some interval ∧
      IntervalAnalysis.Contains interval (consumer.spec (Numerals.Decimal.fractionRat digits)) := by
  simpa only [uniform_constant32, fraction_operations32] using
    Examples.FloatingNumeralBounds.proper_consume operations32 decode32 decode32_zero _ _
      stepLaws32 digits proper consumer

/-- Acceptance constructs an actual result; soundness targets the original exact decimal. -/
theorem decimalSquare64_all_digits (digits : List Nat) (proper : Numerals.Decimal.Digits digits) :
    ∃ value interval, decode64 (fraction64 digits) = some value ∧
      decimalSquare64 digits ((2 : ℚ) ^ (-52 : Int)) = some interval ∧
      IntervalAnalysis.Contains interval
        (Numerals.Decimal.fractionRat digits * Numerals.Decimal.fractionRat digits) := by
  have success := consume64_isSome digits proper _root_.Floating.Intervals.squareConsumer
  change (decimalSquare64 digits ((2 : ℚ) ^ (-52 : Int))).isSome = true at success
  cases released : decimalSquare64 digits ((2 : ℚ) ^ (-52 : Int)) with
  | none => rw [released] at success; contradiction
  | some interval =>
    obtain ⟨value, observed, contained⟩ := decimalSquare64_sound digits _ interval released
    exact ⟨value, interval, observed, rfl, contained⟩

theorem decimalSquare32_all_digits (digits : List Nat) (proper : Numerals.Decimal.Digits digits) :
    ∃ value interval, decode32 (fraction32 digits) = some value ∧
      decimalSquare32 digits ((2 : ℚ) ^ (-23 : Int)) = some interval ∧
      IntervalAnalysis.Contains interval
        (Numerals.Decimal.fractionRat digits * Numerals.Decimal.fractionRat digits) := by
  have success := consume32_isSome digits proper _root_.Floating.Intervals.squareConsumer
  change (decimalSquare32 digits ((2 : ℚ) ^ (-23 : Int))).isSome = true at success
  cases released : decimalSquare32 digits ((2 : ℚ) ^ (-23 : Int)) with
  | none => rw [released] at success; contradiction
  | some interval =>
    obtain ⟨value, observed, contained⟩ := decimalSquare32_sound digits _ interval released
    exact ⟨value, interval, observed, rfl, contained⟩

/-- A retained observation specializes the constructed universal value bound. -/
theorem uniform64_observed_bounds (digits : List Nat) (proper : Numerals.Decimal.Digits digits)
    (value : ℚ) (observed : decode64 (fraction64 digits) = some value) :
    0 ≤ value ∧ value ≤ 1 ∧
      |value - Numerals.Decimal.fractionRat digits| ≤ (2 : ℚ) ^ (-52 : Int) *
        (1 - 1 / (10 : ℚ) ^ digits.length) ∧
      |value - Numerals.Decimal.fractionRat digits| ≤ (2 : ℚ) ^ (-52 : Int) := by
  obtain ⟨actual, decoded, lower, upper, bounded, uniform⟩ := fraction64_range_error digits proper
  have same : actual = value := Option.some.inj (decoded.symm.trans observed)
  subst actual
  exact ⟨lower, upper, bounded, uniform⟩

theorem uniform32_observed_bounds (digits : List Nat) (proper : Numerals.Decimal.Digits digits)
    (value : ℚ) (observed : decode32 (fraction32 digits) = some value) :
    0 ≤ value ∧ value ≤ 1 ∧
      |value - Numerals.Decimal.fractionRat digits| ≤ (2 : ℚ) ^ (-23 : Int) *
        (1 - 1 / (10 : ℚ) ^ digits.length) ∧
      |value - Numerals.Decimal.fractionRat digits| ≤ (2 : ℚ) ^ (-23 : Int) := by
  obtain ⟨actual, decoded, lower, upper, bounded, uniform⟩ := fraction32_range_error digits proper
  have same : actual = value := Option.some.inj (decoded.symm.trans observed)
  subst actual
  exact ⟨lower, upper, bounded, uniform⟩

theorem uniform_empty64 :
    decode64 (fraction64 []) = some 0 ∧
      |(0 : ℚ) - Numerals.Decimal.fractionRat []| ≤ 0 ∧
      ∃ interval, decimalSquare64 [] ((2 : ℚ) ^ (-52 : Int)) = some interval ∧
        IntervalAnalysis.Contains interval 0 := by
  have proper : Numerals.Decimal.Digits [] := by simp [Numerals.Decimal.Digits]
  have observed : decode64 (fraction64 []) = some 0 := by
    simpa only [fraction64_nil] using decode64_zero
  have bounded := (uniform64_observed_bounds [] proper 0 observed).2.2.1
  obtain ⟨_, interval, _, released, contained⟩ := decimalSquare64_all_digits [] proper
  refine ⟨observed, ?_, interval, released, ?_⟩
  · simpa using bounded
  · simpa [Numerals.Decimal.fractionRat_spec, Numerals.Decimal.positionalValue] using contained

theorem uniform_empty32 :
    decode32 (fraction32 []) = some 0 ∧
      |(0 : ℚ) - Numerals.Decimal.fractionRat []| ≤ 0 ∧
      ∃ interval, decimalSquare32 [] ((2 : ℚ) ^ (-23 : Int)) = some interval ∧
        IntervalAnalysis.Contains interval 0 := by
  have proper : Numerals.Decimal.Digits [] := by simp [Numerals.Decimal.Digits]
  have observed : decode32 (fraction32 []) = some 0 := by
    simpa only [fraction32_nil] using decode32_zero
  have bounded := (uniform32_observed_bounds [] proper 0 observed).2.2.1
  obtain ⟨_, interval, _, released, contained⟩ := decimalSquare32_all_digits [] proper
  refine ⟨observed, ?_, interval, released, ?_⟩
  · simpa using bounded
  · simpa [Numerals.Decimal.fractionRat_spec, Numerals.Decimal.positionalValue] using contained

theorem uniform_eighth64 :
    decode64 (fraction64 [1, 2, 5]) = some (1 / 8 : ℚ) ∧
      |(1 / 8 : ℚ) - Numerals.Decimal.fractionRat [1, 2, 5]| ≤
        (2 : ℚ) ^ (-52 : Int) * (1 - 1 / (10 : ℚ) ^ 3) ∧
      ∃ interval, decimalSquare64 [1, 2, 5] ((2 : ℚ) ^ (-52 : Int)) = some interval ∧
        IntervalAnalysis.Contains interval (1 / 64) := by
  have proper : Numerals.Decimal.Digits [1, 2, 5] := by norm_num [Numerals.Decimal.Digits]
  have bounded := (uniform64_observed_bounds _ proper _ fraction64_eighth.2).2.2.1
  obtain ⟨_, interval, _, released, contained⟩ := decimalSquare64_all_digits _ proper
  refine ⟨fraction64_eighth.2, ?_, interval, released, ?_⟩
  · simpa using bounded
  · norm_num [Numerals.Decimal.fractionRat_spec, Numerals.Decimal.positionalValue, Nat.ofDigits] at contained
    exact contained

theorem uniform_eighth32 :
    decode32 (fraction32 [1, 2, 5]) = some (1 / 8 : ℚ) ∧
      |(1 / 8 : ℚ) - Numerals.Decimal.fractionRat [1, 2, 5]| ≤
        (2 : ℚ) ^ (-23 : Int) * (1 - 1 / (10 : ℚ) ^ 3) ∧
      ∃ interval, decimalSquare32 [1, 2, 5] ((2 : ℚ) ^ (-23 : Int)) = some interval ∧
        IntervalAnalysis.Contains interval (1 / 64) := by
  have proper : Numerals.Decimal.Digits [1, 2, 5] := by norm_num [Numerals.Decimal.Digits]
  have bounded := (uniform32_observed_bounds _ proper _ fraction32_eighth.2).2.2.1
  obtain ⟨_, interval, _, released, contained⟩ := decimalSquare32_all_digits _ proper
  refine ⟨fraction32_eighth.2, ?_, interval, released, ?_⟩
  · simpa using bounded
  · norm_num [Numerals.Decimal.fractionRat_spec, Numerals.Decimal.positionalValue, Nat.ofDigits] at contained
    exact contained

theorem uniform_tenth64 :
    decode64 (fraction64 [1]) ≠ some (1 / 10 : ℚ) ∧
      ∃ value interval, decode64 (fraction64 [1]) = some value ∧
        |value - 1 / 10| ≤ (2 : ℚ) ^ (-52 : Int) * (1 - 1 / 10) ∧
        decimalSquare64 [1] ((2 : ℚ) ^ (-52 : Int)) = some interval ∧
        IntervalAnalysis.Contains interval (1 / 100) := by
  have proper : Numerals.Decimal.Digits [1] := by norm_num [Numerals.Decimal.Digits]
  obtain ⟨value, interval, observed, released, contained⟩ := decimalSquare64_all_digits _ proper
  have bounded := (uniform64_observed_bounds _ proper value observed).2.2.1
  refine ⟨fraction64_tenth.2.2, value, interval, observed, ?_, released, ?_⟩
  · simpa [Numerals.Decimal.fractionRat_spec, Numerals.Decimal.positionalValue, Nat.ofDigits] using bounded
  · norm_num [Numerals.Decimal.fractionRat_spec, Numerals.Decimal.positionalValue, Nat.ofDigits] at contained
    exact contained

theorem uniform_tenth32 :
    decode32 (fraction32 [1]) ≠ some (1 / 10 : ℚ) ∧
      ∃ value interval, decode32 (fraction32 [1]) = some value ∧
        |value - 1 / 10| ≤ (2 : ℚ) ^ (-23 : Int) * (1 - 1 / 10) ∧
        decimalSquare32 [1] ((2 : ℚ) ^ (-23 : Int)) = some interval ∧
        IntervalAnalysis.Contains interval (1 / 100) := by
  have proper : Numerals.Decimal.Digits [1] := by norm_num [Numerals.Decimal.Digits]
  obtain ⟨value, interval, observed, released, contained⟩ := decimalSquare32_all_digits _ proper
  have bounded := (uniform32_observed_bounds _ proper value observed).2.2.1
  refine ⟨fraction32_tenth.2.2, value, interval, observed, ?_, released, ?_⟩
  · simpa [Numerals.Decimal.fractionRat_spec, Numerals.Decimal.positionalValue, Nat.ofDigits] using bounded
  · norm_num [Numerals.Decimal.fractionRat_spec, Numerals.Decimal.positionalValue, Nat.ofDigits] at contained
    exact contained

theorem uniform_nines64 :
    decode64 (fraction64 (List.replicate 17 9)) = some 1 ∧
      Numerals.Decimal.fractionRat (List.replicate 17 9) < 1 ∧
      |(1 : ℚ) - Numerals.Decimal.fractionRat (List.replicate 17 9)| ≤
        (2 : ℚ) ^ (-52 : Int) * (1 - 1 / (10 : ℚ) ^ 17) ∧
      ∃ interval, decimalSquare64 (List.replicate 17 9) ((2 : ℚ) ^ (-52 : Int)) = some interval ∧
        IntervalAnalysis.Contains interval
          (Numerals.Decimal.fractionRat (List.replicate 17 9) *
            Numerals.Decimal.fractionRat (List.replicate 17 9)) := by
  have proper := fraction64_strict_bound_counterexample.1
  have bounded := (uniform64_observed_bounds _ proper 1 fraction64_nines_round_to_one.2).2.2.1
  obtain ⟨_, interval, _, released, contained⟩ := decimalSquare64_all_digits _ proper
  refine ⟨fraction64_nines_round_to_one.2, Numerals.Decimal.fractionRat_lt_one _ proper,
    ?_, interval, released, contained⟩
  simpa only [List.length_replicate] using bounded

theorem uniform_nines32 :
    decode32 (fraction32 (List.replicate 8 9)) = some 1 ∧
      Numerals.Decimal.fractionRat (List.replicate 8 9) < 1 ∧
      |(1 : ℚ) - Numerals.Decimal.fractionRat (List.replicate 8 9)| ≤
        (2 : ℚ) ^ (-23 : Int) * (1 - 1 / (10 : ℚ) ^ 8) ∧
      ∃ interval, decimalSquare32 (List.replicate 8 9) ((2 : ℚ) ^ (-23 : Int)) = some interval ∧
        IntervalAnalysis.Contains interval
          (Numerals.Decimal.fractionRat (List.replicate 8 9) *
            Numerals.Decimal.fractionRat (List.replicate 8 9)) := by
  have proper := fraction32_strict_bound_counterexample.1
  have bounded := (uniform32_observed_bounds _ proper 1 fraction32_nines_round_to_one.2).2.2.1
  obtain ⟨_, interval, _, released, contained⟩ := decimalSquare32_all_digits _ proper
  refine ⟨fraction32_nines_round_to_one.2, Numerals.Decimal.fractionRat_lt_one _ proper,
    ?_, interval, released, contained⟩
  simpa only [List.length_replicate] using bounded

theorem uniform_underflow32_digits : Numerals.Decimal.Digits (List.replicate 45 0 ++ [1]) := by
  intro digit member
  simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at member
  omega

/-- The original remains positive while the actual result is zero. -/
theorem uniform_underflow32 :
    0 < Numerals.Decimal.fractionRat (List.replicate 45 0 ++ [1]) ∧
      decode32 (fraction32 (List.replicate 45 0 ++ [1])) = some 0 ∧
      |(0 : ℚ) - Numerals.Decimal.fractionRat (List.replicate 45 0 ++ [1])| ≤
        (2 : ℚ) ^ (-23 : Int) * (1 - 1 / (10 : ℚ) ^ 46) ∧
      ∃ interval, decimalSquare32 (List.replicate 45 0 ++ [1]) ((2 : ℚ) ^ (-23 : Int)) = some interval ∧
        IntervalAnalysis.Contains interval ((1 / (10 : ℚ) ^ 46) * (1 / (10 : ℚ) ^ 46)) := by
  have positive : 0 < Numerals.Decimal.fractionRat (List.replicate 45 0 ++ [1]) := by
    simpa only [Numerals.Decimal.fractionFold_eq_fraction] using fraction32_underflow_positive_exact.1
  have exactValue : Numerals.Decimal.fractionRat (List.replicate 45 0 ++ [1]) =
      1 / (10 : ℚ) ^ 46 :=
    (Numerals.Decimal.fractionFold_eq_fraction _).symm.trans
      Examples.FloatingNumeralBounds.underflow_exact_fraction
  have bounded :=
    (uniform32_observed_bounds _ uniform_underflow32_digits 0 fraction32_underflow.2).2.2.1
  obtain ⟨_, interval, _, released, contained⟩ :=
    decimalSquare32_all_digits _ uniform_underflow32_digits
  refine ⟨positive, fraction32_underflow.2, ?_, interval, released, ?_⟩
  · simpa using bounded
  · simpa only [exactValue] using contained

end Examples.FloatingNumerals
