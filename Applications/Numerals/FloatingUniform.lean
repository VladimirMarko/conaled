import Applications.Numerals.FloatingBounds
import Applications.Floating.Operations

/-!
# Uniform guarantees for actual floating numeral folds

The actual format operations discharge the existing separated step laws. The
generic proper-run induction then constructs every finite stage, the complete
certificate and the closed output range. Error is measured against the
independent exact decimal, with both its finite-length bound and uniform envelope.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Numerals.Floating

open Numerals.FloatingError
open _root_.Floating.Observation

theorem stepLaws64 : StepLaws operations64 decode64 ((2 : ℚ) ^ (-50 : Int))
    ((2 : ℚ) ^ (-53 : Int)) where
  addition_nonneg := le_of_lt (zpow_pos (by norm_num : (0 : ℚ) < 2) _)
  division_nonneg := le_of_lt (zpow_pos (by norm_num : (0 : ℚ) < 2) _)
  digit_exact := decode64_digit
  addition := _root_.Floating.Operations.add64_bounds
  division := _root_.Floating.Operations.divideTen64_bounds

theorem stepLaws32 : StepLaws operations32 decode32 ((2 : ℚ) ^ (-21 : Int))
    ((2 : ℚ) ^ (-24 : Int)) where
  addition_nonneg := le_of_lt (zpow_pos (by norm_num : (0 : ℚ) < 2) _)
  division_nonneg := le_of_lt (zpow_pos (by norm_num : (0 : ℚ) < 2) _)
  digit_exact := decode32_digit
  addition := _root_.Floating.Operations.add32_bounds
  division := _root_.Floating.Operations.divideTen32_bounds

theorem uniform_constant64 :
    (10 / 9 : ℚ) * ((2 : ℚ) ^ (-50 : Int) / 10 + (2 : ℚ) ^ (-53 : Int)) =
      (2 : ℚ) ^ (-52 : Int) := by decide +kernel

theorem uniform_constant32 :
    (10 / 9 : ℚ) * ((2 : ℚ) ^ (-21 : Int) / 10 + (2 : ℚ) ^ (-24 : Int)) =
      (2 : ℚ) ^ (-23 : Int) := by decide +kernel

theorem finiteRun64 (digits : List Nat) (proper : Decimal.Digits digits) :
    FiniteRun operations64 decode64 digits :=
  proper_finite_run operations64 decode64 decode64_zero _ _ stepLaws64 digits proper

theorem finiteRun32 (digits : List Nat) (proper : Decimal.Digits digits) :
    FiniteRun operations32 decode32 digits :=
  proper_finite_run operations32 decode32 decode32_zero _ _ stepLaws32 digits proper

/-- Every recorded conversion, addition and quotient is finite in the actual format. -/
theorem stagesFinite64 (digits : List Nat) (proper : Decimal.Digits digits) :
    StagesFinite operations64 Float.isFinite digits := by
  simpa only [FiniteRun, decode64_isFinite] using finiteRun64 digits proper

theorem stagesFinite32 (digits : List Nat) (proper : Decimal.Digits digits) :
    StagesFinite operations32 Float32.isFinite digits := by
  simpa only [FiniteRun, decode32_isFinite] using finiteRun32 digits proper

theorem analyze64_complete (digits : List Nat) (proper : Decimal.Digits digits) :
    ∃ c, analyze64 digits = some c ∧ decode64 (fraction64 digits) = some c.value ∧
      0 ≤ c.value ∧ c.value ≤ 1 ∧ c.steps.length = digits.length ∧
      operationBound c.steps ≤ (2 : ℚ) ^ (-52 : Int) *
        (1 - 1 / (10 : ℚ) ^ digits.length) := by
  obtain ⟨c, produced, observed, lower, upper, _⟩ :=
    proper_run operations64 decode64 decode64_zero _ _ stepLaws64 digits proper
  refine ⟨c, produced, ?_, lower, upper, run_length operations64 decode64 digits c produced, ?_⟩
  · simpa only [fraction_operations64] using observed
  · simpa only [uniform_constant64] using
      proper_operation_bound_length operations64 decode64 decode64_zero _ _
        stepLaws64 digits proper c produced

theorem analyze32_complete (digits : List Nat) (proper : Decimal.Digits digits) :
    ∃ c, analyze32 digits = some c ∧ decode32 (fraction32 digits) = some c.value ∧
      0 ≤ c.value ∧ c.value ≤ 1 ∧ c.steps.length = digits.length ∧
      operationBound c.steps ≤ (2 : ℚ) ^ (-23 : Int) *
        (1 - 1 / (10 : ℚ) ^ digits.length) := by
  obtain ⟨c, produced, observed, lower, upper, _⟩ :=
    proper_run operations32 decode32 decode32_zero _ _ stepLaws32 digits proper
  refine ⟨c, produced, ?_, lower, upper, run_length operations32 decode32 digits c produced, ?_⟩
  · simpa only [fraction_operations32] using observed
  · simpa only [uniform_constant32] using
      proper_operation_bound_length operations32 decode32 decode32_zero _ _
        stepLaws32 digits proper c produced

theorem observations64_bounds (digits : List Nat) (proper : Decimal.Digits digits)
    (c : Certificate) (produced : analyze64 digits = some c) :
    ∀ s ∈ c.steps, StepBounds ((2 : ℚ) ^ (-50 : Int)) ((2 : ℚ) ^ (-53 : Int)) s :=
  (proper_certificate operations64 decode64 decode64_zero _ _ stepLaws64 digits proper c produced).2.2

theorem observations32_bounds (digits : List Nat) (proper : Decimal.Digits digits)
    (c : Certificate) (produced : analyze32 digits = some c) :
    ∀ s ∈ c.steps, StepBounds ((2 : ℚ) ^ (-21 : Int)) ((2 : ℚ) ^ (-24 : Int)) s :=
  (proper_certificate operations32 decode32 decode32_zero _ _ stepLaws32 digits proper c produced).2.2

/-- The independent decimal error retains the finite-length factor and coarse envelope. -/
theorem fraction64_range_error (digits : List Nat) (proper : Decimal.Digits digits) :
    ∃ value, decode64 (fraction64 digits) = some value ∧ 0 ≤ value ∧ value ≤ 1 ∧
      |value - Decimal.fractionRat digits| ≤ (2 : ℚ) ^ (-52 : Int) *
        (1 - 1 / (10 : ℚ) ^ digits.length) ∧
      |value - Decimal.fractionRat digits| ≤ (2 : ℚ) ^ (-52 : Int) := by
  obtain ⟨c, produced, observed, lower, upper, _⟩ :=
    proper_run operations64 decode64 decode64_zero _ _ stepLaws64 digits proper
  refine ⟨c.value, ?_, lower, upper, ?_, ?_⟩
  · simpa only [fraction_operations64] using observed
  · simpa only [uniform_constant64] using
      proper_error_length operations64 decode64 decode64_zero _ _ stepLaws64 digits proper c produced
  · simpa only [uniform_constant64] using
      proper_error operations64 decode64 decode64_zero _ _ stepLaws64 digits proper c produced

theorem fraction32_range_error (digits : List Nat) (proper : Decimal.Digits digits) :
    ∃ value, decode32 (fraction32 digits) = some value ∧ 0 ≤ value ∧ value ≤ 1 ∧
      |value - Decimal.fractionRat digits| ≤ (2 : ℚ) ^ (-23 : Int) *
        (1 - 1 / (10 : ℚ) ^ digits.length) ∧
      |value - Decimal.fractionRat digits| ≤ (2 : ℚ) ^ (-23 : Int) := by
  obtain ⟨c, produced, observed, lower, upper, _⟩ :=
    proper_run operations32 decode32 decode32_zero _ _ stepLaws32 digits proper
  refine ⟨c.value, ?_, lower, upper, ?_, ?_⟩
  · simpa only [fraction_operations32] using observed
  · simpa only [uniform_constant32] using
      proper_error_length operations32 decode32 decode32_zero _ _ stepLaws32 digits proper c produced
  · simpa only [uniform_constant32] using
      proper_error operations32 decode32 decode32_zero _ _ stepLaws32 digits proper c produced

theorem fraction64_isFinite (digits : List Nat) (proper : Decimal.Digits digits) :
    (fraction64 digits).isFinite = true := by
  obtain ⟨value, observed, _⟩ := fraction64_range_error digits proper
  apply (decode64_isSome_iff _).mp
  rw [observed]
  rfl

theorem fraction32_isFinite (digits : List Nat) (proper : Decimal.Digits digits) :
    (fraction32 digits).isFinite = true := by
  obtain ⟨value, observed, _⟩ := fraction32_range_error digits proper
  apply (decode32_isSome_iff _).mp
  rw [observed]
  rfl

theorem fraction64_exact_fold_error (digits : List Nat) (proper : Decimal.Digits digits) :
    ∃ value, decode64 (fraction64 digits) = some value ∧
      |value - Decimal.fractionFold digits| ≤ (2 : ℚ) ^ (-52 : Int) := by
  obtain ⟨value, observed, _, _, _, error⟩ := fraction64_range_error digits proper
  exact ⟨value, observed, by simpa only [Decimal.fractionFold_eq_fraction] using error⟩

theorem fraction32_exact_fold_error (digits : List Nat) (proper : Decimal.Digits digits) :
    ∃ value, decode32 (fraction32 digits) = some value ∧
      |value - Decimal.fractionFold digits| ≤ (2 : ℚ) ^ (-23 : Int) := by
  obtain ⟨value, observed, _, _, _, error⟩ := fraction32_range_error digits proper
  exact ⟨value, observed, by simpa only [Decimal.fractionFold_eq_fraction] using error⟩

theorem fraction64_exact_fold_error_length (digits : List Nat) (proper : Decimal.Digits digits) :
    ∃ value, decode64 (fraction64 digits) = some value ∧
      |value - Decimal.fractionFold digits| ≤ (2 : ℚ) ^ (-52 : Int) *
        (1 - 1 / (10 : ℚ) ^ digits.length) := by
  obtain ⟨value, observed, _, _, error, _⟩ := fraction64_range_error digits proper
  exact ⟨value, observed, by simpa only [Decimal.fractionFold_eq_fraction] using error⟩

theorem fraction32_exact_fold_error_length (digits : List Nat) (proper : Decimal.Digits digits) :
    ∃ value, decode32 (fraction32 digits) = some value ∧
      |value - Decimal.fractionFold digits| ≤ (2 : ℚ) ^ (-23 : Int) *
        (1 - 1 / (10 : ℚ) ^ digits.length) := by
  obtain ⟨value, observed, _, _, error, _⟩ := fraction32_range_error digits proper
  exact ⟨value, observed, by simpa only [Decimal.fractionFold_eq_fraction] using error⟩

theorem certify64_all_digits (digits : List Nat) (proper : Decimal.Digits digits) :
    certify64 digits ((2 : ℚ) ^ (-52 : Int)) = true := by
  simpa only [certify64, uniform_constant64] using
    proper_certify operations64 decode64 decode64_zero _ _ stepLaws64 digits proper

theorem certify32_all_digits (digits : List Nat) (proper : Decimal.Digits digits) :
    certify32 digits ((2 : ℚ) ^ (-23 : Int)) = true := by
  simpa only [certify32, uniform_constant32] using
    proper_certify operations32 decode32 decode32_zero _ _ stepLaws32 digits proper

end Numerals.Floating
