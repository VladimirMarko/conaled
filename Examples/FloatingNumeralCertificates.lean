import Applications.Numerals.FloatingCertificates
import Mathlib.Tactic.NormNum

/-!
# Concrete source certificates and observer boundaries

The displayed tolerances check the propagated separate-operation bound. The
synthetic operation records below exercise the generic API's assumptions; they
are not models of IEEE arithmetic.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.FloatingNumerals

open Numerals.Floating Numerals.FloatingError
open _root_.Floating.Observation

theorem certified_examples64 :
    certify64 [] 0 = true ∧ certify64 [1, 2, 5] 0 = true ∧
    certify64 [1, 4, 8, 4, 9, 3] (1 / (2 : ℚ) ^ 52) = true ∧
    certify64 (List.replicate 17 9) (1 / (2 : ℚ) ^ 52) = true ∧
    certify64 [0, 7] (1 / (2 : ℚ) ^ 52) = true := by
  decide +kernel

theorem certified_examples32 :
    certify32 [] 0 = true ∧ certify32 [1, 2, 5] 0 = true ∧
    certify32 [1, 4, 8, 4, 9, 3] (1 / (2 : ℚ) ^ 23) = true ∧
    certify32 (List.replicate 8 9) (1 / (2 : ℚ) ^ 23) = true ∧
    certify32 [0, 3] (1 / (2 : ℚ) ^ 23) = true := by
  decide +kernel

theorem certified_underflow32 :
    certify32 (List.replicate 45 0 ++ [1]) (1 / (2 : ℚ) ^ 149) = true := by
  decide +kernel

theorem zero_tolerance_rejects_inexact_tenth :
    certify64 [1] 0 = false ∧ certify32 [1] 0 = false := by
  decide +kernel

theorem conversion_overflow_rejected :
    analyze64 [2 ^ 1024] = none ∧ analyze32 [2 ^ 128] = none := by
  decide +kernel

theorem printed_error_bound64 :
    ∃ value, decode64 (fraction64 [1, 4, 8, 4, 9, 3]) = some value ∧
      |value - Numerals.Decimal.fractionRat [1, 4, 8, 4, 9, 3]| ≤ 1 / (2 : ℚ) ^ 52 :=
  certify64_sound _ _ certified_examples64.2.2.1

theorem printed_error_bound32 :
    ∃ value, decode32 (fraction32 [1, 4, 8, 4, 9, 3]) = some value ∧
      |value - Numerals.Decimal.fractionRat [1, 4, 8, 4, 9, 3]| ≤ 1 / (2 : ℚ) ^ 23 :=
  certify32_sound _ _ certified_examples32.2.2.1

def eighthCertificate : Certificate :=
  ⟨1 / 8, [⟨1, 1 / 4, 1, 5 / 4, 1 / 8⟩,
    ⟨2, 1 / 2, 2, 5 / 2, 1 / 4⟩, ⟨5, 0, 5, 5, 1 / 2⟩]⟩

theorem analyze64_eighth : analyze64 [1, 2, 5] = some eighthCertificate := by
  decide +kernel

theorem analyze32_eighth : analyze32 [1, 2, 5] = some eighthCertificate := by
  decide +kernel

theorem eighth_operation_bound : operationBound eighthCertificate.steps = 0 := by
  norm_num [eighthCertificate, operationBound, propagate, Step.operationBound,
    Step.conversionError, Step.additionError, Step.divisionError]

theorem release64_eighth :
    releaseCertificate operations64 decode64 [1, 2, 5] 0 = some eighthCertificate := by
  apply (releaseCertificate_eq_some_iff _ _ _ _ _).mpr
  exact ⟨analyze64_eighth, le_of_eq eighth_operation_bound⟩

theorem release32_eighth :
    releaseCertificate operations32 decode32 [1, 2, 5] 0 = some eighthCertificate := by
  apply (releaseCertificate_eq_some_iff _ _ _ _ _).mpr
  exact ⟨analyze32_eighth, le_of_eq eighth_operation_bound⟩

def wrongSeed : Operations Nat := ⟨7, id, Nat.add, id⟩
def readNat (n : Nat) : Option ℚ := some (n : ℚ)

/-- The law-free erasure still holds when the actual seed does not decode as zero. -/
theorem wrong_seed_value_erasure :
    (run wrongSeed readNat []).1 = fraction wrongSeed [] :=
  run_value wrongSeed readNat []

theorem wrong_seed_certificate :
    (run wrongSeed readNat []).1 = 7 ∧
    (run wrongSeed readNat []).2 = some ⟨0, []⟩ ∧
    certify wrongSeed readNat [] 0 = true ∧ readNat wrongSeed.zero ≠ some 0 := by
  norm_num [wrongSeed, readNat, run, certify, operationBound, propagate]

def recoverAfterRejectedStage : Operations Nat := ⟨0, id, Nat.add, fun _ => 0⟩
def rejectEleven (n : Nat) : Option ℚ := if n = 11 then none else readNat n

/-- Final decodability cannot replace the observer's required intermediate checks. -/
theorem intermediate_rejection :
    rejectEleven recoverAfterRejectedStage.zero = some 0 ∧
    rejectEleven (fraction recoverAfterRejectedStage [11]) = some 0 ∧
    (run recoverAfterRejectedStage rejectEleven [11]).2 = none := by
  norm_num [recoverAfterRejectedStage, rejectEleven, readNat, fraction, run, observeStep]

theorem rejected_stage_domain : ¬ FiniteRun recoverAfterRejectedStage rejectEleven [11] :=
  (run_none_iff recoverAfterRejectedStage rejectEleven [11]).mp intermediate_rejection.2.2

/-- A rational trace exhibiting cancellation; no actual IEEE execution is asserted. -/
def cancellationTail : Step := ⟨5, 0, 5, 5, 51 / 100⟩
def cancellationHead : Step := ⟨2, 51 / 100, 2, 251 / 100, 1 / 4⟩

theorem cancellation_trace :
    Trace [2, 5] [cancellationHead, cancellationTail] (1 / 4) :=
  Trace.cons cancellationHead (Trace.cons cancellationTail Trace.nil)

theorem cancellation_bounds :
    signedError [cancellationHead, cancellationTail] = 0 ∧
    operationBound [cancellationHead, cancellationTail] = 1 / 500 := by
  norm_num [signedError, operationBound, propagate, cancellationHead, cancellationTail,
    Step.localError, Step.operationBound, Step.conversionError, Step.additionError, Step.divisionError]

theorem cancellation_exact_value : (1 / 4 : ℚ) = Numerals.Decimal.fractionFold [2, 5] := by
  have h := trace_error_identity cancellation_trace
  rw [cancellation_bounds.1, add_zero] at h
  exact h

end Examples.FloatingNumerals
