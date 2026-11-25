import Applications.Resources.PolynomialTime.NormalForm
import Applications.Resources.RotationCertificate.DelimiterTapeMachine

set_option autoImplicit false
set_option warningAsError true

/-!
# Polynomial bounds for delimiter execution

A fixed whole-program action bound determines a polynomial and power
allowance. Widening the allowance preserves the actual target run.
-/

/- Complete preserved component: polynomial_consumer. -/
section

namespace Resources.RotationCertificate.DelimiterMachine.PolynomialTime

open Turing
open Resources.TuringSimulation
open Native

/-- A proof-side polynomial mirroring the existing conventional allowance. -/
noncomputable def timePolynomial (A : Nat) : Polynomial Nat :=
  Polynomial.C 2 * (Polynomial.X + Polynomial.C 3 +
    Polynomial.C 3 *
      (Polynomial.C 4 * Polynomial.X * Polynomial.X +
        Polynomial.C 23 * Polynomial.X + Polynomial.C 38) *
      (Polynomial.C 1 + Polynomial.C A *
        (Polynomial.C 2 * (Polynomial.C 2 * Polynomial.X +
          Polynomial.C 1 + Polynomial.C A) + Polynomial.C 2))) + Polynomial.C 1

theorem timePolynomial_eval (A N : Nat) :
    (timePolynomial A).eval N = 2 * ordinaryTimeBound A N + 1 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, ordinaryTimeBound,
    encodedPrimitiveTimeBound, sourceTimeBound]

/-- This number depends on the whole program's fixed A, before any raw word. -/
noncomputable def powerExponent (A : Nat) : Nat :=
  Resources.PolynomialTime.NormalForm.exponent (timePolynomial A)

theorem polynomial_le_power (A N : Nat) :
    (timePolynomial A).eval N ≤ N ^ powerExponent A + powerExponent A :=
  Resources.PolynomialTime.NormalForm.eval_le_power_add_exponent
    (timePolynomial A) N

/-- The unchanged conventional budget includes its existing decision step. -/
theorem allowance_le_power (A : Nat) (raw : Raw) :
    2 * (MarkedInput.preludeSteps raw +
      encodedPrimitiveTimeBound A raw.length + 1) + 1 ≤
        raw.length ^ powerExponent A + powerExponent A := by
  calc
    2 * (MarkedInput.preludeSteps raw +
        encodedPrimitiveTimeBound A raw.length + 1) + 1 ≤
        2 * ordinaryTimeBound A raw.length + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 (ordinary_allowance_le A raw)) 1
    _ = (timePolynomial A).eval raw.length := (timePolynomial_eval A raw.length).symm
    _ ≤ raw.length ^ powerExponent A + powerExponent A :=
      polynomial_le_power A raw.length

/-- At empty input the uniform polynomial has exactly two steps of slack. -/
theorem empty_allowance_slack (A : Nat) :
    (2 * (MarkedInput.preludeSteps ([] : Raw) +
      encodedPrimitiveTimeBound A 0 + 1) + 1) + 2 = (timePolynomial A).eval 0 := by
  rw [timePolynomial_eval]
  change (2 * (1 + encodedPrimitiveTimeBound A 0 + 1) + 1) + 2 =
    2 * ordinaryTimeBound A 0 + 1
  unfold ordinaryTimeBound
  omega

/-- All three one-letter inputs have exactly the polynomial allowance. -/
theorem singleton_allowance (A : Nat) (letter : Option Bool) :
    2 * (MarkedInput.preludeSteps [letter] +
      encodedPrimitiveTimeBound A 1 + 1) + 1 = (timePolynomial A).eval 1 := by
  rw [timePolynomial_eval]
  change 2 * (3 + encodedPrimitiveTimeBound A 1 + 1) + 1 =
    2 * ordinaryTimeBound A 1 + 1
  unfold ordinaryTimeBound
  omega

theorem polynomial_zero_le_power (A : Nat) :
    (timePolynomial A).eval 0 ≤ 0 ^ powerExponent A + powerExponent A :=
  polynomial_le_power A 0

theorem polynomial_one_le_power (A : Nat) :
    (timePolynomial A).eval 1 ≤ 1 ^ powerExponent A + powerExponent A :=
  polynomial_le_power A 1

variable {R : Type} [Fintype R]

/-- Concrete native and conventional witnesses with their original complete
endpoints and count observations. Only the target allowance is a parameter. -/
def Run (initial : R) [DecidableEq (Alphabet initial)] (raw : Raw) (bound : Nat) : Prop :=
  ∃ native : StateTransition.EvalsToInTime (TM0.step (ordinaryMachine initial))
      (TM0.init (ordinaryInput initial raw))
      (some (ordinaryOutput initial (verifyDelimited raw)))
      (MarkedInput.preludeSteps raw +
        encodedPrimitiveTimeBound (actionMaximum (R := R)) raw.length + 1),
    ∃ target : StateTransition.EvalsToInTime (PrintMove.step (conventionalMachine initial))
        (PrintMove.init (.normal .start) (ordinaryInput initial raw))
        (some (PrintMove.decidedCfg (verifyDelimited raw)
          (ordinaryOutput initial (verifyDelimited raw)).Tape)) bound,
      target.steps = PrintMove.simulationTime (ordinaryMachine initial)
        (TM0.init (ordinaryInput initial raw)) native.steps + 1 ∧
      target.steps ≤ 2 * native.steps + 1 ∧
      PrintMove.step (conventionalMachine initial)
        (PrintMove.decidedCfg (verifyDelimited raw)
          (ordinaryOutput initial (verifyDelimited raw)).Tape) = none

/-- Retain the existing witnesses and widen only the actual target's bound. -/
theorem run_power (initial : R) [DecidableEq (Alphabet initial)] (raw : Raw) :
    Run initial raw
      (raw.length ^ powerExponent (actionMaximum (R := R)) +
        powerExponent (actionMaximum (R := R))) := by
  obtain ⟨native, target, exactTime, bounded, stopped⟩ := conventional_run initial raw
  let widened : StateTransition.EvalsToInTime (PrintMove.step (conventionalMachine initial))
      (PrintMove.init (.normal .start) (ordinaryInput initial raw))
      (some (PrintMove.decidedCfg (verifyDelimited raw)
        (ordinaryOutput initial (verifyDelimited raw)).Tape))
      (raw.length ^ powerExponent (actionMaximum (R := R)) +
        powerExponent (actionMaximum (R := R))) :=
    { toEvalsTo := target.toEvalsTo
      steps_le_m := target.steps_le_m.trans (allowance_le_power (actionMaximum (R := R)) raw) }
  exact ⟨native, widened, exactTime, bounded, stopped⟩

/-- The existential exponent precedes every raw input and every run witness. -/
theorem exists_fixed_power (initial : R) [DecidableEq (Alphabet initial)] :
    ∃ k : Nat, ∀ raw : Raw, Run initial raw (raw.length ^ k + k) :=
  ⟨powerExponent (actionMaximum (R := R)), run_power initial⟩

/-- The actual empty-input run needs no positive-length premise. -/
theorem empty_run (initial : R) [DecidableEq (Alphabet initial)] :
    Run initial []
      (0 ^ powerExponent (actionMaximum (R := R)) +
        powerExponent (actionMaximum (R := R))) :=
  run_power initial []

/-- This actual-run specialization includes delimiter, present false and true. -/
theorem singleton_run (initial : R) [DecidableEq (Alphabet initial)] (letter : Option Bool) :
    Run initial [letter]
      (1 ^ powerExponent (actionMaximum (R := R)) +
        powerExponent (actionMaximum (R := R))) :=
  run_power initial [letter]

/-- Preserve the literal pair, its paid delimiter and its existing answer.
The Run field retains both complete machine witnesses; no input is normalized. -/
theorem literal_pair_run (initial : R) [DecidableEq (Alphabet initial)]
    (input cert : Resources.BinaryCounter.Bits) :
    Run initial (literalPair input cert)
      ((input.length + cert.length + 1) ^ powerExponent (actionMaximum (R := R)) +
        powerExponent (actionMaximum (R := R))) ∧
    (ordinaryInput initial (literalPair input cert)).length =
      input.length + cert.length + 1 ∧
    verifyDelimited (literalPair input cert) = (verifyBitsRun input cert).1 := by
  refine ⟨?_, literal_input_length initial input cert, verifyDelimited_pair input cert⟩
  simpa only [literalPair_length] using run_power initial (literalPair input cert)

end Resources.RotationCertificate.DelimiterMachine.PolynomialTime

end
