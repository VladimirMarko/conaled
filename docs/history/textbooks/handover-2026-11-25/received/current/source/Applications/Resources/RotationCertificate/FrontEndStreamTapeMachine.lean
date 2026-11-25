import Applications.Resources.TuringSimulation.MarkedInput
import Applications.Resources.TuringSimulation.PolynomialDecider
import Applications.Resources.TuringSimulation.VisitedSpace

import Applications.Resources.TuringSimulation.FiniteStackToTape
import Applications.Resources.TuringSimulation.TapeToPrimitive
import Applications.Resources.RotationCertificate.FrontEndStreamMachine

/-!
# Native and primitive tape time for the complete controller

Instantiate the quantitative stack-to-tape simulator with the actual source
controller run and its prefix stack occupancy. The fixed programme determines
the action maximum before choosing the raw input. The native TM1 bound is an
explicit expression of degree at most three in the original raw-word length.
The existing TM1-to-TM0 translator adds a factor at most three, and support
restriction supplies an actual finite primitive-control carrier at the same cost.

The encoded start uses trInit and retains the full relation to the literal
package halt, with the answer on fuel rather than framedRaw. The ordinary
interface below executes input conversion, reflection and singleton output;
actual native prefixes supply visited-space and physical tape containment.
Conventional NP remains a separate obligation. Live halt and the subsequent
outer-none step stay distinct.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.FrontEndStreamMachine

open Function
open Turing Turing.TM2to1
open Resources.BinaryCounter (Bits)
open Resources.TuringSimulation.StackToTape

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R)

/-- This number depends on the fixed complete source programme, including its
fixed caller, and is chosen before the raw input. -/
def tapeActionBound : ℕ := finiteActionBound (program caller)

omit [DecidableEq K] [Fintype K] [Fintype R] [∀ k, Fintype (Γ k)] in
theorem actionBound_le_tapeActionBound (l : Label Λ) :
    actionBound (program caller l) ≤ tapeActionBound caller :=
  actionBound_le_finiteActionBound (program caller) l

/-- Quantitative native TM1 simulation of the actual complete controller.
The source run and every source prefix come from the existing genuine-init
controller theorems. The target input is explicitly the trInit encoded tape. -/
theorem encoded_tape_run_bound (initial : R) (raw : Bits) :
    ∃ target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R),
      TrCfg (Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw]) target ∧
      Nonempty (StateTransition.EvalsToInTime (TM1.step (tr (program caller)))
        (encodedInitial (machine caller initial) raw) (some target)
        (runSteps raw *
          (1 + tapeActionBound caller * (2 * (max raw.length 1 + tapeActionBound caller) + 2)))) := by
  apply finite_run_bounded (program caller)
    (Turing.initList (machine caller initial) raw)
    (Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw])
    (encodedInitial (machine caller initial) raw)
    (encodedInitial_related (machine caller initial) raw)
    (runSteps raw) (tapeActionBound caller) (max raw.length 1)
    (init_iterate caller initial raw)
  intro i c hi hc
  have hcells : stackCells c ≤ max raw.length 1 :=
    (init_peak caller initial raw).1 i (Nat.le_of_lt hi) c hc
  refine ⟨?_, fun l _ => actionBound_le_tapeActionBound caller l⟩
  intro j
  have hsingle : (c.stk j).length ≤ stackCells c :=
    by
      change (c.stk j).length ≤ Finset.univ.sum (fun k => (c.stk k).length)
      exact Finset.single_le_sum (f := fun k => (c.stk k).length)
        (fun k _ => Nat.zero_le (c.stk k).length) (Finset.mem_univ j)
  exact le_trans hsingle hcells

/-- A concrete polynomial expression in the original raw-word length. For a
fixed programme A is constant and the polynomial has degree at most three. -/
def encodedTapeTimeBound (A N : ℕ) : ℕ :=
  (N * N + 10 * N + 36) * (1 + A * (2 * (N + 1 + A) + 2))

/-- The complete controller's actual encoded-input TM1 run is bounded by the
explicit polynomial expression. The endpoint is the related live halt with
the computed Boolean answer on fuel; no extra outer-none transition is charged. -/
theorem encoded_tape_run_polynomial (initial : R) (raw : Bits) :
    ∃ target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R),
      TrCfg (Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw]) target ∧
      Nonempty (StateTransition.EvalsToInTime (TM1.step (tr (program caller)))
        (encodedInitial (machine caller initial) raw) (some target)
        (encodedTapeTimeBound (tapeActionBound caller) raw.length)) := by
  obtain ⟨target, htarget, ⟨run⟩⟩ := encoded_tape_run_bound caller initial raw
  refine ⟨target, htarget, ⟨{ toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }⟩⟩
  apply le_trans run.steps_le_m
  have hmax : max raw.length 1 ≤ raw.length + 1 := by omega
  have hfactor :
      1 + tapeActionBound caller * (2 * (max raw.length 1 + tapeActionBound caller) + 2) ≤
        1 + tapeActionBound caller * (2 * (raw.length + 1 + tapeActionBound caller) + 2) :=
    Nat.add_le_add_left
      (Nat.mul_le_mul_left (tapeActionBound caller)
        (Nat.add_le_add_right
          (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hmax (tapeActionBound caller))) 2)) 1
  exact Nat.mul_le_mul (runSteps_le raw) hfactor

/-- Primitive time to the related live endpoint, using the source's actual
runSteps and prefix stack bound. The programme constant is fixed before raw. -/
theorem encoded_primitive_run_bound (initial : R) (raw : Bits) :
    let tm := machine caller initial
    let : Inhabited (Package.AmbientControl tm) := Package.ambientInhabited tm
    ∃ target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R),
      TrCfg (Turing.haltList tm [BitPairFraming.verifyFramed raw]) target ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (Package.ambientMachine tm))
        (Package.initial tm raw)
        (some (TM1to0.trCfg (tr (program caller)) target))
        (3 * (runSteps raw *
          (1 + tapeActionBound caller * (2 * (max raw.length 1 + tapeActionBound caller) + 2))))) := by
  dsimp only
  let : Inhabited (Label Λ) := ⟨(machine caller initial).main⟩
  let : Inhabited (Registers R) := ⟨(machine caller initial).initialState⟩
  obtain ⟨target, related, ⟨run⟩⟩ := encoded_tape_run_bound caller initial raw
  refine ⟨target, related, ?_⟩
  exact Resources.TuringSimulation.TapeToPrimitive.stack_run_bounded
    (program caller) (encodedInitial (machine caller initial) raw) target
    (runSteps raw *
      (1 + tapeActionBound caller * (2 * (max raw.length 1 + tapeActionBound caller) + 2))) run

/-- Explicit primitive bound for the fixed programme on the original raw-word
length. It reaches live halt; the next outer-none transition is separate. -/
def encodedPrimitiveTimeBound (A N : ℕ) : ℕ :=
  3 * encodedTapeTimeBound A N

theorem encoded_primitive_run_polynomial (initial : R) (raw : Bits) :
    let tm := machine caller initial
    let : Inhabited (Package.AmbientControl tm) := Package.ambientInhabited tm
    ∃ target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R),
      TrCfg (Turing.haltList tm [BitPairFraming.verifyFramed raw]) target ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (Package.ambientMachine tm))
        (Package.initial tm raw)
        (some (TM1to0.trCfg (tr (program caller)) target))
        (encodedPrimitiveTimeBound (tapeActionBound caller) raw.length)) := by
  dsimp only
  let : Inhabited (Label Λ) := ⟨(machine caller initial).main⟩
  let : Inhabited (Registers R) := ⟨(machine caller initial).initialState⟩
  obtain ⟨target, related, ⟨run⟩⟩ := encoded_tape_run_polynomial caller initial raw
  refine ⟨target, related, ?_⟩
  exact Resources.TuringSimulation.TapeToPrimitive.stack_run_bounded
    (program caller) (encodedInitial (machine caller initial) raw) target
    (encodedTapeTimeBound (tapeActionBound caller) raw.length) run

/-- The primitive outer-none observation pays the one additional transition
from the actual related live halt. Its output remains documented by the live
endpoint theorem; outer none itself does not carry that output. -/
theorem encoded_primitive_outer_none (initial : R) (raw : Bits) :
    let tm := machine caller initial
    let : Inhabited (Package.AmbientControl tm) := Package.ambientInhabited tm
    Nonempty (StateTransition.EvalsToInTime (TM0.step (Package.ambientMachine tm))
      (Package.initial tm raw) none
      (encodedPrimitiveTimeBound (tapeActionBound caller) raw.length + 1)) := by
  dsimp only
  let tm := machine caller initial
  let : Inhabited (Package.AmbientControl tm) := Package.ambientInhabited tm
  obtain ⟨target, related, ⟨before⟩⟩ := encoded_primitive_run_polynomial caller initial raw
  have stopped : TM0.step (Package.ambientMachine tm)
      (TM1to0.trCfg (tr (program caller)) target) = none := by
    cases related
    rfl
  let after : StateTransition.EvalsTo (TM0.step (Package.ambientMachine tm))
      (TM1to0.trCfg (tr (program caller)) target) none :=
    { steps := 1
      evals_in_steps := by
        change TM0.step (Package.ambientMachine tm)
          (TM1to0.trCfg (tr (program caller)) target) = none
        exact stopped }
  let run := StateTransition.EvalsTo.trans (TM0.step (Package.ambientMachine tm))
    (Package.initial tm raw) (TM1to0.trCfg (tr (program caller)) target) none
    before.toEvalsTo after
  refine ⟨{ toEvalsTo := run, steps_le_m := ?_ }⟩
  change 1 + before.steps ≤ encodedPrimitiveTimeBound (tapeActionBound caller) raw.length + 1
  calc
    _ ≤ 1 + encodedPrimitiveTimeBound (tapeActionBound caller) raw.length :=
      Nat.add_le_add_left before.steps_le_m 1
    _ = encodedPrimitiveTimeBound (tapeActionBound caller) raw.length + 1 := Nat.add_comm _ _

/-- The complete controller supplies finite alphabets at every physical stack;
this is deliberately separate from FinTM2's designated-input alphabet field. -/
@[instance_reducible] def finitePrimitiveAlphabetFintype (initial : R) :
    Fintype (Package.Alphabet (machine caller initial)) := by
  let : ∀ k, Fintype ((machine caller initial).Γ k) := machineAlphabetFintype caller initial
  exact Package.alphabetFintype (machine caller initial)

/-- The fixed target control is the actual finite support subtype, independent
of input and without a global finiteness assertion for ambient continuations. -/
@[instance_reducible] noncomputable def finitePrimitiveControlFintype (initial : R) :
    Fintype (Package.Control (machine caller initial)) :=
  Package.controlFintype (machine caller initial)

/-- The support-closed finite primitive machine consumes the actual source
run bound, with unchanged primitive count, whole tape and optional endpoint. -/
theorem finite_encoded_primitive_run_bound (initial : R) (raw : Bits) :
    let tm := machine caller initial
    let : Inhabited (Package.Control tm) := Package.controlInhabited tm
    ∃ target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R),
      TrCfg (Turing.haltList tm [BitPairFraming.verifyFramed raw]) target ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (Package.closedMachine tm))
        (TM0.init (trInit tm.k₀ raw))
        (some (Package.mapCfg tm (TM1to0.trCfg (tr (program caller)) target)))
        (3 * (runSteps raw *
          (1 + tapeActionBound caller * (2 * (max raw.length 1 + tapeActionBound caller) + 2))))) := by
  dsimp only
  let tm := machine caller initial
  let : Inhabited (Package.AmbientControl tm) := Package.ambientInhabited tm
  let : Inhabited (Package.Control tm) := Package.controlInhabited tm
  obtain ⟨target, related, ⟨run⟩⟩ := encoded_primitive_run_bound caller initial raw
  exact ⟨target, related, ⟨Package.closedInitialRun tm raw
    (some (TM1to0.trCfg (tr (program caller)) target))
    (3 * (runSteps raw *
      (1 + tapeActionBound caller * (2 * (max raw.length 1 + tapeActionBound caller) + 2)))) run⟩⟩

/-- An actual finite-state, finite-alphabet primitive machine, with its supplied
native default, runs on trInit-encoded input within the explicit polynomial
bound. The complete output tape is retained on its separate fuel track. -/
theorem finite_encoded_primitive_run_polynomial (initial : R) (raw : Bits) :
    let tm := machine caller initial
    let : Inhabited (Package.Control tm) := Package.controlInhabited tm
    ∃ target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R),
      TrCfg (Turing.haltList tm [BitPairFraming.verifyFramed raw]) target ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (Package.closedMachine tm))
        (TM0.init (trInit tm.k₀ raw))
        (some (Package.mapCfg tm (TM1to0.trCfg (tr (program caller)) target)))
        (encodedPrimitiveTimeBound (tapeActionBound caller) raw.length)) := by
  dsimp only
  let tm := machine caller initial
  let : Inhabited (Package.AmbientControl tm) := Package.ambientInhabited tm
  let : Inhabited (Package.Control tm) := Package.controlInhabited tm
  obtain ⟨target, related, ⟨run⟩⟩ := encoded_primitive_run_polynomial caller initial raw
  exact ⟨target, related, ⟨Package.closedInitialRun tm raw
    (some (TM1to0.trCfg (tr (program caller)) target))
    (encodedPrimitiveTimeBound (tapeActionBound caller) raw.length) run⟩⟩

/-- The finite restriction preserves the separately paid terminal transition
and returns outer none with the same bound plus one. -/
theorem finite_encoded_primitive_outer_none (initial : R) (raw : Bits) :
    let tm := machine caller initial
    let : Inhabited (Package.Control tm) := Package.controlInhabited tm
    Nonempty (StateTransition.EvalsToInTime (TM0.step (Package.closedMachine tm))
      (TM0.init (trInit tm.k₀ raw)) none
      (encodedPrimitiveTimeBound (tapeActionBound caller) raw.length + 1)) := by
  dsimp only
  let tm := machine caller initial
  let : Inhabited (Package.AmbientControl tm) := Package.ambientInhabited tm
  let : Inhabited (Package.Control tm) := Package.controlInhabited tm
  obtain ⟨run⟩ := encoded_primitive_outer_none caller initial raw
  exact ⟨Package.closedInitialRun tm raw none
    (encodedPrimitiveTimeBound (tapeActionBound caller) raw.length + 1) run⟩

end Resources.RotationCertificate.FrontEndStreamMachine

namespace Resources.RotationCertificate.FrontEndStreamMachine

open Turing Turing.TM2to1
open Resources.BinaryCounter (Bits)
open Resources.TuringSimulation.StackToTape

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R)

/-- the full relation to the literal singleton-answer package
halt exposes the actual control, registers, marker and two distinct tracks.
The fuel word has one element, so its bottom observation is that answer. -/
theorem related_controller_halt_observation (initial : R) (answer : Bool)
    (target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
      (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R))
    (related : TrCfg (Turing.haltList (machine caller initial) [answer]) target) :
    target.l = none ∧ target.var = initialRegisters initial ∧
      target.Tape.head.1 = true ∧
      target.Tape.head.2 (machine caller initial).k₀ = none ∧
      target.Tape.head.2 (machine caller initial).k₁ = some answer := by
  obtain ⟨control, registers, marker, tracks⟩ :=
    related_marker_observation
      (Turing.haltList (machine caller initial) [answer]) target related
  refine ⟨control, registers, marker, ?_, ?_⟩
  · have observed := tracks (.inl .framedRaw)
    exact observed.trans (congrArg (fun xs : Bits => xs.reverse[0]?)
      (machine_haltList_framedRaw caller initial [answer]))
  · have observed := tracks (.inl .fuel)
    exact observed.trans (congrArg (fun xs : Bits => xs.reverse[0]?)
      (machine_haltList_fuel caller initial [answer]))

/-- the actual finite primitive endpoint has the same marked
tape and therefore the same absent raw track and singleton fuel answer.
This observes the mapped live configuration, not merely the source halt. -/
theorem related_finite_primitive_halt_head (initial : R) (answer : Bool)
    (target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
      (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R))
    (related : TrCfg (Turing.haltList (machine caller initial) [answer]) target) :
    let tm := machine caller initial
    let finish := Package.mapCfg tm (TM1to0.trCfg (tr (program caller)) target)
    finish.Tape.head.1 = true ∧
      finish.Tape.head.2 tm.k₀ = none ∧
      finish.Tape.head.2 tm.k₁ = some answer := by
  obtain ⟨_, _, marker, rawHead, fuelHead⟩ :=
    related_controller_halt_observation caller initial answer target related
  rcases target with ⟨label, regs, T⟩
  let tm := machine caller initial
  let c : TM0.Cfg (Package.Alphabet tm) (Package.AmbientControl tm) :=
    TM1to0.trCfg (tr (program caller)) ⟨label, regs, T⟩
  have tape : (Package.mapCfg tm c).Tape = T := Package.mapCfg_tape tm c
  change (Package.mapCfg tm c).Tape.head.1 = true ∧
    (Package.mapCfg tm c).Tape.head.2 tm.k₀ = none ∧
    (Package.mapCfg tm c).Tape.head.2 tm.k₁ = some answer
  exact ⟨(congrArg (fun tape => tape.head.1) tape).trans marker,
    (congrArg (fun tape => tape.head.2 tm.k₀) tape).trans rawHead,
    (congrArg (fun tape => tape.head.2 tm.k₁) tape).trans fuelHead⟩

/-- consume the existing actual finite primitive run and observe
its same live endpoint. Its original polynomial upper bound is retained
verbatim; no new source or target duration is postulated. -/
theorem finite_encoded_primitive_run_observed (initial : R) (raw : Bits) :
    let tm := machine caller initial
    let : Inhabited (Package.Control tm) := Package.controlInhabited tm
    ∃ target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R),
      TrCfg (Turing.haltList tm [BitPairFraming.verifyFramed raw]) target ∧
      let finish := Package.mapCfg tm (TM1to0.trCfg (tr (program caller)) target)
      finish.Tape.head.1 = true ∧
        finish.Tape.head.2 tm.k₀ = none ∧
        finish.Tape.head.2 tm.k₁ = some (BitPairFraming.verifyFramed raw) ∧
        Nonempty (StateTransition.EvalsToInTime (TM0.step (Package.closedMachine tm))
          (TM0.init (trInit tm.k₀ raw)) (some finish)
          (encodedPrimitiveTimeBound (tapeActionBound caller) raw.length)) := by
  dsimp only
  let tm := machine caller initial
  let : Inhabited (Package.Control tm) := Package.controlInhabited tm
  obtain ⟨target, related, run⟩ := finite_encoded_primitive_run_polynomial caller initial raw
  obtain ⟨marker, rawHead, fuelHead⟩ :=
    related_finite_primitive_halt_head caller initial (BitPairFraming.verifyFramed raw)
      target related
  exact ⟨target, related, marker, rawHead, fuelHead, run⟩

end Resources.RotationCertificate.FrontEndStreamMachine

namespace Resources.RotationCertificate.FrontEndStreamMachine

open Turing Turing.TM2to1
open Resources.BinaryCounter (Bits)
open Resources.TuringSimulation.StackToTape

/-- The explicit native bound is monotone in the original raw-word length,
including the zero-action programme constant. -/
theorem encodedTapeTimeBound_mono (A : Nat) : Monotone (encodedTapeTimeBound A) := by
  intro m n h
  unfold encodedTapeTimeBound
  apply Nat.mul_le_mul
  · exact Nat.add_le_add_right
      (Nat.add_le_add (Nat.mul_le_mul h h) (Nat.mul_le_mul_left 10 h)) 36
  · exact Nat.add_le_add_left
      (Nat.mul_le_mul_left A
        (Nat.add_le_add_right
          (Nat.mul_le_mul_left 2
            (Nat.add_le_add_right (Nat.add_le_add_right h 1) A)) 2)) 1

/-- The primitive simulator's fixed factor preserves monotonicity. -/
theorem encodedPrimitiveTimeBound_mono (A : Nat) :
    Monotone (encodedPrimitiveTimeBound A) := by
  intro m n h
  exact Nat.mul_le_mul_left 3 (encodedTapeTimeBound_mono A h)

/-- A polynomial object for the existing explicit primitive bound. This
packages arithmetic only; execution is supplied by the actual run theorem. -/
noncomputable def encodedPrimitiveTimePolynomial (A : Nat) : Polynomial Nat :=
  3 * ((Polynomial.X ^ 2 + 10 * Polynomial.X + 36) *
    (1 + Polynomial.C A * (2 * (Polynomial.X + 1 + Polynomial.C A) + 2)))

@[simp] theorem encodedPrimitiveTimePolynomial_eval (A N : Nat) :
    (encodedPrimitiveTimePolynomial A).eval N = encodedPrimitiveTimeBound A N := by
  simp [encodedPrimitiveTimePolynomial, encodedPrimitiveTimeBound,
    encodedTapeTimeBound, pow_two]

/-- Composing with the proved quadratic frame bound gives an instance-size
polynomial. Its degree is at most six; no exact degree is asserted at A=0. -/
noncomputable def encodedPrimitiveWitnessPolynomial (A : Nat) : Polynomial Nat :=
  (encodedPrimitiveTimePolynomial A).comp ((Polynomial.X + 1) ^ 2)

@[simp] theorem encodedPrimitiveWitnessPolynomial_eval (A m : Nat) :
    (encodedPrimitiveWitnessPolynomial A).eval m =
      encodedPrimitiveTimeBound A ((m + 1) ^ 2) := by
  simp [encodedPrimitiveWitnessPolynomial]

/-- No witness-size assumption is needed to bound the frame by a linear
function of the combined instance and certificate lengths. -/
theorem frame_length_le_combined (input cert : Bits) :
    (BitPairFraming.frame input cert).length ≤ 2 * (input.length + cert.length + 1) := by
  rw [BitPairFraming.frame_length]
  omega

/-- The already constructed verifier bound is polynomial in the combined
pair size for all pairs, including malformed instance/certificate encodings. -/
theorem encodedPrimitiveTimeBound_frame_le (A : Nat) (input cert : Bits) :
    encodedPrimitiveTimeBound A (BitPairFraming.frame input cert).length ≤
      encodedPrimitiveTimeBound A (2 * (input.length + cert.length + 1)) :=
  encodedPrimitiveTimeBound_mono A (frame_length_le_combined input cert)

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R)

/-- Choose the existing small certificate, consume the actual fixed finite
machine's run on its complete frame, and enlarge only its upper bound.
The endpoint is fully related to the literal true source halt; the start
remains explicitly encoded, so this is not yet the ordinary-I/O result. -/
theorem binaryYes_small_finite_primitive_run (initial : R) (input : Bits)
    (yes : BinaryYes input) :
    let tm := machine caller initial
    let : Inhabited (Package.Control tm) := Package.controlInhabited tm
    ∃ (cert : Bits)
      (target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R)),
      cert.length ≤ input.length ^ 2 ∧
      (BitPairFraming.frame input cert).length ≤ (input.length + 1) ^ 2 ∧
      TrCfg (Turing.haltList tm [true]) target ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (Package.closedMachine tm))
        (TM0.init (trInit tm.k₀ (BitPairFraming.frame input cert)))
        (some (Package.mapCfg tm (TM1to0.trCfg (tr (program caller)) target)))
        (encodedPrimitiveTimeBound (tapeActionBound caller) ((input.length + 1) ^ 2))) := by
  dsimp only
  let tm := machine caller initial
  let : Inhabited (Package.Control tm) := Package.controlInhabited tm
  obtain ⟨cert, small, frameSmall, accepted⟩ :=
    BitPairFraming.verifyFramed_complete_small input yes
  obtain ⟨target, related, ⟨run⟩⟩ :=
    finite_encoded_primitive_run_polynomial caller initial (BitPairFraming.frame input cert)
  refine ⟨cert, target, small, frameSmall, ?_,
    ⟨{ toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }⟩⟩
  · simpa only [accepted] using related
  · exact run.steps_le_m.trans
      (encodedPrimitiveTimeBound_mono (tapeActionBound caller) frameSmall)

end Resources.RotationCertificate.FrontEndStreamMachine

namespace Resources.RotationCertificate.FrontEndStreamMachine

open Turing Turing.TM2to1
open Resources.BinaryCounter (Bits)
open Resources.TuringSimulation
open Resources.TuringSimulation.StackToTape

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R)

/-- A fixed native output-letter function. The actual halt invariant proves
that the fuel observation is some answer; the default branch is unreachable
at the composed output step. -/
def ordinaryEmitter (initial : R) (a : Package.Alphabet (machine caller initial)) :
    Package.Alphabet (machine caller initial) :=
  MarkedInput.symbol (machine caller initial).k₀
    ((a.2 (machine caller initial).k₁).getD false)

theorem ordinaryEmitter_halt_row (initial : R) (answer : Bool) :
    ordinaryEmitter caller initial
        (true, SingletonOutput.haltRow (machine caller initial) answer) =
      MarkedInput.symbol (machine caller initial).k₀ answer := by
  let tm := machine caller initial
  have fuel : SingletonOutput.haltRow tm answer tm.k₁ = (some answer : Option Bool) := by
    change Function.update (fun k : tm.K => (none : Option (tm.Γ k)))
      tm.k₁ (some answer) tm.k₁ = some answer
    exact Function.update_self tm.k₁ (some answer)
      (fun k : tm.K => (none : Option (tm.Γ k)))
  exact congrArg
    (fun result : Option Bool =>
      MarkedInput.symbol (Γ := tm.Γ) tm.k₀ (result.getD false)) fuel

/-- One fixed finite native primitive machine, chosen before any raw word.
Its supplied default is the prelude start; the prelude enters exactly the
source package's supplied primitive main/register default. -/
def ordinaryMachine (initial : R) :
    TM0.Machine (Package.Alphabet (machine caller initial))
      (MarkedInput.Control (Package.Control (machine caller initial))) := by
  let tm := machine caller initial
  letI : Inhabited (Package.Control tm) := Package.controlInhabited tm
  exact MarkedInput.machine tm.k₀ (Package.closedMachine tm) (ordinaryEmitter caller initial)

@[instance_reducible] noncomputable def ordinaryControlFintype (initial : R) :
    Fintype (MarkedInput.Control (Package.Control (machine caller initial))) := by
  letI : Fintype (Package.Control (machine caller initial)) :=
    finitePrimitiveControlFintype caller initial
  infer_instance

/-- The actual controller, on ordinary per-letter Boolean input, reaches the
ordinary singleton Boolean output and returns it under native TM0.eval.
The source primitive count is only bounded; the added prelude/output counts
are literal. All malformed raw words remain included. -/
theorem ordinary_run_and_eval (initial : R) (raw : Bits) :
    let tm := machine caller initial
    let output := MarkedInput.symbol tm.k₀ (BitPairFraming.verifyFramed raw)
    Nonempty (StateTransition.EvalsToInTime (TM0.step (ordinaryMachine caller initial))
      (TM0.init (MarkedInput.input tm.k₀ raw))
      (some ⟨.done, Tape.mk₁ [output]⟩)
      (MarkedInput.preludeSteps raw +
        encodedPrimitiveTimeBound (tapeActionBound caller) raw.length + 1)) ∧
      TM0.eval (ordinaryMachine caller initial) (MarkedInput.input tm.k₀ raw) =
        Part.some (ListBlank.mk [output]) := by
  dsimp only
  let tm := machine caller initial
  let : Inhabited (Package.Control tm) := Package.controlInhabited tm
  obtain ⟨target, related, ⟨before⟩⟩ :=
    finite_encoded_primitive_run_polynomial caller initial raw
  let answer := BitPairFraming.verifyFramed raw
  let marked : Package.Alphabet tm := (true, SingletonOutput.haltRow tm answer)
  let nativeTarget : TM1.Cfg (Γ' tm.K tm.Γ)
      (Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ := target
  have nativeRelated : TrCfg (Turing.haltList tm [answer]) nativeTarget := related
  let ambient : TM0.Cfg (Package.Alphabet tm) (Package.AmbientControl tm) :=
    TM1to0.trCfg (tr tm.m) nativeTarget
  let finish : TM0.Cfg (Package.Alphabet tm) (Package.Control tm) :=
    Package.mapCfg tm ambient
  have ambient_tape : ambient.Tape = nativeTarget.Tape := rfl
  have complete : finish.Tape = Tape.mk₁ [marked] :=
    (Package.mapCfg_tape tm ambient).trans
      (ambient_tape.trans
        (SingletonOutput.haltList_singleton_tape tm answer nativeTarget nativeRelated))
  have stopped : Package.closedMachine tm finish.q marked = none :=
    SingletonOutput.related_package_halt_stopped tm [answer] nativeTarget nativeRelated marked
  have finish_eq :
      finish =
        (⟨finish.q, Tape.mk₁ [marked]⟩ : TM0.Cfg (Package.Alphabet tm) (Package.Control tm)) :=
    congrArg
      (fun T : Tape (Package.Alphabet tm) =>
        (⟨finish.q, T⟩ : TM0.Cfg (Package.Alphabet tm) (Package.Control tm))) complete
  have before_pkg : StateTransition.EvalsToInTime (TM0.step (Package.closedMachine tm))
      (TM0.init (trInit (Γ := tm.Γ) tm.k₀ raw)) (some finish)
      (encodedPrimitiveTimeBound (tapeActionBound caller) raw.length) := before
  have before' : StateTransition.EvalsToInTime (TM0.step (Package.closedMachine tm))
      (TM0.init (trInit (Γ := tm.Γ) tm.k₀ raw)) (some ⟨finish.q, Tape.mk₁ [marked]⟩)
      (encodedPrimitiveTimeBound (tapeActionBound caller) raw.length) :=
    { steps := before_pkg.steps
      evals_in_steps := before_pkg.evals_in_steps.trans (congrArg some finish_eq)
      steps_le_m := before_pkg.steps_le_m }
  have live := MarkedInput.normalizedRunInTime (Γ := tm.Γ) tm.k₀ (Package.closedMachine tm)
    (ordinaryEmitter caller initial) raw finish.q marked
    (encodedPrimitiveTimeBound (tapeActionBound caller) raw.length) before' stopped
  have evaluated := MarkedInput.normalized_eval (Γ := tm.Γ) tm.k₀ (Package.closedMachine tm)
    (ordinaryEmitter caller initial) raw finish.q marked before'.toEvalsTo stopped
  have emitted : ordinaryEmitter caller initial marked =
      MarkedInput.symbol (Γ := tm.Γ) tm.k₀ answer :=
    ordinaryEmitter_halt_row caller initial answer
  have emitted_endpoint :
      (some ⟨MarkedInput.Control.done, Tape.mk₁ [ordinaryEmitter caller initial marked]⟩ :
        Option (TM0.Cfg (Package.Alphabet tm) (MarkedInput.Control (Package.Control tm)))) =
      some ⟨MarkedInput.Control.done,
        Tape.mk₁ [MarkedInput.symbol (Γ := tm.Γ) tm.k₀ answer]⟩ :=
    congrArg
      (fun output : Package.Alphabet tm =>
        (some ⟨MarkedInput.Control.done, Tape.mk₁ [output]⟩ :
          Option (TM0.Cfg (Package.Alphabet tm) (MarkedInput.Control (Package.Control tm)))))
      emitted
  constructor
  · exact ⟨{
      steps := live.steps
      evals_in_steps := live.evals_in_steps.trans emitted_endpoint
      steps_le_m := live.steps_le_m }⟩
  · exact evaluated.trans
      (congrArg (fun output : Package.Alphabet tm => Part.some (ListBlank.mk [output])) emitted)

end Resources.RotationCertificate.FrontEndStreamMachine

namespace Resources.RotationCertificate.FrontEndStreamMachine

open Resources.BinaryCounter (Bits)
open Resources.TuringSimulation

def ordinaryTimeBound (A N : Nat) : Nat :=
  N + 3 + encodedPrimitiveTimeBound A N

theorem ordinaryTimeBound_mono (A : Nat) : Monotone (ordinaryTimeBound A) := by
  intro m n h
  exact Nat.add_le_add (Nat.add_le_add_right h 3)
    (encodedPrimitiveTimeBound_mono A h)

theorem preludeSteps_le_length_add_two {α : Type*} (raw : List α) :
    MarkedInput.preludeSteps raw ≤ raw.length + 2 := by
  cases raw with
  | nil => exact Nat.le_succ 1
  | cons a raw => exact Nat.le_refl _

theorem ordinary_overhead_le (A : Nat) (raw : Bits) :
    MarkedInput.preludeSteps raw + encodedPrimitiveTimeBound A raw.length + 1 ≤
      ordinaryTimeBound A raw.length := by
  calc
    _ ≤ (raw.length + 2) + encodedPrimitiveTimeBound A raw.length + 1 :=
      Nat.add_le_add_right
        (Nat.add_le_add_right (preludeSteps_le_length_add_two raw)
          (encodedPrimitiveTimeBound A raw.length)) 1
    _ = ordinaryTimeBound A raw.length :=
      Nat.add_right_comm (raw.length + 2) (encodedPrimitiveTimeBound A raw.length) 1

/-- Arithmetic packaging of the actual live-run bound. Execution is supplied
by the concrete ordinary native machine, not by this polynomial object. -/
noncomputable def ordinaryTimePolynomial (A : Nat) : Polynomial Nat :=
  Polynomial.X + 3 + encodedPrimitiveTimePolynomial A

@[simp] theorem ordinaryTimePolynomial_eval (A N : Nat) :
    (ordinaryTimePolynomial A).eval N = ordinaryTimeBound A N := by
  simp [ordinaryTimePolynomial, ordinaryTimeBound]

/-- An all-pair bound in the combined instance and certificate length. -/
noncomputable def ordinaryPairTimePolynomial (A : Nat) : Polynomial Nat :=
  (ordinaryTimePolynomial A).comp (2 * (Polynomial.X + 1))

@[simp] theorem ordinaryPairTimePolynomial_eval (A N : Nat) :
    (ordinaryPairTimePolynomial A).eval N = ordinaryTimeBound A (2 * (N + 1)) := by
  simp [ordinaryPairTimePolynomial]

/-- The distinct small-witness composition in the original instance length. -/
noncomputable def ordinaryWitnessTimePolynomial (A : Nat) : Polynomial Nat :=
  (ordinaryTimePolynomial A).comp ((Polynomial.X + 1) ^ 2)

@[simp] theorem ordinaryWitnessTimePolynomial_eval (A N : Nat) :
    (ordinaryWitnessTimePolynomial A).eval N = ordinaryTimeBound A ((N + 1) ^ 2) := by
  simp [ordinaryWitnessTimePolynomial]

theorem ordinaryTimeBound_frame_le (A : Nat) (input cert : Bits) :
    ordinaryTimeBound A (BitPairFraming.frame input cert).length ≤
      (ordinaryPairTimePolynomial A).eval (input.length + cert.length) := by
  rw [ordinaryPairTimePolynomial_eval]
  exact ordinaryTimeBound_mono A (frame_length_le_combined input cert)

theorem ordinaryTimeBound_small_frame_le (A : Nat) (input cert : Bits)
    (small : cert.length ≤ input.length ^ 2) :
    ordinaryTimeBound A (BitPairFraming.frame input cert).length ≤
      (ordinaryWitnessTimePolynomial A).eval input.length := by
  rw [ordinaryWitnessTimePolynomial_eval]
  exact ordinaryTimeBound_mono A (BitPairFraming.frame_length_le_square input cert small)

end Resources.RotationCertificate.FrontEndStreamMachine

namespace Resources.RotationCertificate.FrontEndStreamMachine

open Turing
open Resources.BinaryCounter (Bits)
open Resources.TuringSimulation
open Resources.TuringSimulation.StackToTape

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R)

/-- Only the upper-bound proof changes; the actual native witness is retained. -/
def ordinaryWidenRun (initial : R) (raw : Bits)
    (finish : TM0.Cfg (Package.Alphabet (machine caller initial))
      (MarkedInput.Control (Package.Control (machine caller initial))))
    (run : StateTransition.EvalsToInTime (TM0.step (ordinaryMachine caller initial))
      (TM0.init (MarkedInput.input (machine caller initial).k₀ raw)) (some finish)
      (MarkedInput.preludeSteps raw +
        encodedPrimitiveTimeBound (tapeActionBound caller) raw.length + 1)) :
    StateTransition.EvalsToInTime (TM0.step (ordinaryMachine caller initial))
      (TM0.init (MarkedInput.input (machine caller initial).k₀ raw)) (some finish)
      (ordinaryTimeBound (tapeActionBound caller) raw.length) where
  toEvalsTo := run.toEvalsTo
  steps_le_m := run.steps_le_m.trans (ordinary_overhead_le (tapeActionBound caller) raw)

theorem ordinaryWidenRun_toEvalsTo (initial : R) (raw : Bits)
    (finish : TM0.Cfg (Package.Alphabet (machine caller initial))
      (MarkedInput.Control (Package.Control (machine caller initial))))
    (run : StateTransition.EvalsToInTime (TM0.step (ordinaryMachine caller initial))
      (TM0.init (MarkedInput.input (machine caller initial).k₀ raw)) (some finish)
      (MarkedInput.preludeSteps raw +
        encodedPrimitiveTimeBound (tapeActionBound caller) raw.length + 1)) :
    (ordinaryWidenRun caller initial raw finish run).toEvalsTo = run.toEvalsTo := rfl

theorem ordinaryWidenRun_steps (initial : R) (raw : Bits)
    (finish : TM0.Cfg (Package.Alphabet (machine caller initial))
      (MarkedInput.Control (Package.Control (machine caller initial))))
    (run : StateTransition.EvalsToInTime (TM0.step (ordinaryMachine caller initial))
      (TM0.init (MarkedInput.input (machine caller initial).k₀ raw)) (some finish)
      (MarkedInput.preludeSteps raw +
        encodedPrimitiveTimeBound (tapeActionBound caller) raw.length + 1)) :
    (ordinaryWidenRun caller initial raw finish run).steps = run.steps := rfl

theorem ordinary_done_step (initial : R)
    (T : Tape (Package.Alphabet (machine caller initial))) :
    TM0.step (ordinaryMachine caller initial) ⟨.done, T⟩ = none := rfl

/-- Every raw word reaches the actual stopped ordinary singleton tape within
the uniform polynomial. The native eval result is retained alongside it. -/
theorem ordinary_run_uniform (initial : R) (raw : Bits) :
    let tm := machine caller initial
    let output := MarkedInput.symbol tm.k₀ (BitPairFraming.verifyFramed raw)
    Nonempty (StateTransition.EvalsToInTime (TM0.step (ordinaryMachine caller initial))
      (TM0.init (MarkedInput.input tm.k₀ raw))
      (some ⟨.done, Tape.mk₁ [output]⟩)
      (ordinaryTimeBound (tapeActionBound caller) raw.length)) ∧
      TM0.step (ordinaryMachine caller initial) ⟨.done, Tape.mk₁ [output]⟩ = none ∧
      TM0.eval (ordinaryMachine caller initial) (MarkedInput.input tm.k₀ raw) =
        Part.some (ListBlank.mk [output]) := by
  dsimp only
  obtain ⟨⟨run⟩, evaluated⟩ := ordinary_run_and_eval caller initial raw
  exact ⟨⟨ordinaryWidenRun caller initial raw _ run⟩,
    ordinary_done_step caller initial _, evaluated⟩

/-- The packaged source default retains the supplied user register, including
a supplied true value when the ambient Boolean default would be false. -/
theorem ordinary_source_default_user (initial : R) :
    user ((Package.controlInhabited (machine caller initial)).default.val.2) = initial := rfl

/-- One fixed finite machine deciding the existing raw framed-verifier
function. The run field consumes the actual native execution theorem. -/
noncomputable def ordinaryPolynomialDecider
    (caller : Λ → Statement Γ Λ R) (initial : R) :
    PolynomialBooleanDecider BitPairFraming.verifyFramed where
  Alphabet := Package.Alphabet (machine caller initial)
  Control := MarkedInput.Control (Package.Control (machine caller initial))
  alphabetFintype := finitePrimitiveAlphabetFintype caller initial
  controlFintype := ordinaryControlFintype caller initial
  blank := (false, fun _ => none)
  start := .start
  bit := ⟨MarkedInput.symbol (Γ := (machine caller initial).Γ) (machine caller initial).k₀,
    MarkedInput.symbol_injective (Γ := (machine caller initial).Γ)
      (machine caller initial).k₀⟩
  bit_ne_blank := by
    intro b
    exact MarkedInput.symbol_ne_blank (Γ := (machine caller initial).Γ)
      (machine caller initial).k₀ b
  machine := ordinaryMachine caller initial
  time := ordinaryTimePolynomial (tapeActionBound caller)
  run := by
    intro raw
    obtain ⟨⟨run⟩, stopped, _⟩ := ordinary_run_uniform caller initial raw
    refine ⟨⟨.done, Tape.mk₁
      [MarkedInput.symbol (Γ := (machine caller initial).Γ)
        (machine caller initial).k₀ (BitPairFraming.verifyFramed raw)]⟩,
      ⟨{ toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }⟩, stopped, rfl⟩
    simpa only [ordinaryTimePolynomial_eval] using run.steps_le_m

theorem ordinaryPolynomialDecider_time (initial : R) :
    (ordinaryPolynomialDecider caller initial).time =
      ordinaryTimePolynomial (tapeActionBound caller) := rfl

theorem ordinaryPolynomialDecider_bit (initial : R) (b : Bool) :
    (ordinaryPolynomialDecider caller initial).bit b =
      MarkedInput.symbol (Γ := (machine caller initial).Γ) (machine caller initial).k₀ b := rfl

theorem ordinaryPolynomialDecider_start (initial : R) :
    (ordinaryPolynomialDecider caller initial).start =
      (MarkedInput.Control.start : MarkedInput.Control (Package.Control (machine caller initial))) := rfl

end Resources.RotationCertificate.FrontEndStreamMachine

namespace Resources.RotationCertificate.FrontEndStreamMachine

open Turing
open Resources.BinaryCounter (Bits)
open Resources.TuringSimulation
open Resources.TuringSimulation.StackToTape

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R)

/-- Arbitrary instance/certificate pairs, without validity or length
assumptions, run on one fixed finite native machine in the combined-size
polynomial. The complete ordinary singleton and native eval are retained. -/
theorem ordinary_pair_run_and_eval (initial : R) (input cert : Bits) :
    let tm := machine caller initial
    let raw := BitPairFraming.frame input cert
    let output := MarkedInput.symbol tm.k₀ (verifyBitsRun input cert).1
    Nonempty (StateTransition.EvalsToInTime (TM0.step (ordinaryMachine caller initial))
      (TM0.init (MarkedInput.input tm.k₀ raw))
      (some ⟨.done, Tape.mk₁ [output]⟩)
      ((ordinaryPairTimePolynomial (tapeActionBound caller)).eval
        (input.length + cert.length))) ∧
      TM0.step (ordinaryMachine caller initial) ⟨.done, Tape.mk₁ [output]⟩ = none ∧
      TM0.eval (ordinaryMachine caller initial) (MarkedInput.input tm.k₀ raw) =
        Part.some (ListBlank.mk [output]) := by
  dsimp only
  obtain ⟨⟨run⟩, stopped, evaluated⟩ :=
    ordinary_run_uniform caller initial (BitPairFraming.frame input cert)
  have widened : StateTransition.EvalsToInTime (TM0.step (ordinaryMachine caller initial))
      (TM0.init (MarkedInput.input (machine caller initial).k₀
        (BitPairFraming.frame input cert)))
      (some ⟨.done, Tape.mk₁ [MarkedInput.symbol (machine caller initial).k₀
        (BitPairFraming.verifyFramed (BitPairFraming.frame input cert))]⟩)
      ((ordinaryPairTimePolynomial (tapeActionBound caller)).eval
        (input.length + cert.length)) :=
    { toEvalsTo := run.toEvalsTo
      steps_le_m := run.steps_le_m.trans
        (ordinaryTimeBound_frame_le (tapeActionBound caller) input cert) }
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · simpa only [BitPairFraming.verifyFramed_frame] using widened
  · simpa only [BitPairFraming.verifyFramed_frame] using stopped
  · simpa only [BitPairFraming.verifyFramed_frame] using evaluated

/-- Existing small-certificate completeness supplies the witness. Its literal
frame executes on the actual ordinary machine with the original native run
retained and only the time upper bound composed in the instance length. -/
theorem binaryYes_small_ordinary_run (initial : R) (input : Bits) (yes : BinaryYes input) :
    let tm := machine caller initial
    ∃ cert : Bits,
      cert.length ≤ input.length ^ 2 ∧
      (BitPairFraming.frame input cert).length ≤ (input.length + 1) ^ 2 ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (ordinaryMachine caller initial))
        (TM0.init (MarkedInput.input tm.k₀ (BitPairFraming.frame input cert)))
        (some ⟨.done, Tape.mk₁ [MarkedInput.symbol tm.k₀ true]⟩)
        ((ordinaryWitnessTimePolynomial (tapeActionBound caller)).eval input.length)) ∧
      TM0.step (ordinaryMachine caller initial)
        ⟨.done, Tape.mk₁ [MarkedInput.symbol tm.k₀ true]⟩ = none ∧
      TM0.eval (ordinaryMachine caller initial)
          (MarkedInput.input tm.k₀ (BitPairFraming.frame input cert)) =
        Part.some (ListBlank.mk [MarkedInput.symbol tm.k₀ true]) := by
  dsimp only
  obtain ⟨cert, small, frameSmall, accepted⟩ :=
    BitPairFraming.verifyFramed_complete_small input yes
  obtain ⟨⟨run⟩, stopped, evaluated⟩ :=
    ordinary_run_uniform caller initial (BitPairFraming.frame input cert)
  have widened : StateTransition.EvalsToInTime (TM0.step (ordinaryMachine caller initial))
      (TM0.init (MarkedInput.input (machine caller initial).k₀
        (BitPairFraming.frame input cert)))
      (some ⟨.done, Tape.mk₁ [MarkedInput.symbol (machine caller initial).k₀
        (BitPairFraming.verifyFramed (BitPairFraming.frame input cert))]⟩)
      ((ordinaryWitnessTimePolynomial (tapeActionBound caller)).eval input.length) :=
    { toEvalsTo := run.toEvalsTo
      steps_le_m := run.steps_le_m.trans
        (ordinaryTimeBound_small_frame_le (tapeActionBound caller) input cert small) }
  refine ⟨cert, small, frameSmall, ⟨?_⟩, ?_, ?_⟩
  · simpa only [accepted] using widened
  · simpa only [accepted] using stopped
  · simpa only [accepted] using evaluated

end Resources.RotationCertificate.FrontEndStreamMachine

namespace Resources.RotationCertificate.FrontEndStreamMachine

open Function Turing Turing.TM2to1
open Resources.BinaryCounter (Bits)
open Resources.TuringSimulation.StackToTape
open Resources.TuringSimulation.VisitedSpace

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R)

/-- Consume the actual finite primitive controller witness and retain it.
Every primitive prefix, including intermediate move/write continuations, has a
bounded physical interval containing the input, all visits and all nonblank
cells. The full source halt relation and complete mapped target remain visible.

This is for actual trInit-encoded native initialization, with the supplied
package main/register-derived finite default. No raw serializer, conventional
NP claim, or tighter height-only space estimate is included. -/
theorem finite_encoded_primitive_visited_space (initial : R) (raw : Bits) :
    let tm := machine caller initial
    let : Inhabited (Package.Control tm) := Package.controlInhabited tm
    ∃ target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R),
      TrCfg (Turing.haltList tm [BitPairFraming.verifyFramed raw]) target ∧
      ∃ run : StateTransition.EvalsToInTime (TM0.step (Package.closedMachine tm))
          (TM0.init (trInit (Γ := tm.Γ) tm.k₀ raw))
          (some (Package.mapCfg tm (TM1to0.trCfg (tr (program caller)) target)))
          (encodedPrimitiveTimeBound (tapeActionBound caller) raw.length),
        cfgAt (Package.closedMachine tm) (TM0.init (trInit (Γ := tm.Γ) tm.k₀ raw)) run.steps =
          some (Package.mapCfg tm (TM1to0.trCfg (tr (program caller)) target)) ∧
        ∀ i ≤ run.steps,
          (visitedCells (Package.closedMachine tm) (TM0.init (trInit (Γ := tm.Γ) tm.k₀ raw)) 0 i).card ≤
            encodedPrimitiveTimeBound (tapeActionBound caller) raw.length + 1 ∧
          (inputVisitedCells (Package.closedMachine tm) (TM0.init (trInit (Γ := tm.Γ) tm.k₀ raw))
            0 (trInit (Γ := tm.Γ) tm.k₀ raw).length i).card ≤
            max raw.length 1 + encodedPrimitiveTimeBound (tapeActionBound caller) raw.length ∧
          (visitedInterval (Package.closedMachine tm) (TM0.init (trInit (Γ := tm.Γ) tm.k₀ raw))
            0 (trInit (Γ := tm.Γ) tm.k₀ raw).length i).card ≤
            max raw.length 1 + encodedPrimitiveTimeBound (tapeActionBound caller) raw.length ∧
          ∀ c, cfgAt (Package.closedMachine tm) (TM0.init (trInit (Γ := tm.Γ) tm.k₀ raw)) i = some c →
            headPosition (Package.closedMachine tm) (TM0.init (trInit (Γ := tm.Γ) tm.k₀ raw)) 0 i ∈
              visitedInterval (Package.closedMachine tm) (TM0.init (trInit (Γ := tm.Γ) tm.k₀ raw))
                0 (trInit (Γ := tm.Γ) tm.k₀ raw).length i ∧
            ∀ x, c.Tape.nth (x - headPosition (Package.closedMachine tm)
                (TM0.init (trInit (Γ := tm.Γ) tm.k₀ raw)) 0 i) ≠ default →
              x ∈ visitedInterval (Package.closedMachine tm) (TM0.init (trInit (Γ := tm.Γ) tm.k₀ raw))
                0 (trInit (Γ := tm.Γ) tm.k₀ raw).length i := by
  dsimp only
  let tm := machine caller initial
  let : Inhabited (Package.Control tm) := Package.controlInhabited tm
  obtain ⟨target, related, ⟨run⟩⟩ := finite_encoded_primitive_run_polynomial caller initial raw
  refine ⟨target, related, run, run.evals_in_steps, ?_⟩
  intro i hi
  have hspace := (space_le_of_run (Package.closedMachine tm)
    (TM0.init (trInit (Γ := tm.Γ) tm.k₀ raw))
    (some (Package.mapCfg tm (TM1to0.trCfg (tr (program caller)) target)))
    (encodedPrimitiveTimeBound (tapeActionBound caller) raw.length) run 0
    (trInit (Γ := tm.Γ) tm.k₀ raw).length).2 i hi
  have hlength : max (trInit (Γ := tm.Γ) tm.k₀ raw).length 1 = max raw.length 1 := by
    have nested : max (max raw.length 1) 1 = max raw.length 1 := by omega
    exact (congrArg (fun n : ℕ => max n 1)
      (trInit_length (Γ := tm.Γ) tm.k₀ raw)).trans nested
  refine ⟨hspace.1, ?_, ?_, ?_⟩
  · simpa only [hlength] using hspace.2.1
  · simpa only [hlength] using hspace.2.2
  · intro c hcfg
    refine ⟨?_, ?_⟩
    · exact visitedCells_subset_interval (Package.closedMachine tm)
        (TM0.init (trInit (Γ := tm.Γ) tm.k₀ raw)) 0 (trInit (Γ := tm.Γ) tm.k₀ raw).length i
        (live_head_mem_visitedCells (Package.closedMachine tm)
          (TM0.init (trInit (Γ := tm.Γ) tm.k₀ raw)) c 0 i i le_rfl hcfg)
    · exact init_nonblank_mem_interval_of_run (Package.closedMachine tm)
        (trInit (Γ := tm.Γ) tm.k₀ raw)
        (some (Package.mapCfg tm (TM1to0.trCfg (tr (program caller)) target)))
        (encodedPrimitiveTimeBound (tapeActionBound caller) raw.length)
        run 0 i hi c hcfg

end Resources.RotationCertificate.FrontEndStreamMachine

namespace Resources.RotationCertificate.FrontEndStreamMachine

open Turing
open Resources.BinaryCounter (Bits)
open Resources.TuringSimulation
open Resources.TuringSimulation.StackToTape
open Resources.TuringSimulation.VisitedSpace

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R)

/-- The actual ordinary run and its complete result are retained. Every live
primitive prefix has a polynomial interval containing the declared input,
all actual visits, and every nonblank physical tape cell. The paid terminal
observation adds no visited or enclosing-interval cell. -/
theorem ordinary_native_run_with_visited_space (initial : R) (raw : Bits) :
    let tm := machine caller initial
    let input := MarkedInput.input (Γ := tm.Γ) tm.k₀ raw
    let output := MarkedInput.symbol (Γ := tm.Γ) tm.k₀ (BitPairFraming.verifyFramed raw)
    let finish : TM0.Cfg (Package.Alphabet tm) (MarkedInput.Control (Package.Control tm)) :=
      ⟨.done, Tape.mk₁ [output]⟩
    let B := ordinaryTimeBound (tapeActionBound caller) raw.length
    ∃ run : StateTransition.EvalsToInTime (TM0.step (ordinaryMachine caller initial))
        (TM0.init input) (some finish) B,
      cfgAt (ordinaryMachine caller initial) (TM0.init input) run.steps = some finish ∧
      TM0.step (ordinaryMachine caller initial) finish = none ∧
      TM0.eval (ordinaryMachine caller initial) input = Part.some (ListBlank.mk [output]) ∧
      (∀ i ≤ run.steps,
        (visitedCells (ordinaryMachine caller initial) (TM0.init input) 0 i).card ≤ B + 1 ∧
        (visitedInterval (ordinaryMachine caller initial) (TM0.init input) 0 raw.length i).card ≤
          raw.length + 1 + B ∧
        ∀ reached, cfgAt (ordinaryMachine caller initial) (TM0.init input) i = some reached →
          headPosition (ordinaryMachine caller initial) (TM0.init input) 0 i ∈
            visitedInterval (ordinaryMachine caller initial) (TM0.init input) 0 raw.length i ∧
          ∀ x, reached.Tape.nth
              (x - headPosition (ordinaryMachine caller initial) (TM0.init input) 0 i) ≠ default →
            x ∈ visitedInterval (ordinaryMachine caller initial) (TM0.init input) 0 raw.length i) ∧
      cfgAt (ordinaryMachine caller initial) (TM0.init input) (run.steps + 1) = none ∧
      visitedCells (ordinaryMachine caller initial) (TM0.init input) 0 (run.steps + 1) =
        visitedCells (ordinaryMachine caller initial) (TM0.init input) 0 run.steps ∧
      visitedInterval (ordinaryMachine caller initial) (TM0.init input) 0 raw.length
          (run.steps + 1) =
        visitedInterval (ordinaryMachine caller initial) (TM0.init input) 0 raw.length run.steps := by
  dsimp only
  obtain ⟨⟨run⟩, stopped, evaluated⟩ := ordinary_run_uniform caller initial raw
  refine ⟨run, run.evals_in_steps, stopped, evaluated, ?_, ?_⟩
  · intro i hi
    have observed := (space_le_of_run (ordinaryMachine caller initial)
      (TM0.init (MarkedInput.input (Γ := (machine caller initial).Γ)
        (machine caller initial).k₀ raw)) _
      (ordinaryTimeBound (tapeActionBound caller) raw.length) run 0 raw.length).2 i hi
    refine ⟨observed.1, ?_, ?_⟩
    · exact observed.2.2.trans (Nat.add_le_add_right (by omega) _)
    · intro reached hcfg
      refine ⟨?_, ?_⟩
      · exact visitedCells_subset_interval (ordinaryMachine caller initial) _ 0 raw.length i
          (live_head_mem_visitedCells (ordinaryMachine caller initial) _ reached
            0 i i le_rfl hcfg)
      · have physical := init_nonblank_mem_interval_of_run (ordinaryMachine caller initial)
          (MarkedInput.input (Γ := (machine caller initial).Γ) (machine caller initial).k₀ raw)
          _ (ordinaryTimeBound (tapeActionBound caller) raw.length) run 0 i hi reached hcfg
        have lengthEq := MarkedInput.input_length (Γ := (machine caller initial).Γ)
          (machine caller initial).k₀ raw
        intro x hx
        exact Eq.mp
          (congrArg (fun n : ℕ => x ∈ visitedInterval (ordinaryMachine caller initial)
            (TM0.init (MarkedInput.input (Γ := (machine caller initial).Γ)
              (machine caller initial).k₀ raw)) 0 n i) lengthEq)
          (physical x hx)
  · exact halted_run_adds_no_cells (ordinaryMachine caller initial) _ _
      (ordinaryTimeBound (tapeActionBound caller) raw.length) run stopped 0 raw.length

end Resources.RotationCertificate.FrontEndStreamMachine
