import Applications.Resources.RotationCertificate.CertificateCorrespondence
import Examples.RotationDistance

import Applications.Resources.RotationCertificate.FrontEndStreamTapeMachine
import Examples.RotationCertificateFrontEndStreamMachine

/-!
# Connected native tape runs on the retained controller fixtures

The raw/F01, raw/F02 and raw/V01 source observations remain fixed. Their target
clocks are upper bounds obtained from the public simulation. Initialization
cases distinguish supplied true registers, an absent symbol from some false,
and the separate raw input and Boolean answer stores.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.RotationCertificateFrontEndStreamTapeMachine

open Turing Turing.TM2to1
open Resources.RotationCertificate
open Resources.RotationCertificate.FrontEndStreamMachine
open Resources.TuringSimulation.StackToTape
open Resources.BinaryCounter (Bits)

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R) (initial : R)

theorem empty_raw_rejects_on_tape :
    ∃ target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R),
      TrCfg (Turing.haltList (machine caller initial) [false]) target ∧
      Nonempty (StateTransition.EvalsToInTime (TM1.step (tr (program caller)))
        (encodedInitial (machine caller initial) []) (some target)
        (20 * (1 + tapeActionBound caller * (2 * (1 + tapeActionBound caller) + 2)))) := by
  have output : BitPairFraming.verifyFramed ([] : Bits) = false :=
    Examples.RotationCertificateFrontEndStreamMachine.source_F01_has_its_original_component_tariffs.2
  have clock : runSteps ([] : Bits) = 20 :=
    (Examples.RotationCertificateFrontEndStreamMachine.an_actual_raw_fixture_has_the_canonical_clock caller Examples.RotationCertificateFrontEndStreamMachine.raw_F01
      (initialRegisters initial) (fun _ => [])
      (Examples.RotationCertificateFrontEndStreamMachine.raw_F01_actual_first_halt caller (initialRegisters initial) (fun _ => []))).symm
  have result := encoded_tape_run_bound caller initial []
  rw [output, clock] at result
  exact result

theorem singleton_false_raw_rejects_on_tape :
    ∃ target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R),
      TrCfg (Turing.haltList (machine caller initial) [false]) target ∧
      Nonempty (StateTransition.EvalsToInTime (TM1.step (tr (program caller)))
        (encodedInitial (machine caller initial) [false]) (some target)
        (20 * (1 + tapeActionBound caller * (2 * (1 + tapeActionBound caller) + 2)))) := by
  have output : BitPairFraming.verifyFramed ([false] : Bits) = false :=
    Examples.RotationCertificateFrontEndStreamMachine.source_F02_has_its_original_component_tariffs.2
  have clock : runSteps ([false] : Bits) = 20 :=
    (Examples.RotationCertificateFrontEndStreamMachine.an_actual_raw_fixture_has_the_canonical_clock caller Examples.RotationCertificateFrontEndStreamMachine.raw_F02
      (initialRegisters initial) (fun _ => [])
      (Examples.RotationCertificateFrontEndStreamMachine.raw_F02_actual_first_halt caller (initialRegisters initial) (fun _ => []))).symm
  have result := encoded_tape_run_bound caller initial [false]
  rw [output, clock] at result
  exact result

theorem literal_equal_leaf_raw_accepts_on_tape :
    ∃ target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R),
      TrCfg (Turing.haltList (machine caller initial) [true]) target ∧
      Nonempty (StateTransition.EvalsToInTime (TM1.step (tr (program caller)))
        (encodedInitial (machine caller initial) Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw) (some target)
        (95 * (1 + tapeActionBound caller * (2 * (41 + tapeActionBound caller) + 2)))) := by
  have output : BitPairFraming.verifyFramed Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw = true :=
    Examples.RotationCertificateFrontEndStreamMachine.source_V01_has_its_original_component_tariffs.2
  have clock : runSteps Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw = 95 :=
    (Examples.RotationCertificateFrontEndStreamMachine.an_actual_raw_fixture_has_the_canonical_clock caller Examples.RotationCertificateFrontEndStreamMachine.raw_V01
      (initialRegisters initial) (fun _ => [])
      (Examples.RotationCertificateFrontEndStreamMachine.raw_V01_actual_first_halt caller (initialRegisters initial) (fun _ => []))).symm
  have length : Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw.length = 41 := rfl
  have result := encoded_tape_run_bound caller initial Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw
  rw [output, clock, length] at result
  exact result

theorem literal_equal_leaf_has_the_explicit_polynomial_bound :
    ∃ target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R),
      TrCfg (Turing.haltList (machine caller initial) [true]) target ∧
      Nonempty (StateTransition.EvalsToInTime (TM1.step (tr (program caller)))
        (encodedInitial (machine caller initial) Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw) (some target)
        (2127 * (1 + tapeActionBound caller * (2 * (42 + tapeActionBound caller) + 2)))) := by
  have output : BitPairFraming.verifyFramed Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw = true :=
    Examples.RotationCertificateFrontEndStreamMachine.source_V01_has_its_original_component_tariffs.2
  have length : Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw.length = 41 := rfl
  have result := encoded_tape_run_polynomial caller initial Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw
  rw [output, length] at result
  exact result

/- A concrete nondefault register case: the requested user state is true. The
global Bool default is false, so using ambient defaults would violate this case. -/
def haltCaller : Unit → Statement (fun _ : Unit => Bool) Unit Bool :=
  fun _ => TM2.Stmt.halt

theorem explicit_true_initial_registers (raw : Bits) :
    (encodedInitial (machine haltCaller true) raw).l =
        some (Λ'.normal (machine haltCaller true).main) ∧
      (encodedInitial (machine haltCaller true) raw).var = initialRegisters true ∧
      user (encodedInitial (machine haltCaller true) raw).var = true :=
  ⟨rfl, rfl, rfl⟩

theorem empty_encoded_input_has_a_marker_without_a_raw_symbol :
    (encodedInitial (machine haltCaller true) []).Tape.head.1 = true ∧
      (encodedInitial (machine haltCaller true) []).Tape.head.2
        (machine haltCaller true).k₀ = none ∧
      (trInit (Γ := (machine haltCaller true).Γ) (machine haltCaller true).k₀ ([] : Bits)).length = 1 :=
  ⟨rfl, rfl, rfl⟩

theorem singleton_false_encoded_input_has_a_symbol_on_its_marker :
    (encodedInitial (machine haltCaller true) [false]).Tape.head.1 = true ∧
      (encodedInitial (machine haltCaller true) [false]).Tape.head.2
        (machine haltCaller true).k₀ = some false ∧
      (trInit (Γ := (machine haltCaller true).Γ) (machine haltCaller true).k₀ ([false] : Bits)).length = 1 :=
  ⟨rfl, rfl, rfl⟩

theorem the_boolean_answer_store_is_not_the_raw_input_store :
    (machine haltCaller true).k₀ ≠ (machine haltCaller true).k₁ ∧
      (Turing.haltList (machine haltCaller true) [true]).stk
        (machine haltCaller true).k₀ = [] ∧
      (Turing.haltList (machine haltCaller true) [true]).stk
        (machine haltCaller true).k₁ = [true] := by
  refine ⟨machine_input_ne_output haltCaller true, ?_, ?_⟩
  · exact machine_haltList_framedRaw haltCaller true [true]
  · rfl

/-
Connected controller clients prepared before compiler feedback. Append inside
Examples.RotationCertificateFrontEndStreamTapeMachine, after haltCaller and its
native-tape initialization cases. All source fixtures and clocks are retained.
-/

theorem empty_raw_rejects_on_finite_primitive :
    let tm := machine caller initial
    letI : Inhabited (Package.Control tm) := Package.controlInhabited tm
    ∃ target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R),
      TrCfg (Turing.haltList tm [false]) target ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (Package.closedMachine tm))
        (TM0.init (trInit tm.k₀ []))
        (some (Package.mapCfg tm (TM1to0.trCfg (tr (program caller)) target)))
        (3 * (20 * (1 + tapeActionBound caller *
          (2 * (1 + tapeActionBound caller) + 2))))) := by
  have output : BitPairFraming.verifyFramed ([] : Bits) = false :=
    Examples.RotationCertificateFrontEndStreamMachine.source_F01_has_its_original_component_tariffs.2
  have clock : runSteps ([] : Bits) = 20 :=
    (Examples.RotationCertificateFrontEndStreamMachine.an_actual_raw_fixture_has_the_canonical_clock
      caller Examples.RotationCertificateFrontEndStreamMachine.raw_F01
      (initialRegisters initial) (fun _ => [])
      (Examples.RotationCertificateFrontEndStreamMachine.raw_F01_actual_first_halt
        caller (initialRegisters initial) (fun _ => []))).symm
  have result := finite_encoded_primitive_run_bound caller initial []
  rw [output, clock] at result
  exact result

theorem singleton_false_raw_rejects_on_finite_primitive :
    let tm := machine caller initial
    letI : Inhabited (Package.Control tm) := Package.controlInhabited tm
    ∃ target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R),
      TrCfg (Turing.haltList tm [false]) target ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (Package.closedMachine tm))
        (TM0.init (trInit tm.k₀ [false]))
        (some (Package.mapCfg tm (TM1to0.trCfg (tr (program caller)) target)))
        (3 * (20 * (1 + tapeActionBound caller *
          (2 * (1 + tapeActionBound caller) + 2))))) := by
  have output : BitPairFraming.verifyFramed ([false] : Bits) = false :=
    Examples.RotationCertificateFrontEndStreamMachine.source_F02_has_its_original_component_tariffs.2
  have clock : runSteps ([false] : Bits) = 20 :=
    (Examples.RotationCertificateFrontEndStreamMachine.an_actual_raw_fixture_has_the_canonical_clock
      caller Examples.RotationCertificateFrontEndStreamMachine.raw_F02
      (initialRegisters initial) (fun _ => [])
      (Examples.RotationCertificateFrontEndStreamMachine.raw_F02_actual_first_halt
        caller (initialRegisters initial) (fun _ => []))).symm
  have result := finite_encoded_primitive_run_bound caller initial [false]
  rw [output, clock] at result
  exact result

theorem literal_equal_leaf_raw_accepts_on_finite_primitive :
    let tm := machine caller initial
    letI : Inhabited (Package.Control tm) := Package.controlInhabited tm
    ∃ target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R),
      TrCfg (Turing.haltList tm [true]) target ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (Package.closedMachine tm))
        (TM0.init (trInit tm.k₀
          Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw))
        (some (Package.mapCfg tm (TM1to0.trCfg (tr (program caller)) target)))
        (3 * (95 * (1 + tapeActionBound caller *
          (2 * (41 + tapeActionBound caller) + 2))))) := by
  have output : BitPairFraming.verifyFramed
      Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw = true :=
    Examples.RotationCertificateFrontEndStreamMachine.source_V01_has_its_original_component_tariffs.2
  have clock : runSteps Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw = 95 :=
    (Examples.RotationCertificateFrontEndStreamMachine.an_actual_raw_fixture_has_the_canonical_clock
      caller Examples.RotationCertificateFrontEndStreamMachine.raw_V01
      (initialRegisters initial) (fun _ => [])
      (Examples.RotationCertificateFrontEndStreamMachine.raw_V01_actual_first_halt
        caller (initialRegisters initial) (fun _ => []))).symm
  have length : Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw.length = 41 := rfl
  have result := finite_encoded_primitive_run_bound caller initial
    Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw
  rw [output, clock, length] at result
  exact result

theorem literal_equal_leaf_primitive_polynomial_bound :
    let tm := machine caller initial
    letI : Inhabited (Package.Control tm) := Package.controlInhabited tm
    ∃ target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R),
      TrCfg (Turing.haltList tm [true]) target ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (Package.closedMachine tm))
        (TM0.init (trInit tm.k₀
          Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw))
        (some (Package.mapCfg tm (TM1to0.trCfg (tr (program caller)) target)))
        (3 * (2127 * (1 + tapeActionBound caller *
          (2 * (42 + tapeActionBound caller) + 2))))) := by
  have output : BitPairFraming.verifyFramed
      Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw = true :=
    Examples.RotationCertificateFrontEndStreamMachine.source_V01_has_its_original_component_tariffs.2
  have length : Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw.length = 41 := rfl
  have result := finite_encoded_primitive_run_polynomial caller initial
    Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw
  rw [output, length] at result
  exact result

theorem literal_equal_leaf_primitive_outer_none_pays_one_more :
    let tm := machine caller initial
    letI : Inhabited (Package.Control tm) := Package.controlInhabited tm
    Nonempty (StateTransition.EvalsToInTime (TM0.step (Package.closedMachine tm))
      (TM0.init (trInit tm.k₀
        Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw)) none
      (3 * (2127 * (1 + tapeActionBound caller *
        (2 * (42 + tapeActionBound caller) + 2))) + 1)) := by
  have length : Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw.length = 41 := rfl
  have result := finite_encoded_primitive_outer_none caller initial
    Examples.RotationCertificateFrontEndStreamMachine.raw_V01.raw
  rw [length] at result
  exact result

theorem finite_native_initial_uses_true_registers (raw : Bits) :
    let tm := machine haltCaller true
    letI : Inhabited (Package.Control tm) := Package.controlInhabited tm
    let start : TM0.Cfg (Package.Alphabet tm) (Package.Control tm) :=
      TM0.init (trInit tm.k₀ raw)
    start.q.val.2 = initialRegisters true ∧ user start.q.val.2 = true :=
  ⟨rfl, rfl⟩

theorem finite_native_empty_keeps_marker_and_absent_symbol :
    let tm := machine haltCaller true
    letI : Inhabited (Package.Control tm) := Package.controlInhabited tm
    let start : TM0.Cfg (Package.Alphabet tm) (Package.Control tm) :=
      TM0.init (trInit tm.k₀ [])
    start.Tape.head.1 = true ∧ start.Tape.head.2 tm.k₀ = none :=
  ⟨rfl, rfl⟩

theorem finite_native_false_keeps_marker_and_present_false :
    let tm := machine haltCaller true
    letI : Inhabited (Package.Control tm) := Package.controlInhabited tm
    let start : TM0.Cfg (Package.Alphabet tm) (Package.Control tm) :=
      TM0.init (trInit tm.k₀ [false])
    start.Tape.head.1 = true ∧ start.Tape.head.2 tm.k₀ = some false :=
  ⟨rfl, rfl⟩

theorem finite_restriction_preserves_the_complete_tape
    (c : TM0.Cfg (Package.Alphabet (machine haltCaller true))
      (Package.AmbientControl (machine haltCaller true))) :
    (Package.mapCfg (machine haltCaller true) c).Tape = c.Tape :=
  Package.mapCfg_tape (machine haltCaller true) c

end Examples.RotationCertificateFrontEndStreamTapeMachine

namespace Examples.RotationCertificateFrontEndStreamTapeMachine.CertificateTime

open Turing Turing.TM2to1
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate
open Resources.RotationCertificate.CertificateCorrespondence
open Resources.RotationCertificate.FrontEndStreamMachine
open Resources.TuringSimulation.StackToTape
open RotationDistanceExample (empty)

/-- The four fixed A=0/1 and N=0/1 observations include both zero boundaries. -/
theorem primitive_bound_literal_values :
    encodedPrimitiveTimeBound 0 0 = 108 ∧
      encodedPrimitiveTimeBound 0 1 = 141 ∧
      encodedPrimitiveTimeBound 1 0 = 756 ∧
      encodedPrimitiveTimeBound 1 1 = 1269 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Each polynomial evaluation is connected to the actual bound definition. -/
theorem primitive_polynomial_literal_values :
    (encodedPrimitiveTimePolynomial 0).eval 0 = 108 ∧
      (encodedPrimitiveTimePolynomial 0).eval 1 = 141 ∧
      (encodedPrimitiveTimePolynomial 1).eval 0 = 756 ∧
      (encodedPrimitiveTimePolynomial 1).eval 1 = 1269 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [encodedPrimitiveTimePolynomial_eval] <;> rfl

/-- At instance length zero the composed argument is one, not zero. This
is arithmetic only; the empty raw instance is not a yes instance. -/
theorem witness_polynomial_zero_argument :
    (encodedPrimitiveWitnessPolynomial 0).eval 0 = 141 ∧
      (encodedPrimitiveWitnessPolynomial 1).eval 0 = 1269 := by
  constructor <;> rw [encodedPrimitiveWitnessPolynomial_eval] <;> rfl

/-- The fixed generic frame allowance at the twenty-bit empty-tree instance
is441. It is distinct from the literal empty-certificate frame length41. -/
theorem empty_instance_generic_frame_allowance :
    ((wordBits (inputCode empty.val empty.val [])).length + 1) ^ 2 = 441 ∧
      (BitPairFraming.frame (wordBits (inputCode empty.val empty.val [])) []).length = 41 := by
  have inputLength : (wordBits (inputCode empty.val empty.val [])).length = 20 :=
    (encoded_instance_length empty empty []).trans rfl
  constructor
  · rw [inputLength]
    decide
  · rw [BitPairFraming.frame_length, inputLength]
    rfl

/-- This consumer applies the actual monotonicity and proved frame bound,
including A=0 and all small malformed pairs as well as accepting pairs. -/
theorem small_frame_bound_uses_the_instance_polynomial (A : Nat) (input cert : Bits)
    (small : cert.length ≤ input.length ^ 2) :
    encodedPrimitiveTimeBound A (BitPairFraming.frame input cert).length ≤
      (encodedPrimitiveWitnessPolynomial A).eval input.length := by
  rw [encodedPrimitiveWitnessPolynomial_eval]
  exact encodedPrimitiveTimeBound_mono A
    (BitPairFraming.frame_length_le_square input cert small)

/-- The all-pair bound does not require valid syntax or a bounded certificate. -/
theorem arbitrary_pair_bound_keeps_both_input_lengths (A : Nat) (input cert : Bits) :
    encodedPrimitiveTimeBound A (BitPairFraming.frame input cert).length ≤
      encodedPrimitiveTimeBound A (2 * (input.length + cert.length + 1)) :=
  encodedPrimitiveTimeBound_frame_le A input cert

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R)

/-- A concrete yes instance discharges the new finite-machine consumer's
language premise. Its witness allowance is400 and its frame allowance441;
neither allowance replaces the actual run's stored transition count. -/
theorem empty_instance_has_an_actual_finite_primitive_witness (initial : R) :
    let tm := machine caller initial
    let : Inhabited (Package.Control tm) := Package.controlInhabited tm
    ∃ (cert : Bits)
      (target : TM1.Cfg (Γ' (StackId K) (alphabet Γ))
        (Λ' (StackId K) (alphabet Γ) (Label Λ) (Registers R)) (Registers R)),
      cert.length ≤ 400 ∧
      (BitPairFraming.frame (wordBits (inputCode empty.val empty.val [])) cert).length ≤ 441 ∧
      TrCfg (Turing.haltList tm [true]) target ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (Package.closedMachine tm))
        (TM0.init (trInit tm.k₀
          (BitPairFraming.frame (wordBits (inputCode empty.val empty.val [])) cert)))
        (some (Package.mapCfg tm (TM1to0.trCfg (tr (program caller)) target)))
        (encodedPrimitiveTimeBound (tapeActionBound caller) 441)) := by
  have yes := binaryYes_empty_shapes empty empty ([] : Bits)
  have run := binaryYes_small_finite_primitive_run caller initial
    (wordBits (inputCode empty.val empty.val [])) yes
  have inputLength : (wordBits (inputCode empty.val empty.val [])).length = 20 :=
    (encoded_instance_length empty empty []).trans rfl
  simpa only [inputLength, show (20 : Nat) ^ 2 = 400 by decide,
    show ((20 : Nat) + 1) ^ 2 = 441 by decide] using run

end Examples.RotationCertificateFrontEndStreamTapeMachine.CertificateTime

namespace Examples.RotationCertificateFrontEndStreamTapeMachine.Ordinary

open Function Turing
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate
open Resources.RotationCertificate.FrontEndStreamMachine
open Resources.TuringSimulation
open Resources.TuringSimulation.StackToTape

theorem ordinary_bound_fixed_values :
    ordinaryTimeBound 0 0 = 111 ∧ ordinaryTimeBound 0 1 = 145 ∧
      ordinaryTimeBound 1 0 = 759 ∧ ordinaryTimeBound 1 1 = 1273 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem ordinary_polynomial_fixed_values :
    (ordinaryTimePolynomial 0).eval 0 = 111 ∧
      (ordinaryTimePolynomial 0).eval 1 = 145 ∧
      (ordinaryTimePolynomial 1).eval 0 = 759 ∧
      (ordinaryTimePolynomial 1).eval 1 = 1273 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [ordinaryTimePolynomial_eval] <;> rfl

theorem all_pair_polynomial_at_zero :
    (ordinaryPairTimePolynomial 0).eval 0 = 185 ∧
      (ordinaryPairTimePolynomial 1).eval 0 = 1985 := by
  constructor <;> rw [ordinaryPairTimePolynomial_eval] <;> rfl

theorem small_witness_polynomial_at_zero :
    (ordinaryWitnessTimePolynomial 0).eval 0 = 145 ∧
      (ordinaryWitnessTimePolynomial 1).eval 0 = 1273 := by
  constructor <;> rw [ordinaryWitnessTimePolynomial_eval] <;> rfl

theorem literal_empty_pair_frame :
    BitPairFraming.frame [] [] = [true] ∧
      (BitPairFraming.frame [] []).length = 1 := ⟨rfl, rfl⟩

/-- Fixed finite data, with the caller's Boolean initial register supplied as
true before any raw word is introduced. -/
def haltCaller : Bool → Statement (fun _ : Bool => Bool) Bool Bool := fun _ => .halt

abbrev fixedPackage : FinTM2 := machine haltCaller true

def fixedBit : Bool → Package.Alphabet fixedPackage :=
  MarkedInput.symbol (Γ := fixedPackage.Γ) fixedPackage.k₀

def fixedInput (raw : Bits) : List (Package.Alphabet fixedPackage) :=
  MarkedInput.input (Γ := fixedPackage.Γ) fixedPackage.k₀ raw

noncomputable def fixedDecider : PolynomialBooleanDecider BitPairFraming.verifyFramed :=
  ordinaryPolynomialDecider haltCaller true

theorem fixed_input_is_literal_letter_map (raw : Bits) :
    fixedInput raw = raw.map fixedBit := rfl

theorem true_initial_register_is_preserved_by_the_source_default :
    user ((Package.controlInhabited fixedPackage).default.val.2) = true :=
  ordinary_source_default_user haltCaller true

theorem wrapper_start_is_the_fixed_prelude_start :
    fixedDecider.start =
      (MarkedInput.Control.start : MarkedInput.Control (Package.Control fixedPackage)) := rfl

theorem fixed_false_letter_is_not_blank : fixedDecider.bit false ≠ fixedDecider.blank :=
  fixedDecider.false_ne_blank

theorem fixed_true_and_false_letters_differ : fixedDecider.bit true ≠ fixedDecider.bit false :=
  fixedDecider.true_ne_false

theorem empty_and_present_false_have_distinct_complete_native_tapes :
    Tape.mk₁ (fixedInput []) ≠ Tape.mk₁ (fixedInput [false]) := by
  intro equal
  have observed := congrArg
    (fun T : Tape (Package.Alphabet fixedPackage) => T.head.2 fixedPackage.k₀) equal
  change none = some false at observed
  cases observed

/-- The actual empty-input prelude reaches the supplied supported source
control and the complete marked blank tape in one native write. -/
theorem true_initial_empty_prelude :
    (flip Bind.bind (TM0.step (ordinaryMachine haltCaller true)))^[1]
      (some (TM0.init (fixedInput []))) =
      some ⟨.run (Package.controlInhabited fixedPackage).default,
        Tape.mk (true, fun _ => none) ∅ ∅⟩ := by
  let : Inhabited (Package.Control fixedPackage) := Package.controlInhabited fixedPackage
  exact MarkedInput.prelude_exact (Γ := fixedPackage.Γ) fixedPackage.k₀
    (Package.closedMachine fixedPackage)
    (ordinaryEmitter haltCaller true) []

/-- A present false letter is scanned and marked, with its full tape retained.
The supplied source register is still the same true initial register. -/
theorem true_initial_false_prelude :
    (flip Bind.bind (TM0.step (ordinaryMachine haltCaller true)))^[3]
      (some (TM0.init (fixedInput [false]))) =
      some ⟨.run (Package.controlInhabited fixedPackage).default,
        Tape.mk (true, (fixedBit false).2) ∅ ∅⟩ := by
  let : Inhabited (Package.Control fixedPackage) := Package.controlInhabited fixedPackage
  have encoded : TM2to1.trInit (Γ := fixedPackage.Γ) fixedPackage.k₀ [false] =
      [(true, (fixedBit false).2)] := rfl
  have reflected : TapeReflection.tape
      (Tape.mk₁ (TM2to1.trInit (Γ := fixedPackage.Γ) fixedPackage.k₀ [false])) =
      Tape.mk (true, (fixedBit false).2) ∅ ∅ :=
    (congrArg (fun input : List (Package.Alphabet fixedPackage) =>
      TapeReflection.tape (Tape.mk₁ input)) encoded).trans
        (SingletonOutput.reflection_singleton
          ((true, (fixedBit false).2) : Package.Alphabet fixedPackage))
  have actual := MarkedInput.prelude_exact (Γ := fixedPackage.Γ) fixedPackage.k₀
    (Package.closedMachine fixedPackage) (ordinaryEmitter haltCaller true) [false]
  exact actual.trans
    (congrArg (fun T : Tape (Package.Alphabet fixedPackage) =>
      (some ⟨MarkedInput.Control.run (Package.controlInhabited fixedPackage).default, T⟩ :
        Option (TM0.Cfg (Package.Alphabet fixedPackage)
          (MarkedInput.Control (Package.Control fixedPackage))))) reflected)

/-- The complete malformed empty input really returns the ordinary false
singleton under native evaluation. -/
theorem empty_raw_native_eval :
    TM0.eval (ordinaryMachine haltCaller true) (fixedInput []) =
      Part.some (ListBlank.mk [fixedBit false]) := by
  have answer : BitPairFraming.verifyFramed [] = false := rfl
  simpa only [fixedInput, fixedBit, answer] using (ordinary_run_and_eval haltCaller true []).2

theorem present_false_raw_native_eval :
    TM0.eval (ordinaryMachine haltCaller true) (fixedInput [false]) =
      Part.some (ListBlank.mk [fixedBit false]) := by
  have answer : BitPairFraming.verifyFramed [false] = false := rfl
  simpa only [fixedInput, fixedBit, answer] using (ordinary_run_and_eval haltCaller true [false]).2

/-- No syntax or small-certificate premise: every pair uses the same fixed
machine and supplies an actual bounded native run with a whole singleton. -/
theorem fixed_program_all_pairs (input cert : Bits) :
    ∃ finish : TM0.Cfg (Package.Alphabet fixedPackage)
        (MarkedInput.Control (Package.Control fixedPackage)),
      Nonempty (StateTransition.EvalsToInTime (TM0.step (ordinaryMachine haltCaller true))
        (TM0.init (fixedInput (BitPairFraming.frame input cert))) (some finish)
        ((ordinaryPairTimePolynomial (tapeActionBound haltCaller)).eval
          (input.length + cert.length))) ∧
      finish.Tape = Tape.mk₁ [fixedBit (verifyBitsRun input cert).1] ∧
      TM0.step (ordinaryMachine haltCaller true) finish = none := by
  obtain ⟨run, stopped, _⟩ := ordinary_pair_run_and_eval haltCaller true input cert
  exact ⟨⟨.done, Tape.mk₁ [fixedBit (verifyBitsRun input cert).1]⟩, run, rfl, stopped⟩

end Examples.RotationCertificateFrontEndStreamTapeMachine.Ordinary
