import PrefixComposition144b
import SourceRunToOrdinary148
import Applications.Resources.TuringSimulation.PrintMove

set_option autoImplicit false
set_option warningAsError true

/-!
# Paid delimiter preprocessing through the ordinary native machine

UNCOMPILED implementation draft. The research import PrefixComposition144b must
be supplied from the exact retained delimiter family. The proofs below consume
its actual source run and all-prefix occupancy. The native input remains the
literal three-letter word, with some Boolean as the fixed output-letter map.
-/

namespace Resources.RotationCertificate.DelimiterPreludeDraft.NativeConsumer148

open Function Turing
open Resources.TuringSimulation
open Resources.TuringSimulation.StackToTape

variable {R : Type} [Fintype R]

abbrev Alphabet (initial : R) := OrdinaryPackage.Alphabet (machine initial)

abbrev Control (initial : R) := OrdinaryPackage.Control (machine initial)

/-- All source stack alphabets are finite independently of the raw word. -/
@[instance_reducible] def alphabetFintype (initial : R) : Fintype (Alphabet initial) := by
  let : ∀ k, Fintype ((machine initial).Γ k) := machineAlphabetFintype initial
  exact OrdinaryPackage.alphabetFintype (machine initial)

/-- Finite supported native control, with the fixed prelude phases added. -/
@[instance_reducible] noncomputable def controlFintype (initial : R) :
    Fintype (Control initial) := OrdinaryPackage.controlFintype (machine initial)

/-- The three actual input letters are injected before any input word. -/
def inputLetter (initial : R) : Option Bool ↪ Alphabet initial :=
  OrdinaryPackage.inputLetter (machine initial)

/-- Boolean output uses the two bit letters within that same work alphabet. -/
def outputLetter (initial : R) :
    (machine initial).Γ (machine initial).k₁ → (machine initial).Γ (machine initial).k₀ :=
  fun answer => some answer

def outputBit (initial : R) : Bool ↪ Alphabet initial :=
  ⟨fun answer => inputLetter initial (some answer), fun _ _ same =>
    Option.some.inj ((inputLetter initial).injective same)⟩

/-- This is only a per-letter map on the supplied literal input. -/
def ordinaryInput (initial : R) (raw : Raw) : List (Alphabet initial) :=
  raw.map (inputLetter initial)

def ordinaryMachine (initial : R) :
    @TM0.Machine (Alphabet initial) (Control initial)
      (OrdinaryPackage.controlInhabited (machine initial)) :=
  OrdinaryPackage.machine (machine initial) (outputLetter initial) false

/-- The complete live output includes both blank tails. -/
def ordinaryOutput (initial : R) (answer : Bool) : TM0.Cfg (Alphabet initial) (Control initial) :=
  OrdinaryPackage.outputCfg (machine initial) (outputLetter initial) answer

theorem input_ne_blank (initial : R) (letter : Option Bool) :
    inputLetter initial letter ≠ (default : Alphabet initial) :=
  OrdinaryPackage.inputLetter_ne_blank (machine initial) letter

theorem delimiter_is_present (initial : R) :
    (inputLetter initial none).2 inputIndex = some none :=
  OrdinaryPackage.inputLetter_selected (machine initial) none

theorem false_is_present (initial : R) :
    (inputLetter initial (some false)).2 inputIndex = some (some false) :=
  OrdinaryPackage.inputLetter_selected (machine initial) (some false)

theorem delimiter_ne_false (initial : R) :
    inputLetter initial none ≠ inputLetter initial (some false) := by
  intro same
  have impossible := (inputLetter initial).injective same
  cases impossible

theorem supplied_source_registers (initial : R) :
    (OrdinaryPackage.sourceDefault (machine initial)).val.2 =
      FrontEndStreamMachine.initialRegisters (none, initial) := rfl

theorem supplied_source_main (initial : R) :
    (machine initial).main = FrontEndStreamMachine.callerLabel .prefix := rfl

theorem input_output_distinct (initial : R) :
    (machine initial).k₀ ≠ (machine initial).k₁ := by
  intro same
  cases same

theorem ordinaryInput_length (initial : R) (raw : Raw) :
    (ordinaryInput initial raw).length = raw.length := by
  simp only [ordinaryInput, List.length_map]

theorem literal_input_length (initial : R) (input cert : Resources.BinaryCounter.Bits) :
    (ordinaryInput initial (literalPair input cert)).length =
      input.length + cert.length + 1 :=
  (ordinaryInput_length initial (literalPair input cert)).trans (literalPair_length input cert)

theorem ordinaryOutput_tape (initial : R) (answer : Bool) :
    (ordinaryOutput initial answer).Tape = Tape.mk₁ [outputBit initial answer] := rfl

theorem ordinaryOutput_stopped (initial : R) (answer : Bool) :
    TM0.step (ordinaryMachine initial) (ordinaryOutput initial answer) = none := rfl

/-- The retained all-prefix theorem supplies the generic compiler premise.
The only weakening is max(2N,1) ≤ 2N+1, already used by the frozen allowance. -/
theorem source_prefix_occupancy (initial : R) (raw : Raw) (i : ℕ) (c : Cfg R)
    (within : i < (GeneralProof1.outputsInTime initial raw).steps)
    (reached : (flip Bind.bind (machine initial).step)^[i]
      (some (initList (machine initial) raw)) = some c) :
    (∑ k, (c.stk k).length) ≤ 2 * raw.length + 1 := by
  change i < totalSourceSteps raw at within
  have cells : FrontEndStreamMachine.stackCells c ≤ max (2 * raw.length) 1 :=
    GeneralProof1.total_prefix_cells initial raw i (Nat.le_of_lt within) c reached
  change FrontEndStreamMachine.stackCells c ≤ 2 * raw.length + 1
  exact cells.trans (by omega)

/-- Real primitive execution from the literal package initializer, with the
complete halt relation and the originally frozen polynomial allowance. -/
theorem encoded_native_run (initial : R) (raw : Raw) :
    ∃ target : OrdinaryPackage.NativeTarget (machine initial),
      TM2to1.TrCfg (haltList (machine initial) [verifyDelimited raw]) target ∧
      Nonempty (OrdinaryPackage.EncodedRun (machine initial) raw target
        (encodedPrimitiveTimeBound (actionMaximum (R := R)) raw.length)) := by
  obtain ⟨target, related, ⟨run⟩⟩ := OrdinaryPackage.encodedRun_of_outputsInTime
    (machine initial) raw [verifyDelimited raw] (sourceTimeBound raw.length)
    (2 * raw.length + 1) (GeneralProof1.outputsInTime initial raw)
    (source_prefix_occupancy initial raw)
  refine ⟨target, related, ⟨{ toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }⟩⟩
  let : Fintype (machine initial).Λ := (machine initial).ΛFin
  have actionEq : finiteActionBound (machine initial).m = actionMaximum (R := R) := rfl
  have allowanceEq :
      3 * (sourceTimeBound raw.length *
        (1 + finiteActionBound (machine initial).m *
          (2 * ((2 * raw.length + 1) + finiteActionBound (machine initial).m) + 2))) =
      encodedPrimitiveTimeBound (actionMaximum (R := R)) raw.length := by
    rw [actionEq]
    simp only [encodedPrimitiveTimeBound, Nat.mul_assoc]
  exact run.steps_le_m.trans allowanceEq.le

/-- Both native witnesses retain their actual counts. The ordinary prelude
and output write are paid on top of the generated primitive witness. -/
theorem ordinary_run (initial : R) (raw : Raw) :
    ∃ target : OrdinaryPackage.NativeTarget (machine initial),
      TM2to1.TrCfg (haltList (machine initial) [verifyDelimited raw]) target ∧
      ∃ before : OrdinaryPackage.EncodedRun (machine initial) raw target
          (encodedPrimitiveTimeBound (actionMaximum (R := R)) raw.length),
        ∃ live : StateTransition.EvalsToInTime (TM0.step (ordinaryMachine initial))
            (TM0.init (ordinaryInput initial raw))
            (some (ordinaryOutput initial (verifyDelimited raw)))
            (MarkedInput.preludeSteps raw +
              encodedPrimitiveTimeBound (actionMaximum (R := R)) raw.length + 1),
          ∃ after : StateTransition.EvalsToInTime (TM0.step (ordinaryMachine initial))
              (TM0.init (ordinaryInput initial raw)) none
              (MarkedInput.preludeSteps raw +
                encodedPrimitiveTimeBound (actionMaximum (R := R)) raw.length + 2),
            live.steps = 1 + (before.steps + MarkedInput.preludeSteps raw) ∧
            after.steps = 1 + live.steps ∧
            TM0.step (ordinaryMachine initial) (ordinaryOutput initial (verifyDelimited raw)) = none ∧
            TM0.eval (ordinaryMachine initial) (ordinaryInput initial raw) =
              Part.some (ListBlank.mk [outputBit initial (verifyDelimited raw)]) := by
  obtain ⟨target, related, ⟨before⟩⟩ := encoded_native_run initial raw
  let live := OrdinaryPackage.runInTime (machine initial) (outputLetter initial) false
    raw (verifyDelimited raw) target related
    (encodedPrimitiveTimeBound (actionMaximum (R := R)) raw.length) before
  let after := OrdinaryPackage.nextNoneRun (machine initial) (outputLetter initial) false
    raw (verifyDelimited raw) target related
    (encodedPrimitiveTimeBound (actionMaximum (R := R)) raw.length) before
  exact ⟨target, related, before, live, after,
    OrdinaryPackage.runInTime_steps (machine initial) (outputLetter initial) false
      raw (verifyDelimited raw) target related
      (encodedPrimitiveTimeBound (actionMaximum (R := R)) raw.length) before,
    OrdinaryPackage.nextNoneRun_steps (machine initial) (outputLetter initial) false
      raw (verifyDelimited raw) target related
      (encodedPrimitiveTimeBound (actionMaximum (R := R)) raw.length) before,
    ordinaryOutput_stopped initial (verifyDelimited raw),
    OrdinaryPackage.eval_of_run (machine initial) (outputLetter initial) false
      raw (verifyDelimited raw) target related
      (encodedPrimitiveTimeBound (actionMaximum (R := R)) raw.length) before⟩

/-- A convenient live-only observation, retaining the exact complete tape. -/
theorem ordinary_live (initial : R) (raw : Raw) :
    Nonempty (StateTransition.EvalsToInTime (TM0.step (ordinaryMachine initial))
      (TM0.init (ordinaryInput initial raw))
      (some (ordinaryOutput initial (verifyDelimited raw)))
      (MarkedInput.preludeSteps raw +
        encodedPrimitiveTimeBound (actionMaximum (R := R)) raw.length + 1)) := by
  obtain ⟨_target, _related, _before, live, _after, _facts⟩ := ordinary_run initial raw
  exact ⟨live⟩

theorem ordinary_literal_pair (initial : R) (input cert : Resources.BinaryCounter.Bits) :
    Nonempty (StateTransition.EvalsToInTime (TM0.step (ordinaryMachine initial))
      (TM0.init (ordinaryInput initial (literalPair input cert)))
      (some (ordinaryOutput initial ((verifyBitsRun input cert).1)))
      (MarkedInput.preludeSteps (literalPair input cert) +
        encodedPrimitiveTimeBound (actionMaximum (R := R)) (literalPair input cert).length + 1)) := by
  simpa only [verifyDelimited_pair] using ordinary_live initial (literalPair input cert)

/-- Missing and repeated delimiters use the already proved cleanup run. -/
theorem ordinary_malformed (initial : R) (raw : Raw) (malformed : splitLiteral raw = none) :
    Nonempty (StateTransition.EvalsToInTime (TM0.step (ordinaryMachine initial))
      (TM0.init (ordinaryInput initial raw)) (some (ordinaryOutput initial false))
      (MarkedInput.preludeSteps raw +
        encodedPrimitiveTimeBound (actionMaximum (R := R)) raw.length + 1)) := by
  simpa only [verifyDelimited, malformed] using ordinary_live initial raw

/-- A polynomial expression that bounds the paid ordinary overhead uniformly. -/
def ordinaryTimeBound (A N : ℕ) : ℕ := N + 3 + encodedPrimitiveTimeBound A N

theorem ordinary_allowance_le (A : ℕ) (raw : Raw) :
    MarkedInput.preludeSteps raw + encodedPrimitiveTimeBound A raw.length + 1 ≤
      ordinaryTimeBound A raw.length := by
  have overhead := FrontEndStreamMachine.preludeSteps_le_length_add_two raw
  unfold ordinaryTimeBound
  omega

/-- Widen only the bound; the actual stored native run is retained. -/
theorem ordinary_uniform (initial : R) (raw : Raw) :
    Nonempty (StateTransition.EvalsToInTime (TM0.step (ordinaryMachine initial))
      (TM0.init (ordinaryInput initial raw))
      (some (ordinaryOutput initial (verifyDelimited raw)))
      (ordinaryTimeBound (actionMaximum (R := R)) raw.length)) := by
  obtain ⟨run⟩ := ordinary_live initial raw
  exact ⟨{ toEvalsTo := run.toEvalsTo
           steps_le_m := run.steps_le_m.trans (ordinary_allowance_le (actionMaximum (R := R)) raw) }⟩

/-- This fixed equality instance and native machine precede the raw input.
The Boolean output embedding is separate from the three input letters. -/
def conventionalMachine (initial : R) [DecidableEq (Alphabet initial)] :
    PrintMove.Machine (Alphabet initial) (PrintMove.Control (Control initial)) :=
  PrintMove.adapter (ordinaryMachine initial) (outputBit initial true)

/-- Direct conventional consumer: no Boolean-input decider record is needed.
The target tape is the complete proved native singleton moved right. -/
theorem conventional_run (initial : R) [DecidableEq (Alphabet initial)] (raw : Raw) :
    ∃ native : StateTransition.EvalsToInTime (TM0.step (ordinaryMachine initial))
        (TM0.init (ordinaryInput initial raw))
        (some (ordinaryOutput initial (verifyDelimited raw)))
        (MarkedInput.preludeSteps raw +
          encodedPrimitiveTimeBound (actionMaximum (R := R)) raw.length + 1),
      ∃ target : StateTransition.EvalsToInTime (PrintMove.step (conventionalMachine initial))
          (PrintMove.init (.normal .start) (ordinaryInput initial raw))
          (some (PrintMove.decidedCfg (verifyDelimited raw)
            (ordinaryOutput initial (verifyDelimited raw)).Tape))
          (2 * (MarkedInput.preludeSteps raw +
            encodedPrimitiveTimeBound (actionMaximum (R := R)) raw.length + 1) + 1),
        target.steps = PrintMove.simulationTime (ordinaryMachine initial)
          (TM0.init (ordinaryInput initial raw)) native.steps + 1 ∧
        target.steps ≤ 2 * native.steps + 1 ∧
        PrintMove.step (conventionalMachine initial)
          (PrintMove.decidedCfg (verifyDelimited raw)
            (ordinaryOutput initial (verifyDelimited raw)).Tape) = none := by
  obtain ⟨native⟩ := ordinary_live initial raw
  have observed : (ordinaryOutput initial (verifyDelimited raw)).Tape.head =
      outputBit initial (verifyDelimited raw) := rfl
  obtain ⟨target, exactTime, bounded, stopped⟩ :=
    PrintMove.decide_of_native_run (ordinaryMachine initial) (outputBit initial)
      (TM0.init (ordinaryInput initial raw)) (ordinaryOutput initial (verifyDelimited raw))
      (verifyDelimited raw)
      (MarkedInput.preludeSteps raw +
        encodedPrimitiveTimeBound (actionMaximum (R := R)) raw.length + 1)
      native (ordinaryOutput_stopped initial (verifyDelimited raw)) observed
  exact ⟨native, target, exactTime, bounded, stopped⟩

end Resources.RotationCertificate.DelimiterPreludeDraft.NativeConsumer148
