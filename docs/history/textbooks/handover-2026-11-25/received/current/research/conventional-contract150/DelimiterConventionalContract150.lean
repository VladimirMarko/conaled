import ConventionalPolynomialDecider150
import DelimiterPolynomial149

set_option autoImplicit false
set_option warningAsError true

/-!
# The literal delimiter checker as a conventional polynomial decider

UNCOMPILED research draft150. All fixed machine and execution data below come
from the already checked delimiter composition. The smaller generic contract
is accompanied by the original full native/conventional Run refinement.
-/

namespace Resources.RotationCertificate.DelimiterPreludeDraft.ConventionalContract150

open Function Turing
open Resources.BinaryCounter (Bits)
open Resources.TuringSimulation
open NativeConsumer148 PolynomialConsumer149
open ConventionalPolynomialDraft150

variable {R : Type} [Fintype R]

/-- This fixed package is constructed from the actual paid run. -/
noncomputable def decider (initial : R) [DecidableEq (Alphabet initial)] :
    PolynomialDecider (Option Bool) verifyDelimited where
  inputFintype := inferInstance
  Alphabet := NativeConsumer148.Alphabet initial
  Control := PrintMove.Control (NativeConsumer148.Control initial)
  alphabetFintype := NativeConsumer148.alphabetFintype initial
  controlFintype := by
    let : Fintype (NativeConsumer148.Control initial) := NativeConsumer148.controlFintype initial
    infer_instance
  blank := default
  start := .normal .start
  accept := .accept
  reject := .reject
  start_ne_accept := PrintMove.normal_ne_accept .start
  start_ne_reject := PrintMove.normal_ne_reject .start
  accept_ne_reject := PrintMove.accept_ne_reject
  letter := inputLetter initial
  letter_ne_blank := input_ne_blank initial
  machine := conventionalMachine initial
  machine_eq_none_iff :=
    PrintMove.adapter_eq_none_iff (ordinaryMachine initial) (outputBit initial true)
  exponent := powerExponent (actionMaximum (R := R))
  run := by
    intro raw
    obtain ⟨_native, target, _exact, _relative, _halted⟩ := run_power initial raw
    refine ⟨PrintMove.decidedCfg (verifyDelimited raw)
      (ordinaryOutput initial (verifyDelimited raw)).Tape, ⟨target⟩, ?_⟩
    cases verifyDelimited raw <;> rfl

/-- The contract fixes exactly the already simulated machine and input letters. -/
theorem machine_and_input (initial : R) [DecidableEq (Alphabet initial)] :
    (decider initial).machine = conventionalMachine initial ∧
    (decider initial).letter = inputLetter initial ∧
    (decider initial).exponent = powerExponent (actionMaximum (R := R)) :=
  ⟨rfl, rfl, rfl⟩

/-- Retain the stronger actual native/target witnesses and complete endpoint
tapes, exact simulation count and relative bound outside the smaller contract. -/
theorem full_run_refinement (initial : R) [DecidableEq (Alphabet initial)] (raw : Raw) :
    Run initial raw (raw.length ^ (decider initial).exponent + (decider initial).exponent) :=
  run_power initial raw

/-- This equality is about the real accepted language, including malformed raw
words. The arbitrary-raw parser converse is reused, not reproved. -/
theorem accepts_iff_checking_relation (initial : R) [DecidableEq (Alphabet initial)] (raw : Raw) :
    (decider initial).Accepts raw ↔
      ∃ input cert : Bits, raw = literalPair input cert ∧ (verifyBitsRun input cert).1 = true :=
  ((decider initial).accepts_iff raw).trans (GeneralProof1.verifyDelimited_accept_iff raw)

/-- The actual conventional language consumes the original pure-power witness
bound. The literal pair length is retained as a distinct paid input observation. -/
theorem binaryYes_iff_small_accepted_pair (initial : R) [DecidableEq (Alphabet initial)]
    (input : Bits) :
    BinaryYes input ↔ ∃ cert : Bits,
      cert.length ≤ input.length ^ 2 ∧
      (literalPair input cert).length ≤ input.length ^ 2 + input.length + 1 ∧
      (decider initial).Accepts (literalPair input cert) := by
  rw [binaryYes_iff_exists_small_delimited_certificate]
  constructor
  · rintro ⟨cert, small, length, accepted⟩
    exact ⟨cert, small, length, ((decider initial).accepts_iff _).2 accepted⟩
  · rintro ⟨cert, small, length, accepted⟩
    exact ⟨cert, small, length, ((decider initial).accepts_iff _).1 accepted⟩

/-- Empty raw input is covered by the uniform run and rejects. -/
theorem empty_rejects (initial : R) [DecidableEq (Alphabet initial)] :
    ¬ (decider initial).Accepts [] := by
  rw [(decider initial).accepts_iff]
  change false ≠ true
  decide

/-- Rejection is universal for missing delimiters, not just a closed fixture. -/
theorem missing_rejects (initial : R) [DecidableEq (Alphabet initial)] (input : Bits) :
    ¬ (decider initial).Accepts (input.map some) := by
  rw [(decider initial).accepts_iff]
  simp [verifyDelimited, GeneralProof1.splitLiteral_missing]

/-- A second delimiter anywhere in the certificate part forces real rejection. -/
theorem repeated_rejects (initial : R) [DecidableEq (Alphabet initial)]
    (input cert : Bits) (tail : Raw) :
    ¬ (decider initial).Accepts (literalPair input cert ++ none :: tail) := by
  rw [(decider initial).accepts_iff]
  simp [verifyDelimited, GeneralProof1.splitLiteral_repeated]

/-- The three source letters remain distinct and none is physical blank. -/
theorem three_nonblank_letters (initial : R) [DecidableEq (Alphabet initial)] :
    (decider initial).letter none ≠ (decider initial).blank ∧
    (decider initial).letter (some false) ≠ (decider initial).blank ∧
    (decider initial).letter (some true) ≠ (decider initial).blank ∧
    (decider initial).letter none ≠ (decider initial).letter (some false) ∧
    (decider initial).letter none ≠ (decider initial).letter (some true) ∧
    (decider initial).letter (some false) ≠ (decider initial).letter (some true) := by
  refine ⟨(decider initial).letter_ne_blank _, (decider initial).letter_ne_blank _,
    (decider initial).letter_ne_blank _, ?_, ?_, ?_⟩
  · intro same
    have impossible := (decider initial).letter.injective same
    cases impossible
  · intro same
    have impossible := (decider initial).letter.injective same
    cases impossible
  · intro same
    have impossible := Option.some.inj ((decider initial).letter.injective same)
    cases impossible

/-- A closed fixed finite machine exists: choose a one-element register carrier
and its equality once, before the raw input. This is not a table export. -/
noncomputable def unitDecider : PolynomialDecider (Option Bool) verifyDelimited := by
  classical
  exact decider ()

theorem unit_language (raw : Raw) :
    unitDecider.Accepts raw ↔
      ∃ input cert : Bits, raw = literalPair input cert ∧ (verifyBitsRun input cert).1 = true := by
  classical
  exact accepts_iff_checking_relation () raw

end Resources.RotationCertificate.DelimiterPreludeDraft.ConventionalContract150
