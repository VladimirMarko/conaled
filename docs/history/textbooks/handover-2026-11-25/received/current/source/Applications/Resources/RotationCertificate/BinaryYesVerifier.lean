import Applications.Resources.TuringSimulation.ConventionalPolynomialDecider
import Applications.Resources.RotationCertificate.DelimiterPolynomialTime
import Applications.Resources.TuringSimulation.ConventionalVerifier
import Applications.Resources.RotationCertificate.CertificateCorrespondence

set_option autoImplicit false
set_option warningAsError true

/-!
# Conventional verification of binary rotation instances

The delimiter decider retains the complete execution refinement. Its
fixed checking language yields the explicit BinaryYes criterion with
quadratic certificates and a separate paid literal-pair length bound.
-/

/- Complete preserved component: delimiter_conventional. -/
section

namespace Resources.RotationCertificate.DelimiterMachine.Conventional

open Function Turing
open Resources.BinaryCounter (Bits)
open Resources.TuringSimulation
open Native _root_.Resources.RotationCertificate.DelimiterMachine.PolynomialTime
open ConventionalPolynomial

variable {R : Type} [Fintype R]

/-- This fixed package is constructed from the actual paid run. -/
noncomputable def decider (initial : R) [DecidableEq (Alphabet initial)] :
    PolynomialDecider (Option Bool) verifyDelimited where
  inputFintype := inferInstance
  Alphabet := Native.Alphabet initial
  Control := PrintMove.Control (Native.Control initial)
  alphabetFintype := Native.alphabetFintype initial
  controlFintype := by
    let : Fintype (Native.Control initial) := Native.controlFintype initial
    infer_instance
  blank := default
  start := .normal .start
  accept := .accept
  reject := .reject
  start_ne_accept := PrintMove.normal_ne_accept (.start : Native.Control initial)
  start_ne_reject := PrintMove.normal_ne_reject (.start : Native.Control initial)
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
  ((decider initial).accepts_iff raw).trans (Execution.verifyDelimited_accept_iff raw)

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
  simp [verifyDelimited, Execution.splitLiteral_missing]

/-- A second delimiter anywhere in the certificate part forces real rejection. -/
theorem repeated_rejects (initial : R) [DecidableEq (Alphabet initial)]
    (input cert : Bits) (tail : Raw) :
    ¬ (decider initial).Accepts (literalPair input cert ++ none :: tail) := by
  rw [(decider initial).accepts_iff]
  simp [verifyDelimited, Execution.splitLiteral_repeated]

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

end Resources.RotationCertificate.DelimiterMachine.Conventional

end

/- Complete preserved component: binary_yes_criterion. -/
section

namespace Resources.RotationCertificate.BinaryYesVerifier

open Resources.BinaryCounter (Bits)
open Resources.TuringSimulation
open ConventionalVerifier (PolynomialCheckingRelation ConventionalVerifierCriterion)
open DelimiterMachine
open DelimiterMachine.Conventional
open CertificateCorrespondence

/-- The existing total Boolean checker defines the binary checking relation. -/
def CheckingRelation (input cert : Bits) : Prop := (verifyBitsRun input cert).1 = true

theorem literalPair_agrees (input cert : Bits) :
    ConventionalVerifier.literalPair input cert =
      DelimiterMachine.literalPair input cert := rfl

/-- Every field uses the one fixed already constructed delimiter machine. -/
noncomputable def checking : PolynomialCheckingRelation CheckingRelation where
  answer := verifyDelimited
  decider := unitDecider
  language := by
    intro raw
    exact unit_language raw

/-- The exact criterion is inhabited by the current machine and the existing
quadratic certificate completeness/raw soundness proofs. -/
noncomputable def binaryYesCriterion : ConventionalVerifierCriterion BinaryYes where
  relation := CheckingRelation
  checking := checking
  witnessExponent := 2
  witness_iff := by
    intro input
    constructor
    · exact verifyBitsRun_complete_small input
    · rintro ⟨cert, _small, accepted⟩
      exact verifyBitsRun_sound input cert accepted

theorem binaryYes_has_conventional_verifier :
    Nonempty (ConventionalVerifierCriterion BinaryYes) := ⟨binaryYesCriterion⟩

theorem fixed_machine_and_witness_exponent :
    binaryYesCriterion.checking.decider = unitDecider ∧
      binaryYesCriterion.witnessExponent = 2 := ⟨rfl, rfl⟩

/-- Actual acceptance and both original size observations survive the generic
criterion interface, without an additive constant on certificate length. -/
theorem binaryYes_iff_small_accepted_pair (input : Bits) :
    BinaryYes input ↔ ∃ cert : Bits,
      cert.length ≤ input.length ^ 2 ∧
      (ConventionalVerifier.literalPair input cert).length ≤
        input.length ^ 2 + input.length + 1 ∧
      checking.decider.Accepts (ConventionalVerifier.literalPair input cert) :=
  binaryYesCriterion.accepted_small_pair_iff input

/-- This application has the stronger unbounded-witness soundness theorem.
The generic criterion itself requires its witness bound in both directions. -/
theorem accepted_pair_sound (input cert : Bits)
    (accepted : checking.decider.Accepts (ConventionalVerifier.literalPair input cert)) :
    BinaryYes input :=
  verifyBitsRun_sound input cert ((checking.accepts_pair_iff input cert).1 accepted)

/-- Retain the full existing native/target refinement for every raw word. The
fixed classical alphabet equality is supplied before the input quantifier. -/
theorem full_run_refinement :
    letI : DecidableEq (Native.Alphabet ()) := Classical.decEq _
    ∀ raw : Raw, PolynomialTime.Run () raw
      (raw.length ^ checking.decider.exponent + checking.decider.exponent) := by
  classical
  intro raw
  exact DelimiterMachine.Conventional.full_run_refinement () raw

/-- Zero raw length forces an empty certificate for the concrete exponent two.
No analogous universal assertion is made for the generic exponent zero. -/
theorem empty_certificate_bound (cert : Bits) :
    cert.length ≤ ([] : Bits).length ^ binaryYesCriterion.witnessExponent ↔ cert = [] := by
  change cert.length ≤ 0 ^ 2 ↔ cert = []
  simp

/-- An empty pair is a one-letter raw word, distinct from raw empty input. -/
theorem empty_pair_literal :
    ConventionalVerifier.literalPair [] [] = [none] ∧
      (ConventionalVerifier.literalPair [] []).length = 1 ∧
      ConventionalVerifier.literalPair [] [] ≠ [] :=
  ⟨rfl, rfl, ConventionalVerifier.literalPair_ne_nil [] []⟩

theorem empty_raw_rejects : ¬ checking.decider.Accepts [] := checking.empty_raw_rejects

/-- The syntactically valid empty pair rejects because its empty instance is
outside BinaryYes, not because the delimiter word is absent. -/
theorem empty_pair_rejects : ¬ checking.decider.Accepts [none] := by
  intro accepted
  exact not_binaryYes_nil (accepted_pair_sound [] [] accepted)

/-- Zero-node shapes are encoded by a nonempty twenty-bit instance. The actual
criterion supplies a small accepted witness on its paid literal pair. -/
theorem zero_node_zero_width (s t : Trees.Rotations.Shape 0) :
    (wordBits (inputCode s.val t.val [])).length = 20 ∧
      ∃ cert : Bits, cert.length ≤ 400 ∧
        (ConventionalVerifier.literalPair
          (wordBits (inputCode s.val t.val [])) cert).length ≤ 421 ∧
        checking.decider.Accepts (ConventionalVerifier.literalPair
          (wordBits (inputCode s.val t.val [])) cert) := by
  have inputLength : (wordBits (inputCode s.val t.val [])).length = 20 := by
    simpa using encoded_instance_length s t []
  obtain ⟨cert, small, pairLength, accepted⟩ :=
    (binaryYes_iff_small_accepted_pair _).1 (binaryYes_empty_shapes s t [])
  refine ⟨inputLength, cert, ?_, ?_, accepted⟩
  · simpa [inputLength] using small
  · simpa [inputLength] using pairLength

end Resources.RotationCertificate.BinaryYesVerifier

end
