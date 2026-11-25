import ConventionalVerifierCriterion150
import DelimiterConventionalContract150
import Applications.Resources.RotationCertificate.CertificateCorrespondence

set_option autoImplicit false
set_option warningAsError true

/-!
# BinaryYes satisfies the explicit conventional verifier criterion

UNCOMPILED research draft150, depending on the frozen uncompiled conventional
contract150. The actual fixed delimiter decider and the existing small
certificate theorem supply the criterion. Its two exponents remain distinct:
machine time uses total pair length; the witness exponent is exactly two.

No independently defined NTM/NP equivalence or obligation qualification follows
from naming this selected verifier characterization.
-/

namespace Resources.RotationCertificate.ConventionalVerifierCriterion150

open Resources.BinaryCounter (Bits)
open Resources.TuringSimulation
open ConventionalVerifierDraft150 (PolynomialCheckingRelation ConventionalVerifierCriterion)
open DelimiterPreludeDraft
open DelimiterPreludeDraft.ConventionalContract150
open CertificateCorrespondence

/-- The existing total Boolean checker defines the binary checking relation. -/
def CheckingRelation (input cert : Bits) : Prop := (verifyBitsRun input cert).1 = true

theorem literalPair_agrees (input cert : Bits) :
    ConventionalVerifierDraft150.literalPair input cert =
      DelimiterPreludeDraft.literalPair input cert := rfl

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
      (ConventionalVerifierDraft150.literalPair input cert).length ≤
        input.length ^ 2 + input.length + 1 ∧
      checking.decider.Accepts (ConventionalVerifierDraft150.literalPair input cert) :=
  binaryYesCriterion.accepted_small_pair_iff input

/-- This application has the stronger unbounded-witness soundness theorem.
The generic criterion itself requires its witness bound in both directions. -/
theorem accepted_pair_sound (input cert : Bits)
    (accepted : checking.decider.Accepts (ConventionalVerifierDraft150.literalPair input cert)) :
    BinaryYes input :=
  verifyBitsRun_sound input cert ((checking.accepts_pair_iff input cert).1 accepted)

/-- Retain the full existing native/target refinement for every raw word. The
fixed classical alphabet equality is supplied before the input quantifier. -/
theorem full_run_refinement :
    letI : DecidableEq (NativeConsumer148.Alphabet ()) := Classical.decEq _
    ∀ raw : Raw, PolynomialConsumer149.Run () raw
      (raw.length ^ checking.decider.exponent + checking.decider.exponent) := by
  classical
  intro raw
  exact DelimiterPreludeDraft.ConventionalContract150.full_run_refinement () raw

/-- Zero raw length forces an empty certificate for the concrete exponent two.
No analogous universal assertion is made for the generic exponent zero. -/
theorem empty_certificate_bound (cert : Bits) :
    cert.length ≤ ([] : Bits).length ^ binaryYesCriterion.witnessExponent ↔ cert = [] := by
  change cert.length ≤ 0 ^ 2 ↔ cert = []
  simp

/-- An empty pair is a one-letter raw word, distinct from raw empty input. -/
theorem empty_pair_literal :
    ConventionalVerifierDraft150.literalPair [] [] = [none] ∧
      (ConventionalVerifierDraft150.literalPair [] []).length = 1 ∧
      ConventionalVerifierDraft150.literalPair [] [] ≠ [] :=
  ⟨rfl, rfl, ConventionalVerifierDraft150.literalPair_ne_nil [] []⟩

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
        (ConventionalVerifierDraft150.literalPair
          (wordBits (inputCode s.val t.val [])) cert).length ≤ 421 ∧
        checking.decider.Accepts (ConventionalVerifierDraft150.literalPair
          (wordBits (inputCode s.val t.val [])) cert) := by
  have inputLength : (wordBits (inputCode s.val t.val [])).length = 20 := by
    simpa using encoded_instance_length s t []
  obtain ⟨cert, small, pairLength, accepted⟩ :=
    (binaryYes_iff_small_accepted_pair _).1 (binaryYes_empty_shapes s t [])
  refine ⟨inputLength, cert, ?_, ?_, accepted⟩
  · simpa [inputLength] using small
  · simpa [inputLength] using pairLength

end Resources.RotationCertificate.ConventionalVerifierCriterion150
