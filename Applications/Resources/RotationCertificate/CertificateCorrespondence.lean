import Applications.Resources.RotationCertificate.BitPairFraming

/-!
# Literal rotation-distance instances and small checked certificates

Expose the exact original shape-distance decision, literal threshold width, instance size, legal rotation traces and polynomially bounded certificates for the existing Boolean checker.
-/

set_option autoImplicit false
set_option warningAsError true


namespace Resources.RotationCertificate.CertificateCorrespondence

open Resources.BinaryCounter (Bits value)
open Trees.Rotations (Shape RotationMove applyMoves?)
open BitPairFraming

/-- Unfolding the independent binary language retains the exact source
shapes and the supplied binary threshold list. -/
theorem binaryYes_iff_encoded_distance (input : Bits) :
    BinaryYes input ↔
      ∃ (n : Nat) (s t : Shape n) (bs : Bits),
        input = wordBits (inputCode s.val t.val bs) ∧
          Shape.distance s t ≤ value bs := by
  constructor
  · rintro ⟨word, encoded, n, s, t, bs, wordEq, bound⟩
    exact ⟨n, s, t, bs, wordEq ▸ encoded, bound⟩
  · rintro ⟨n, s, t, bs, encoded, bound⟩
    exact ⟨inputCode s.val t.val bs, encoded, ⟨n, s, t, bs, rfl, bound⟩⟩

/-- The represented decision on supplied shapes uses their actual distance
and the literal threshold. The converse identifies the parsed fields through
the proved complete-code injectivity; it does not select another instance. -/
theorem binaryYes_code_iff {n : Nat} (s t : Shape n) (bs : Bits) :
    BinaryYes (wordBits (inputCode s.val t.val bs)) ↔
      Shape.distance s t ≤ value bs := by
  constructor
  · rintro ⟨word, encoded, yes⟩
    have wordEq : inputCode s.val t.val bs = word := wordBits_injective encoded
    rw [← wordEq] at yes
    obtain ⟨source, target, fuel, moves, inputEq, run, bound⟩ :=
      (yes_iff_trace (inputCode s.val t.val bs)).1 yes
    obtain ⟨sourceEq, targetEq, fuelEq⟩ :=
      inputCode_injective s.val t.val bs source target fuel inputEq
    rw [← sourceEq, ← targetEq] at run
    rw [← fuelEq] at bound
    exact (Shape.distance_le_length s t run).trans bound
  · intro bound
    exact ⟨inputCode s.val t.val bs, rfl, ⟨n, s, t, bs, rfl, bound⟩⟩

/-- Exact instance size, including all redundant high zero threshold bits. -/
theorem encoded_instance_length {n : Nat} (s t : Shape n) (bs : Bits) :
    (wordBits (inputCode s.val t.val bs)).length = 16 * n + 4 * bs.length + 20 := by
  rw [wordBits_length, inputCode_length, s.property, t.property]
  omega

/-- The actual framed Boolean checker recognizes exactly legal trace codes
for the fixed input fields, with no equal-size, syntax or positivity premise. -/
theorem verifyFramed_code_iff_trace (source target : BinaryTree Unit)
    (bs cert : Bits) :
    verifyFramed (frame (wordBits (inputCode source target bs)) cert) = true ↔
      ∃ moves : List RotationMove, cert = wordBits (certCode moves) ∧
        applyMoves? moves source = some target ∧ moves.length ≤ value bs := by
  rw [verifyFramed_frame]
  constructor
  · intro accepted
    obtain ⟨otherSource, otherTarget, fuel, moves, inputEq, certEq, run, bound⟩ :=
      (verifyBitsRun_accept_iff_trace _ cert).1 accepted
    obtain ⟨sourceEq, targetEq, fuelEq⟩ := inputCode_injective
      source target bs otherSource otherTarget fuel (wordBits_injective inputEq)
    rw [← sourceEq, ← targetEq] at run
    rw [← fuelEq] at bound
    exact ⟨moves, certEq, run, bound⟩
  · rintro ⟨moves, encoded, run, bound⟩
    exact (verifyBitsRun_accept_iff_trace _ cert).2
      ⟨source, target, bs, moves, rfl, encoded, run, bound⟩

/-- The existing small-certificate completeness and raw soundness combine
into a two-way relation on arbitrary bit instances. -/
theorem binaryYes_iff_exists_small_framed_certificate (input : Bits) :
    BinaryYes input ↔
      ∃ cert : Bits, cert.length ≤ input.length ^ 2 ∧
        (frame input cert).length ≤ (input.length + 1) ^ 2 ∧
        verifyFramed (frame input cert) = true := by
  constructor
  · exact verifyFramed_complete_small input
  · rintro ⟨cert, _, _, accepted⟩
    exact (binaryYes_iff_exists_framed_certificate input).2 ⟨cert, accepted⟩

/-- Both directions connect the original shape-distance decision to the
actual Boolean relation with the same polynomial witness bound. -/
theorem distance_le_iff_exists_small_framed_certificate {n : Nat}
    (s t : Shape n) (bs : Bits) :
    Shape.distance s t ≤ value bs ↔
      ∃ cert : Bits,
        cert.length ≤ (wordBits (inputCode s.val t.val bs)).length ^ 2 ∧
        (frame (wordBits (inputCode s.val t.val bs)) cert).length ≤
          ((wordBits (inputCode s.val t.val bs)).length + 1) ^ 2 ∧
        verifyFramed (frame (wordBits (inputCode s.val t.val bs)) cert) = true := by
  exact (binaryYes_code_iff s t bs).symm.trans
    (binaryYes_iff_exists_small_framed_certificate _)

/-- The empty raw instance is not a well-formed distance instance. -/
theorem not_binaryYes_nil : ¬ BinaryYes [] := by
  intro yes
  obtain ⟨n, s, t, bs, encoded, _⟩ := (binaryYes_iff_encoded_distance []).1 yes
  have size := congrArg List.length encoded
  rw [List.length_nil, encoded_instance_length] at size
  omega

/-- The zero-node boundary uses the proved elementary distance theorem. -/
theorem binaryYes_empty_shapes (s t : Shape 0) (bs : Bits) :
    BinaryYes (wordBits (inputCode s.val t.val bs)) := by
  apply (binaryYes_code_iff s t bs).2
  rw [Shape.distance_empty]
  exact Nat.zero_le _

/-- The one-node boundary has the same zero-distance consequence. -/
theorem binaryYes_singleton_shapes (s t : Shape 1) (bs : Bits) :
    BinaryYes (wordBits (inputCode s.val t.val bs)) := by
  apply (binaryYes_code_iff s t bs).2
  rw [Shape.distance_singleton]
  exact Nat.zero_le _

end Resources.RotationCertificate.CertificateCorrespondence
