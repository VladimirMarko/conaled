import Applications.Resources.RotationCertificate.CertificateCorrespondence
import Examples.RotationDistance

/-!
# Connected literal certificate correspondence cases

Retain zero-size boundaries, explicit high zero threshold bits, exact instance and certificate sizes, and the existing independent rotation-distance fixtures.
-/

set_option autoImplicit false
set_option warningAsError true


namespace Examples.RotationCertificateCorrespondence

open Resources.BinaryCounter (Bits value)
open Resources.RotationCertificate
open Resources.RotationCertificate.BitPairFraming
open Resources.RotationCertificate.CertificateCorrespondence
open Trees.Rotations (Shape applyMoves?)
open RotationDistanceExample (empty singleton leftTwo rightTwo rootRight)

private theorem empty_trace_accepts {n : Nat} (shape : Shape n) (bs : Bits) :
    verifyFramed (frame (wordBits (inputCode shape.val shape.val bs)) []) = true := by
  apply (verifyFramed_code_iff_trace shape.val shape.val bs []).2
  exact ⟨[], rfl, Trees.Rotations.applyMoves?_nil shape.val, Nat.zero_le _⟩

private theorem root_right_accepts (bs : Bits) (positive : 1 ≤ value bs) :
    verifyFramed (frame (wordBits (inputCode leftTwo.val rightTwo.val bs))
      (wordBits (certCode [rootRight]))) = true := by
  apply (verifyFramed_code_iff_trace leftTwo.val rightTwo.val bs _).2
  exact ⟨[rootRight], rfl, RotationDistanceExample.one_right_rotation, positive⟩

private theorem rejects_of_not_binaryYes (input : Bits) (rejected : ¬ BinaryYes input)
    (cert : Bits) : verifyFramed (frame input cert) = false := by
  cases returned : verifyFramed (frame input cert) with
  | false => rfl
  | true =>
      exact False.elim (rejected
        ((binaryYes_iff_exists_framed_certificate input).2 ⟨cert, returned⟩))

/-- Empty shapes, literal zero-width threshold and literal empty certificate. -/
theorem empty_zero_width_case :
    (wordBits (inputCode empty.val empty.val [])).length = 20 ∧
      ([] : Bits).length = 0 ∧
      (frame (wordBits (inputCode empty.val empty.val [])) []).length = 41 ∧
      verifyFramed (frame (wordBits (inputCode empty.val empty.val [])) []) = true := by
  have inputLength : (wordBits (inputCode empty.val empty.val [])).length = 20 :=
    (encoded_instance_length empty empty []).trans rfl
  refine ⟨inputLength, rfl, ?_, empty_trace_accepts empty []⟩
  rw [frame_length, inputLength]
  rfl

/-- The two high zero bits remain in the input while the empty trace accepts. -/
theorem empty_width_two_case :
    value [false, false] = 0 ∧
      (wordBits (inputCode empty.val empty.val [false, false])).length = 28 ∧
      ([] : Bits).length = 0 ∧
      (frame (wordBits (inputCode empty.val empty.val [false, false])) []).length = 57 ∧
      verifyFramed
        (frame (wordBits (inputCode empty.val empty.val [false, false])) []) = true := by
  have inputLength :
      (wordBits (inputCode empty.val empty.val [false, false])).length = 28 :=
    (encoded_instance_length empty empty [false, false]).trans rfl
  refine ⟨rfl, inputLength, rfl, ?_, empty_trace_accepts empty [false, false]⟩
  rw [frame_length, inputLength]
  rfl

/-- The concrete nonzero distance excludes every certificate at zero threshold. -/
theorem two_node_zero_threshold_not_in_language :
    ¬ BinaryYes (wordBits (inputCode leftTwo.val rightTwo.val [])) := by
  intro yes
  have bound := (binaryYes_code_iff leftTwo rightTwo []).1 yes
  rw [RotationDistanceExample.two_node_distance] at bound
  change 1 ≤ 0 at bound
  omega

theorem two_node_zero_threshold_rejects_every_certificate (cert : Bits) :
    verifyFramed (frame (wordBits (inputCode leftTwo.val rightTwo.val [])) cert) = false :=
  rejects_of_not_binaryYes _ two_node_zero_threshold_not_in_language cert

/-- The fixed root-rotation certificate has eight bits and is rejected here. -/
theorem two_node_zero_threshold_case :
    (wordBits (inputCode leftTwo.val rightTwo.val [])).length = 52 ∧
      (wordBits (certCode [rootRight])).length = 8 ∧
      (frame (wordBits (inputCode leftTwo.val rightTwo.val []))
        (wordBits (certCode [rootRight]))).length = 113 ∧
      verifyFramed (frame (wordBits (inputCode leftTwo.val rightTwo.val []))
        (wordBits (certCode [rootRight]))) = false := by
  have inputLength : (wordBits (inputCode leftTwo.val rightTwo.val [])).length = 52 :=
    (encoded_instance_length leftTwo rightTwo []).trans rfl
  have certLength : (wordBits (certCode [rootRight])).length = 8 :=
    (wordBits_length (certCode [rootRight])).trans rfl
  refine ⟨inputLength, certLength, ?_, two_node_zero_threshold_rejects_every_certificate _⟩
  rw [frame_length, inputLength, certLength]

/-- One represented unit of fuel admits exactly the existing legal root move. -/
theorem one_rotation_case :
    (wordBits (inputCode leftTwo.val rightTwo.val [true])).length = 56 ∧
      (wordBits (certCode [rootRight])).length = 8 ∧
      (frame (wordBits (inputCode leftTwo.val rightTwo.val [true]))
        (wordBits (certCode [rootRight]))).length = 121 ∧
      verifyFramed (frame (wordBits (inputCode leftTwo.val rightTwo.val [true]))
        (wordBits (certCode [rootRight]))) = true := by
  have inputLength : (wordBits (inputCode leftTwo.val rightTwo.val [true])).length = 56 :=
    (encoded_instance_length leftTwo rightTwo [true]).trans rfl
  have certLength : (wordBits (certCode [rootRight])).length = 8 :=
    (wordBits_length (certCode [rootRight])).trans rfl
  refine ⟨inputLength, certLength, ?_, root_right_accepts [true] (by decide)⟩
  rw [frame_length, inputLength, certLength]

/-- A redundant high zero preserves the value and increases the literal input. -/
theorem one_rotation_high_zero_case :
    value [true, false] = 1 ∧
      (wordBits (inputCode leftTwo.val rightTwo.val [true, false])).length = 60 ∧
      (wordBits (certCode [rootRight])).length = 8 ∧
      (frame (wordBits (inputCode leftTwo.val rightTwo.val [true, false]))
        (wordBits (certCode [rootRight]))).length = 129 ∧
      verifyFramed (frame (wordBits (inputCode leftTwo.val rightTwo.val [true, false]))
        (wordBits (certCode [rootRight]))) = true := by
  have inputLength :
      (wordBits (inputCode leftTwo.val rightTwo.val [true, false])).length = 60 :=
    (encoded_instance_length leftTwo rightTwo [true, false]).trans rfl
  have certLength : (wordBits (certCode [rootRight])).length = 8 :=
    (wordBits_length (certCode [rootRight])).trans rfl
  refine ⟨rfl, inputLength, certLength, ?_, root_right_accepts [true, false] (by decide)⟩
  rw [frame_length, inputLength, certLength]

theorem high_zero_does_not_identify_the_two_instances :
    value [true] = value [true, false] ∧
      wordBits (inputCode leftTwo.val rightTwo.val [true]) ≠
        wordBits (inputCode leftTwo.val rightTwo.val [true, false]) := by
  refine ⟨rfl, ?_⟩
  intro same
  have sameLength := congrArg List.length same
  rw [one_rotation_case.1, one_rotation_high_zero_case.2.1] at sameLength
  omega

/-- Empty raw syntax is distinct from the encoded pair of two empty trees. -/
theorem raw_empty_instance_case (cert : Bits) :
    ([] : Bits).length = 0 ∧ ¬ BinaryYes [] ∧
      verifyFramed (frame [] cert) = false :=
  ⟨rfl, not_binaryYes_nil, rejects_of_not_binaryYes [] not_binaryYes_nil cert⟩

/-- These consumers retain all threshold lists at both zero-distance boundaries. -/
theorem zero_and_one_node_language_boundaries (bs : Bits) :
    BinaryYes (wordBits (inputCode empty.val empty.val bs)) ∧
      BinaryYes (wordBits (inputCode singleton.val singleton.val bs)) :=
  ⟨binaryYes_empty_shapes empty empty bs,
    binaryYes_singleton_shapes singleton singleton bs⟩

theorem arbitrary_zero_node_boundary (s t : Shape 0) (bs : Bits) :
    BinaryYes (wordBits (inputCode s.val t.val bs)) :=
  binaryYes_empty_shapes s t bs

theorem arbitrary_one_node_boundary (s t : Shape 1) (bs : Bits) :
    BinaryYes (wordBits (inputCode s.val t.val bs)) :=
  binaryYes_singleton_shapes s t bs

/-- The bounded-certificate theorem is exercised on the nonzero distance case. -/
theorem one_rotation_has_a_small_accepted_witness :
    ∃ cert : Bits, cert.length ≤ 3136 ∧
      (frame (wordBits (inputCode leftTwo.val rightTwo.val [true])) cert).length ≤ 3249 ∧
      verifyFramed (frame (wordBits (inputCode leftTwo.val rightTwo.val [true])) cert) = true := by
  have bound : Shape.distance leftTwo rightTwo ≤ value [true] := by
    rw [RotationDistanceExample.two_node_distance]
    decide
  have witness :=
    (distance_le_iff_exists_small_framed_certificate leftTwo rightTwo [true]).1 bound
  simpa only [one_rotation_case.1, show (56 : Nat) ^ 2 = 3136 by decide,
    show ((56 : Nat) + 1) ^ 2 = 3249 by decide] using witness

/-- The reverse bounded-certificate implication cannot admit a no instance. -/
theorem zero_threshold_has_no_small_accepted_witness :
    ¬ ∃ cert : Bits,
      cert.length ≤ (wordBits (inputCode leftTwo.val rightTwo.val [])).length ^ 2 ∧
      (frame (wordBits (inputCode leftTwo.val rightTwo.val [])) cert).length ≤
        ((wordBits (inputCode leftTwo.val rightTwo.val [])).length + 1) ^ 2 ∧
      verifyFramed (frame (wordBits (inputCode leftTwo.val rightTwo.val [])) cert) = true := by
  intro witnessed
  exact two_node_zero_threshold_not_in_language
    ((binaryYes_iff_exists_small_framed_certificate _).2 witnessed)

end Examples.RotationCertificateCorrespondence
