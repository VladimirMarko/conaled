import Applications.Resources.RotationCertificate.BinaryVerifier
import Examples.RotationCertificateParsing
import Examples.RotationCertificateVerification

/-!
# Connected fixed-bit rotation certificates

Independent finite-block cases retain endian order, fixed zero blocks, reserved
tags and incomplete endings. Actual complete decoding, syntax parsing and
streaming have distinct failure stages. Their source observation need not grow
when malformed bits are appended. Packed emitter outputs feed the actual binary
verifier; the small-witness and all-raw work clients retain their separate scopes.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RotationCertificateBinary
open Trees Trees.Rotations Resources
open Resources.BinaryCounter (Bits value)
open Resources.RotationCertificate
open RotationDistanceExample (empty leftTwo rightTwo rootRight)

/-! Representative literal blocks fix traversal order and preserve the supplied suffix. -/

theorem literal_tag_packing (suffix : Bits) :
    packTagRun emptyTag suffix = (false :: false :: false :: false :: suffix, 5) ∧
      packTagRun nodeTag suffix = (true :: false :: false :: false :: suffix, 5) ∧
      packTagRun pathLeftTag suffix = (false :: false :: false :: true :: suffix, 5) ∧
      packTagRun endMoveTag suffix = (false :: true :: false :: true :: suffix, 5) ∧
      packTagRun (15 : Tag) suffix = (true :: true :: true :: true :: suffix, 5) :=
  ⟨(packTagRun_eq emptyTag suffix).trans rfl,
    (packTagRun_eq nodeTag suffix).trans rfl,
    (packTagRun_eq pathLeftTag suffix).trans rfl,
    (packTagRun_eq endMoveTag suffix).trans rfl,
    (packTagRun_eq (15 : Tag) suffix).trans rfl⟩

theorem every_four_bit_block_recovers_its_order (b0 b1 b2 b3 : Bool) :
    tagBits (decodeTagRun b0 b1 b2 b3).1 = [b0, b1, b2, b3] ∧
      (decodeTagRun b0 b1 b2 b3).2 = 1 :=
  ⟨tagBits_decodeTagRun b0 b1 b2 b3, decodeTagRun_cost b0 b1 b2 b3⟩

theorem literal_root_certificate_packing (suffix : Bits) :
    packWordRun (certCode [rootRight]) suffix =
      (true :: true :: true :: false :: false :: true :: false :: true :: suffix, 13) :=
  (packWordRun_eq (certCode [rootRight]) suffix).trans rfl

theorem arbitrary_packing_preserves_the_suffix (word : Word) (suffix : Bits) :
    (packWordRun word suffix).1 = wordBits word ++ suffix ∧
      (packWordRun word suffix).2 = 6 * word.length + 1 ∧
      (packWordRun word suffix).1.length = 4 * word.length + suffix.length := by
  refine ⟨packWordRun_value word suffix, packWordRun_cost word suffix, ?_⟩
  rw [packWordRun_value, List.length_append, wordBits_length]

theorem actual_pack_unpack_cost (word : Word) :
    Resources.bind (packWordRun word []) unpackWordRun =
      (some word, 10 * word.length + 3) :=
  pack_unpack_eq word

theorem actual_decoding_preserves_every_original_bit (raw : Bits) (word : Word)
    (returned : (unpackWordRun raw).1 = some word) :
    packWordRun word [] = (raw, 6 * word.length + 1) :=
  packWordRun_of_unpacked raw word returned

theorem arbitrary_prefix_preserves_a_failed_suffix
    (pref : Word) (raw : Bits) (cost : Nat)
    (failed : unpackWordRun raw = (none, cost)) :
    unpackWordRun (wordBits pref ++ raw) = (none, cost + 2 * pref.length) := by
  rw [unpackWordRun_prefix, failed]

theorem every_partial_ending_fails (pref : Word) (a b c : Bool) :
    unpackWordRun (wordBits pref ++ [a]) = (none, 2 * pref.length + 2) ∧
      unpackWordRun (wordBits pref ++ [a, b]) = (none, 2 * pref.length + 2) ∧
      unpackWordRun (wordBits pref ++ [a, b, c]) = (none, 2 * pref.length + 2) :=
  ⟨unpackWordRun_partial pref [a] (by simp) (by simp),
    unpackWordRun_partial pref [a, b] (by simp) (by simp),
    unpackWordRun_partial pref [a, b, c] (by simp) (by simp)⟩

theorem arbitrary_raw_decode_contract (raw : Bits) (word : Word) :
    ((unpackWordRun raw).1 = some word ↔ raw = wordBits word) ∧
      ((unpackWordRun raw).1 = none ↔ raw.length % 4 ≠ 0) ∧
      (unpackWordRun raw).2 ≤ raw.length + 2 :=
  ⟨unpackWordRun_iff raw word, unpackWordRun_none_iff raw, unpackWordRun_cost_le raw⟩

/-! Word framing is strictly finer than the numeric value of the whole bit list. -/

theorem zero_blocks_cannot_be_normalized_away :
    value (wordBits []) = value (wordBits [emptyTag]) ∧
      wordBits [] ≠ wordBits [emptyTag] ∧
      unpackWordRun (wordBits []) = (some [], 2) ∧
      unpackWordRun (wordBits [emptyTag]) = (some [emptyTag], 6) :=
  ⟨rfl, by decide, unpackWordRun_code [], unpackWordRun_code [emptyTag]⟩

theorem high_zero_blocks_retain_a_distinct_word :
    value (wordBits [nodeTag]) = value (wordBits [nodeTag, emptyTag]) ∧
      wordBits [nodeTag] ≠ wordBits [nodeTag, emptyTag] ∧
      unpackWordRun (wordBits [nodeTag]) = (some [nodeTag], 6) ∧
      unpackWordRun (wordBits [nodeTag, emptyTag]) = (some [nodeTag, emptyTag], 10) :=
  ⟨rfl, by decide, unpackWordRun_code [nodeTag], unpackWordRun_code [nodeTag, emptyTag]⟩

theorem reserved_blocks_decode_before_syntax_rejects
    (tag : Tag) (reserved : 11 ≤ tag.val) (cert : Bits) :
    unpackWordRun (wordBits [tag]) = (some [tag], 6) ∧
      verifyBitsRun (wordBits [tag]) cert = (false, 12) := by
  have parser :=
    Examples.RotationCertificateParsing.every_reserved_tag_rejects_at_input_start
      tag reserved []
  refine ⟨unpackWordRun_code [tag], ?_⟩
  have observed := verifyBitsRun_parse_none (wordBits [tag]) cert [tag]
    (congrArg Prod.fst (unpackWordRun_code [tag])) (congrArg Prod.fst parser)
  rw [unpackWordRun_code, parser] at observed
  exact observed

/-! The accepted one-rotation pair contains 56 input bits and 8 certificate bits. -/

theorem one_rotation_bit_lengths :
    (wordBits (inputCode leftTwo.val rightTwo.val [true])).length = 56 ∧
      (wordBits (certCode [rootRight])).length = 8 ∧
      (wordBits (inputCode leftTwo.val rightTwo.val [true])).length +
        (wordBits (certCode [rootRight])).length = 64 := by
  have inputLength : (wordBits (inputCode leftTwo.val rightTwo.val [true])).length = 56 :=
    (wordBits_length (inputCode leftTwo.val rightTwo.val [true])).trans rfl
  have certLength : (wordBits (certCode [rootRight])).length = 8 :=
    (wordBits_length (certCode [rootRight])).trans rfl
  refine ⟨inputLength, certLength, ?_⟩
  omega

theorem packed_empty_equal_input :
    verifyBitsRun (wordBits (inputCode empty.val empty.val [])) [] = (true, 43) := by
  have parsed := congrArg Prod.fst (parseInputRun_code empty.val empty.val [])
  have observed := verifyBitsRun_code_of_some (inputCode empty.val empty.val []) []
    empty.val empty.val [] parsed
  rw [Examples.RotationCertificateVerification.complete_wrapper_literal_cases.1] at observed
  exact observed

theorem packed_one_rotation :
    verifyBitsRun (wordBits (inputCode leftTwo.val rightTwo.val [true]))
      (wordBits (certCode [rootRight])) = (true, 137) := by
  have parsed := congrArg Prod.fst (parseInputRun_code leftTwo.val rightTwo.val [true])
  have observed := verifyBitsRun_code_of_some (inputCode leftTwo.val rightTwo.val [true])
    (certCode [rootRight]) leftTwo.val rightTwo.val [true] parsed
  rw [Examples.RotationCertificateVerification.complete_wrapper_literal_cases.2.1] at observed
  exact observed

/-! Input failures never inspect the arbitrary bit certificate. -/

theorem partial_input_skips_the_certificate (short cert : Bits)
    (positive : 0 < short.length) (incomplete : short.length < 4) :
    verifyBitsRun short cert = (false, 4) := by
  have failed := unpackWordRun_short short positive incomplete
  have observed := verifyBitsRun_input_none short cert (congrArg Prod.fst failed)
  rw [failed] at observed
  exact observed

theorem decoded_empty_input_skips_the_certificate (cert : Bits) :
    verifyBitsRun [] cert = (false, 8) :=
  verifyBitsRun_parse_none [] cert [] rfl rfl

/-! Certificate decoding is complete and precedes every stream operation. -/

theorem partial_certificate_before_stream (source target : BinaryTree Unit) (bs : Bits)
    (pref : Word) (short : Bits)
    (positive : 0 < short.length) (incomplete : short.length < 4) :
    verifyBitsRun (wordBits (inputCode source target bs)) (wordBits pref ++ short) =
      (false, 4 * (inputCode source target bs).length + 7 * source.numNodes +
        7 * target.numNodes + 3 * bs.length + 2 * pref.length + 21) := by
  have failed := unpackWordRun_partial pref short positive incomplete
  have decoded := congrArg Prod.fst (unpackWordRun_code (inputCode source target bs))
  have parsed := congrArg Prod.fst (parseInputRun_code source target bs)
  have observed := verifyBitsRun_certificate_none
    (wordBits (inputCode source target bs)) (wordBits pref ++ short)
    (inputCode source target bs) source target bs decoded parsed (congrArg Prod.fst failed)
  rw [unpackWordRun_code, parseInputRun_code, failed] at observed
  refine observed.trans ?_
  apply Prod.ext
  · rfl
  · dsimp only
    omega

theorem valid_inputs_with_partial_certificates (bit : Bool) :
    verifyBitsRun (wordBits (inputCode empty.val empty.val [])) [bit] = (false, 41) ∧
      verifyBitsRun (wordBits (inputCode leftTwo.val rightTwo.val [true])) [bit] =
        (false, 108) :=
  ⟨partial_certificate_before_stream empty.val empty.val [] [] [bit] (by simp) (by simp),
    partial_certificate_before_stream leftTwo.val rightTwo.val [true] [] [bit]
      (by simp) (by simp)⟩

theorem valid_move_bits_then_partial_block (bit : Bool) :
    verifyBitsRun (wordBits (inputCode leftTwo.val rightTwo.val [true]))
      (wordBits (certCode [rootRight]) ++ [bit]) = (false, 112) :=
  partial_certificate_before_stream leftTwo.val rightTwo.val [true]
    (certCode [rootRight]) [bit] (by simp) (by simp)

theorem malformed_extension_can_reduce_observed_work (bit : Bool) :
    verifyBitsRun (wordBits (inputCode leftTwo.val rightTwo.val [true]))
        (wordBits (certCode [rootRight])) = (true, 137) ∧
      verifyBitsRun (wordBits (inputCode leftTwo.val rightTwo.val [true]))
        (wordBits (certCode [rootRight]) ++ [bit]) = (false, 112) ∧
      (verifyBitsRun (wordBits (inputCode leftTwo.val rightTwo.val [true]))
        (wordBits (certCode [rootRight]) ++ [bit])).2 <
      (verifyBitsRun (wordBits (inputCode leftTwo.val rightTwo.val [true]))
        (wordBits (certCode [rootRight]))).2 := by
  refine ⟨packed_one_rotation, valid_move_bits_then_partial_block bit, ?_⟩
  rw [packed_one_rotation, valid_move_bits_then_partial_block bit]
  decide

theorem zero_fuel_still_pays_for_complete_bit_decoding (tag : Tag) (tail : Word) :
    verifyBitsRun (wordBits (inputCode empty.val empty.val [])) (wordBits (tag :: tail)) =
      (false, 4 * (tag :: tail).length + 44) := by
  have parsed := congrArg Prod.fst (parseInputRun_code empty.val empty.val [])
  have wordRun : verifyRun (inputCode empty.val empty.val []) (tag :: tail) =
      (false, 20) := by
    rw [verifyRun_code, checkStreamRun_no_fuel [] empty.val empty.val tag tail rfl]
    rfl
  have observed := verifyBitsRun_code_of_some (inputCode empty.val empty.val [])
    (tag :: tail) empty.val empty.val [] parsed
  rw [wordRun] at observed
  refine observed.trans ?_
  apply Prod.ext
  · rfl
  · change 20 + 4 * (tag :: tail).length + 4 + 20 = 4 * (tag :: tail).length + 44
    omega

/-! Actual packed emitter results pass through actual decoding and verification. -/

theorem actual_packed_input_decodes (source target : BinaryTree Unit) (bs : Bits) :
    unpackWordRun (emitPackedInputRun source target bs).1 =
      (some (inputCode source target bs), 4 * (inputCode source target bs).length + 2) := by
  rw [emitPackedInputRun_value, unpackWordRun_code]

theorem actual_packed_certificate_decodes (moves : List RotationMove) :
    unpackWordRun (emitPackedCertificateRun moves).1 =
      (some (certCode moves), 4 * (certCode moves).length + 2) := by
  rw [emitPackedCertificateRun_value, unpackWordRun_code]

theorem actual_packed_emitters_feed_acceptance
    (source target : BinaryTree Unit) (bs : Bits) (moves : List RotationMove)
    (run : applyMoves? moves source = some target) (bounded : moves.length ≤ value bs) :
    (verifyBitsRun (emitPackedInputRun source target bs).1
      (emitPackedCertificateRun moves).1).1 = true := by
  have decoded := congrArg Prod.fst (actual_packed_input_decodes source target bs)
  have parsed := congrArg Prod.fst (parseInputRun_code source target bs)
  have certificate := congrArg Prod.fst (actual_packed_certificate_decodes moves)
  rw [verifyBitsRun_success _ _ (inputCode source target bs) (certCode moves)
    source target bs decoded parsed certificate]
  exact checkStreamRun_complete moves bs source target run bounded

theorem actual_one_rotation_pipeline_work :
    Resources.bind (emitPackedInputRun leftTwo.val rightTwo.val [true]) (fun input =>
      Resources.bind (emitPackedCertificateRun [rootRight]) (fun cert =>
        verifyBitsRun input cert)) = (true, 267) := by
  have input : emitPackedInputRun leftTwo.val rightTwo.val [true] =
      (wordBits (inputCode leftTwo.val rightTwo.val [true]), 112) :=
    emitPackedInputRun_eq leftTwo.val rightTwo.val [true]
  have cert : emitPackedCertificateRun [rootRight] =
      (wordBits (certCode [rootRight]), 18) := emitPackedCertificateRun_eq [rootRight]
  have observed := congrArg (fun result : Measured Bool Nat =>
    (result.1, 112 + (18 + result.2))) packed_one_rotation
  rw [input, cert]
  exact observed

/-! The independent language is inhabited, and its small witness has the all-raw work bound. -/

theorem one_rotation_binary_language_is_inhabited :
    BinaryYes (wordBits (inputCode leftTwo.val rightTwo.val [true])) :=
  verifyBitsRun_sound _ _ (congrArg Prod.fst packed_one_rotation)

theorem accepted_raw_bits_have_a_bounded_legal_trace (input cert : Bits) :
    (verifyBitsRun input cert).1 = true ↔
      ∃ (source target : BinaryTree Unit) (bs : Bits) (moves : List RotationMove),
        input = wordBits (inputCode source target bs) ∧
        cert = wordBits (certCode moves) ∧ applyMoves? moves source = some target ∧
        moves.length ≤ value bs :=
  verifyBitsRun_accept_iff_trace input cert

theorem small_bit_witness_and_its_uniform_work (input : Bits) (yes : BinaryYes input) :
    ∃ cert : Bits, cert.length ≤ input.length ^ 2 ∧
      (verifyBitsRun input cert).1 = true ∧
        (verifyBitsRun input cert).2 ≤ 40 * (input.length + cert.length + 1) ^ 2 := by
  obtain ⟨cert, small, accepted⟩ := verifyBitsRun_complete_small input yes
  exact ⟨cert, small, accepted, verifyBitsRun_work_all input cert⟩

theorem arbitrary_incomplete_words_are_within_the_bound (input cert : Bits) :
    (verifyBitsRun input cert).2 ≤ 40 * (input.length + cert.length + 1) ^ 2 :=
  verifyBitsRun_work_all input cert

end Examples.RotationCertificateBinary
