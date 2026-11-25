import Applications.Resources.RotationCertificate.BitCodec
import Applications.Resources.RotationCertificate.Verifier

/-!
# Binary rotation-certificate verification

The actual decoder first supplies the complete input word to the actual input
parser. Only successful input syntax permits certificate decoding, followed by
the actual stream on the returned fields. Complete certificate decoding is eager;
the stream's unvisited symbol suffix does not imply unvisited certificate bits.
Soundness and a quadratic bit-witness bound refer to an independent language.
The universal work theorem is a declared source-event bound, not a machine-time
or formal NP-membership result.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate
open Resources.BinaryCounter (Bits value)
open Trees.Rotations (RotationMove applyMoves?)

/-- Decode and parse input before decoding the complete certificate and streaming. -/
def verifyBitsRun (input cert : Bits) : Measured Bool Nat :=
  CallCount.tick (bind (unpackWordRun input) (fun decoded => match decoded with
    | none => (false, 1)
    | some word => bind (parseInputRun word) (fun parsed => match parsed with
      | none => (false, 1)
      | some (source, target, bs) =>
          bind (unpackWordRun cert) (fun moves => match moves with
            | none => (false, 1)
            | some actual => checkStreamRun bs source target actual))))

theorem verifyBitsRun_input_none (input cert : Bits)
    (failed : (unpackWordRun input).1 = none) :
    verifyBitsRun input cert = (false, (unpackWordRun input).2 + 2) := by
  simp only [verifyBitsRun, CallCount.tick, bind, failed]

theorem verifyBitsRun_parse_none (input cert : Bits) (word : Word)
    (decoded : (unpackWordRun input).1 = some word)
    (failed : (parseInputRun word).1 = none) :
    verifyBitsRun input cert =
      (false, (unpackWordRun input).2 + (parseInputRun word).2 + 2) := by
  simp only [verifyBitsRun, CallCount.tick, bind, decoded, failed]
  congr 1

theorem verifyBitsRun_certificate_none (input cert : Bits) (word : Word)
    (source target : BinaryTree Unit) (bs : Bits)
    (decoded : (unpackWordRun input).1 = some word)
    (parsed : (parseInputRun word).1 = some (source, target, bs))
    (failed : (unpackWordRun cert).1 = none) :
    verifyBitsRun input cert =
      (false, (unpackWordRun input).2 + (parseInputRun word).2 +
        (unpackWordRun cert).2 + 2) := by
  simp only [verifyBitsRun, CallCount.tick, bind, decoded, parsed, failed]
  congr 1
  omega

theorem verifyBitsRun_success (input cert : Bits) (word moves : Word)
    (source target : BinaryTree Unit) (bs : Bits)
    (decoded : (unpackWordRun input).1 = some word)
    (parsed : (parseInputRun word).1 = some (source, target, bs))
    (certificate : (unpackWordRun cert).1 = some moves) :
    verifyBitsRun input cert =
      ((checkStreamRun bs source target moves).1,
        (unpackWordRun input).2 + (parseInputRun word).2 +
        (unpackWordRun cert).2 + (checkStreamRun bs source target moves).2 + 1) := by
  simp only [verifyBitsRun, CallCount.tick, bind, decoded, parsed, certificate]
  congr 1
  omega

/-- With exact codes, Boolean acceptance agrees for every pair of symbol words. -/
theorem verifyBitsRun_code_value (input cert : Word) :
    (verifyBitsRun (wordBits input) (wordBits cert)).1 = (verifyRun input cert).1 := by
  cases parsed : (parseInputRun input).1 with
  | none =>
      rw [verifyBitsRun_parse_none _ _ input (by rw [unpackWordRun_code]) parsed,
        verifyRun_of_none input cert parsed]
  | some fields =>
      rcases fields with ⟨source, target, bs⟩
      rw [verifyBitsRun_success _ _ input cert source target bs
          (by rw [unpackWordRun_code]) parsed (by rw [unpackWordRun_code]),
        verifyRun_of_some input cert source target bs parsed]

/-- Successful input syntax charges both actual decoders and one verifier entry. -/
theorem verifyBitsRun_code_of_some (input cert : Word)
    (source target : BinaryTree Unit) (bs : Bits)
    (parsed : (parseInputRun input).1 = some (source, target, bs)) :
    verifyBitsRun (wordBits input) (wordBits cert) =
      ((verifyRun input cert).1,
        4 * input.length + 4 * cert.length + 4 + (verifyRun input cert).2) := by
  rw [verifyBitsRun_success _ _ input cert source target bs
      (by rw [unpackWordRun_code]) parsed (by rw [unpackWordRun_code]),
    verifyRun_of_some input cert source target bs parsed,
    unpackWordRun_code, unpackWordRun_code]
  dsimp only
  congr 1
  omega

/-- Syntax failure skips the entire bit certificate, regardless of its contents. -/
theorem verifyBitsRun_code_of_none (input : Word) (cert : Bits)
    (failed : (parseInputRun input).1 = none) :
    verifyBitsRun (wordBits input) cert =
      (false, 4 * input.length + 2 + (verifyRun input []).2) := by
  rw [verifyBitsRun_parse_none _ cert input (by rw [unpackWordRun_code]) failed,
    unpackWordRun_code, verifyRun_of_none input [] failed]
  dsimp only
  congr 1

/-- Every raw accepting pair has exact complete codes and an accepting word pair. -/
theorem verifyBitsRun_accept_iff (input cert : Bits) :
    (verifyBitsRun input cert).1 = true ↔
      ∃ word moves : Word, input = wordBits word ∧ cert = wordBits moves ∧
        (verifyRun word moves).1 = true := by
  constructor
  · intro accepted
    cases decoded : (unpackWordRun input).1 with
    | none =>
        rw [verifyBitsRun_input_none input cert decoded] at accepted
        cases accepted
    | some word =>
        cases parsed : (parseInputRun word).1 with
        | none =>
            rw [verifyBitsRun_parse_none input cert word decoded parsed] at accepted
            cases accepted
        | some fields =>
            rcases fields with ⟨source, target, bs⟩
            cases certificate : (unpackWordRun cert).1 with
            | none =>
                rw [verifyBitsRun_certificate_none input cert word source target bs
                  decoded parsed certificate] at accepted
                cases accepted
            | some moves =>
                have inputCode := (unpackWordRun_iff input word).1 decoded
                have certCode := (unpackWordRun_iff cert moves).1 certificate
                refine ⟨word, moves, inputCode, certCode, ?_⟩
                rw [inputCode, certCode, verifyBitsRun_code_value] at accepted
                exact accepted
  · rintro ⟨word, moves, inputCode, certCode, accepted⟩
    rw [inputCode, certCode, verifyBitsRun_code_value]
    exact accepted

theorem verifyBitsRun_accept_iff_trace (input cert : Bits) :
    (verifyBitsRun input cert).1 = true ↔
      ∃ (source target : BinaryTree Unit) (bs : Bits) (moves : List RotationMove),
        input = wordBits (inputCode source target bs) ∧
        cert = wordBits (certCode moves) ∧ applyMoves? moves source = some target ∧
        moves.length ≤ value bs := by
  constructor
  · intro accepted
    obtain ⟨word, certificate, encodedInput, encodedCert, accepted⟩ :=
      (verifyBitsRun_accept_iff input cert).1 accepted
    obtain ⟨source, target, bs, moves, wordEq, certEq, run, bound⟩ :=
      (verifyRun_accept_iff word certificate).1 accepted
    exact ⟨source, target, bs, moves, wordEq ▸ encodedInput, certEq ▸ encodedCert,
      run, bound⟩
  · rintro ⟨source, target, bs, moves, encodedInput, encodedCert, run, bound⟩
    apply (verifyBitsRun_accept_iff input cert).2
    refine ⟨inputCode source target bs, certCode moves, encodedInput, encodedCert, ?_⟩
    exact (verifyRun_accept_iff _ _).2 ⟨source, target, bs, moves, rfl, rfl, run, bound⟩

/-- Independent binary language, using the distance-based symbol language. -/
def BinaryYes (input : Bits) : Prop :=
  ∃ word : Word, input = wordBits word ∧ Yes word

theorem verifyBitsRun_sound (input cert : Bits)
    (accepted : (verifyBitsRun input cert).1 = true) : BinaryYes input := by
  obtain ⟨word, moves, encoded, _, checked⟩ :=
    (verifyBitsRun_accept_iff input cert).1 accepted
  exact ⟨word, encoded, verifyRun_sound word moves checked⟩

/-- Packing the attained minimum gives a quadratic-size bit certificate. -/
theorem verifyBitsRun_complete_small (input : Bits) (yes : BinaryYes input) :
    ∃ cert : Bits, cert.length ≤ input.length ^ 2 ∧
      (verifyBitsRun input cert).1 = true := by
  obtain ⟨word, encoded, yes⟩ := yes
  obtain ⟨moves, size, checked⟩ := verifyRun_complete_small word yes
  refine ⟨wordBits moves, ?_, ?_⟩
  · rw [encoded, wordBits_length, wordBits_length]
    simp only [pow_two] at size ⊢
    nlinarith [Nat.zero_le (word.length * word.length)]
  · rw [encoded, verifyBitsRun_code_value]
    exact checked

theorem binaryYes_iff_exists_certificate (input : Bits) :
    BinaryYes input ↔ ∃ cert : Bits, (verifyBitsRun input cert).1 = true := by
  constructor
  · intro yes
    obtain ⟨cert, _, accepted⟩ := verifyBitsRun_complete_small input yes
    exact ⟨cert, accepted⟩
  · rintro ⟨cert, accepted⟩
    exact verifyBitsRun_sound input cert accepted

/-- Actual word packing preserves the complete word verifier's Boolean. -/
theorem verifyBitsRun_packed_value (input cert : Word) :
    (verifyBitsRun (packWordRun input []).1 (packWordRun cert []).1).1 =
      (verifyRun input cert).1 := by
  rw [packWordRun_value, packWordRun_value, List.append_nil, List.append_nil,
    verifyBitsRun_code_value]

/-- Actual tree/trace emitters and bit packers feed the actual binary verifier. -/
theorem verifyBitsRun_emit_trace (source target : BinaryTree Unit) (bs : Bits)
    (moves : List RotationMove) (run : applyMoves? moves source = some target)
    (bound : moves.length ≤ value bs) :
    (verifyBitsRun (emitPackedInputRun source target bs).1
      (emitPackedCertificateRun moves).1).1 = true := by
  rw [emitPackedInputRun_value, emitPackedCertificateRun_value, verifyBitsRun_code_value]
  exact (verifyRun_accept_iff _ _).2
    ⟨source, target, bs, moves, rfl, rfl, run, bound⟩

/-- The observation bound covers every raw pair, including incomplete bit blocks. -/
theorem verifyBitsRun_work_all (input cert : Bits) :
    (verifyBitsRun input cert).2 ≤ 40 * (input.length + cert.length + 1) ^ 2 := by
  have inputBound := unpackWordRun_cost_le input
  cases decoded : (unpackWordRun input).1 with
  | none =>
      rw [verifyBitsRun_input_none input cert decoded]
      dsimp only
      nlinarith [Nat.zero_le (input.length * input.length),
        Nat.zero_le (cert.length * cert.length), Nat.zero_le (input.length * cert.length)]
  | some word =>
      have wordSize : word.length ≤ input.length := by
        rw [(unpackWordRun_iff input word).1 decoded, wordBits_length]
        omega
      have parserBound := parseInputRun_cost_le word
      cases parsed : (parseInputRun word).1 with
      | none =>
          rw [verifyBitsRun_parse_none input cert word decoded parsed]
          dsimp only
          nlinarith [Nat.zero_le (input.length * input.length),
            Nat.zero_le (cert.length * cert.length),
            Nat.zero_le (input.length * cert.length)]
      | some fields =>
          rcases fields with ⟨source, target, bs⟩
          have certificateBound := unpackWordRun_cost_le cert
          cases certificate : (unpackWordRun cert).1 with
          | none =>
              rw [verifyBitsRun_certificate_none input cert word source target bs
                decoded parsed certificate]
              dsimp only
              nlinarith [Nat.zero_le (input.length * input.length),
                Nat.zero_le (cert.length * cert.length),
                Nat.zero_le (input.length * cert.length)]
          | some moves =>
              have certSize : moves.length ≤ cert.length := by
                rw [(unpackWordRun_iff cert moves).1 certificate, wordBits_length]
                omega
              have wordWork := verifyRun_work_all word moves
              rw [verifyRun_of_some word moves source target bs parsed] at wordWork
              dsimp only at wordWork
              have lengths : word.length + moves.length + 1 ≤
                  input.length + cert.length + 1 := by omega
              have squares := Nat.mul_le_mul lengths lengths
              rw [verifyBitsRun_success input cert word moves source target bs
                decoded parsed certificate]
              dsimp only
              simp only [pow_two] at wordWork ⊢
              nlinarith [Nat.zero_le (input.length * input.length),
                Nat.zero_le (cert.length * cert.length),
                Nat.zero_le (input.length * cert.length)]

end Resources.RotationCertificate
