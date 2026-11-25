import DelimiterPrelude144b

/-!
Pure protocol extension of the frozen delimiter draft. UNCOMPILED repair2.
No original file or fixture value is changed. This local research import is a
staging dependency, not an installed source owner or a compiler result.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.DelimiterPreludeDraft.GeneralProof1

open Resources.BinaryCounter (Bits)

theorem first_delimiter_cases (raw : Raw) :
    (∃ bits : Bits, raw = bits.map some) ∨
      ∃ (bits : Bits) (tail : Raw), raw = bits.map some ++ none :: tail := by
  induction raw with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons a raw ih =>
      cases a with
      | none => exact Or.inr ⟨[], raw, rfl⟩
      | some b =>
          rcases ih with ⟨bits, rfl⟩ | ⟨bits, tail, rfl⟩
          · exact Or.inl ⟨b :: bits, rfl⟩
          · exact Or.inr ⟨b :: bits, tail, rfl⟩

/-- The complete malformed/valid classification, with an arbitrary tail after
the second delimiter. No raw input is omitted. -/
theorem protocol_cases (raw : Raw) :
    (∃ input : Bits, raw = input.map some) ∨
      (∃ input cert : Bits, raw = literalPair input cert) ∨
      ∃ (input cert : Bits) (tail : Raw), raw = literalPair input cert ++ none :: tail := by
  rcases first_delimiter_cases raw with ⟨input, rfl⟩ | ⟨input, tail, rfl⟩
  · exact Or.inl ⟨input, rfl⟩
  · rcases first_delimiter_cases tail with ⟨cert, rfl⟩ | ⟨cert, rest, rfl⟩
    · exact Or.inr (Or.inl ⟨input, cert, by simp [literalPair, List.append_assoc]⟩)
    · exact Or.inr (Or.inr ⟨input, cert, rest,
        by simp [literalPair, List.append_assoc]⟩)

theorem suffixBits_map_append (bits : Bits) (tail : Raw) :
    suffixBits (bits.map some ++ tail) = (suffixBits tail).map (bits ++ ·) := by
  induction bits with
  | nil =>
      simp only [List.map_nil, List.nil_append]
      cases suffixBits tail <;> rfl
  | cons b bits ih =>
      simp only [List.map_cons, List.cons_append, suffixBits, ih]
      cases suffixBits tail <;> rfl

theorem splitLiteral_map_append (input : Bits) (tail : Raw) :
    splitLiteral (input.map some ++ tail) =
      (splitLiteral tail).map (fun pair => (input ++ pair.1, pair.2)) := by
  induction input with
  | nil =>
      simp only [List.map_nil, List.nil_append]
      cases splitLiteral tail <;> rfl
  | cons b input ih =>
      simp only [List.map_cons, List.cons_append, splitLiteral, ih]
      cases splitLiteral tail <;> rfl

theorem suffixBits_before_delimiter (bits : Bits) (tail : Raw) :
    suffixBits (bits.map some ++ none :: tail) = none := by
  rw [suffixBits_map_append]
  rfl

theorem splitLiteral_missing (input : Bits) : splitLiteral (input.map some) = none := by
  have h := splitLiteral_map_append input []
  simpa only [List.append_nil, splitLiteral, Option.map_none] using h

theorem splitLiteral_repeated (input cert : Bits) (tail : Raw) :
    splitLiteral (literalPair input cert ++ none :: tail) = none := by
  have shape : literalPair input cert ++ none :: tail =
      input.map some ++ none :: (cert.map some ++ none :: tail) := by
    simp only [literalPair, List.append_assoc, List.singleton_append]
    rfl
  rw [shape, splitLiteral_map_append, splitLiteral, suffixBits_before_delimiter]
  rfl

theorem suffixBits_iff (raw : Raw) (bits : Bits) :
    suffixBits raw = some bits ↔ raw = bits.map some := by
  constructor
  · intro parsed
    rcases first_delimiter_cases raw with ⟨other, rfl⟩ | ⟨before, tail, rfl⟩
    · have same : other = bits := Option.some.inj ((suffixBits_map other).symm.trans parsed)
      exact congrArg (List.map some) same
    · rw [suffixBits_before_delimiter] at parsed
      cases parsed
  · rintro rfl
    exact suffixBits_map bits

/-- The converse protocol connection includes repeated/missing rejection. -/
theorem splitLiteral_iff (raw : Raw) (input cert : Bits) :
    splitLiteral raw = some (input, cert) ↔ raw = literalPair input cert := by
  constructor
  · intro parsed
    rcases protocol_cases raw with ⟨before, rfl⟩ | ⟨left, right, rfl⟩ | ⟨left, right, tail, rfl⟩
    · rw [splitLiteral_missing] at parsed
      cases parsed
    · have same : (left, right) = (input, cert) :=
        Option.some.inj ((splitLiteral_pair left right).symm.trans parsed)
      cases same
      rfl
    · rw [splitLiteral_repeated] at parsed
      cases parsed
  · rintro rfl
    exact splitLiteral_pair input cert

theorem literalPair_injective :
    Function.Injective (fun pair : Bits × Bits => literalPair pair.1 pair.2) := by
  intro left right equal
  have observed := congrArg splitLiteral equal
  rw [splitLiteral_pair, splitLiteral_pair] at observed
  exact Option.some.inj observed

theorem splitLiteral_none_iff (raw : Raw) :
    splitLiteral raw = none ↔
      (∃ input : Bits, raw = input.map some) ∨
      ∃ (input cert : Bits) (tail : Raw), raw = literalPair input cert ++ none :: tail := by
  constructor
  · intro parsed
    rcases protocol_cases raw with ⟨input, rfl⟩ | ⟨input, cert, rfl⟩ | ⟨input, cert, tail, rfl⟩
    · exact Or.inl ⟨input, rfl⟩
    · rw [splitLiteral_pair] at parsed
      cases parsed
    · exact Or.inr ⟨input, cert, tail, rfl⟩
  · rintro (⟨input, rfl⟩ | ⟨input, cert, tail, rfl⟩)
    · exact splitLiteral_missing input
    · exact splitLiteral_repeated input cert tail

theorem suffixWorkLength_map_append (bits : Bits) (tail : Raw) :
    suffixWorkLength (bits.map some ++ tail) = bits.length + suffixWorkLength tail := by
  induction bits with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil, Nat.zero_add]
  | cons b bits ih =>
      simp only [List.map_cons, List.cons_append, suffixWorkLength, List.length_cons, ih]
      omega

theorem workLength_map_append (bits : Bits) (tail : Raw) :
    workLength (bits.map some ++ tail) = 2 * bits.length + workLength tail := by
  induction bits with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil, Nat.mul_zero, Nat.zero_add]
  | cons b bits ih =>
      simp only [List.map_cons, List.cons_append, workLength, List.length_cons, ih]
      omega

theorem workLength_missing (input : Bits) : workLength (input.map some) = 2 * input.length := by
  simpa only [List.append_nil, workLength, Nat.add_zero] using workLength_map_append input []

theorem workLength_pair (input cert : Bits) :
    workLength (literalPair input cert) = 2 * input.length + cert.length + 1 := by
  have shape : literalPair input cert = input.map some ++ none :: cert.map some := by
    simp only [literalPair, List.append_assoc, List.singleton_append]
  rw [shape, workLength_map_append, workLength]
  have h := suffixWorkLength_map_append cert []
  simp only [List.append_nil, suffixWorkLength, Nat.add_zero] at h
  rw [h]
  omega

theorem workLength_repeated (input cert : Bits) (tail : Raw) :
    workLength (literalPair input cert ++ none :: tail) =
      2 * input.length + cert.length + 1 := by
  have shape : literalPair input cert ++ none :: tail =
      input.map some ++ none :: (cert.map some ++ none :: tail) := by
    simp only [literalPair, List.append_assoc, List.singleton_append]
    rfl
  rw [shape, workLength_map_append, workLength, suffixWorkLength_map_append,
    suffixWorkLength]
  omega

theorem repeated_length (input cert : Bits) (tail : Raw) :
    (literalPair input cert ++ none :: tail).length =
      input.length + cert.length + tail.length + 2 := by
  rw [List.length_append, literalPair_length, List.length_cons]
  omega

theorem preludeSteps_missing (input : Bits) :
    preludeSteps (input.map some) = 3 * input.length + 2 := by
  rw [preludeSteps, List.length_map, workLength_missing]
  omega

theorem preludeSteps_pair (input cert : Bits) :
    preludeSteps (literalPair input cert) = 3 * input.length + 2 * cert.length + 4 := by
  rw [preludeSteps, literalPair_length, workLength_pair]
  omega

theorem preludeSteps_pair_frame (input cert : Bits) :
    preludeSteps (literalPair input cert) =
      (literalPair input cert).length + (BitPairFraming.frame input cert).length + 2 := by
  rw [preludeSteps, workLength_pair, BitPairFraming.frame_length]

theorem preludeSteps_repeated (input cert : Bits) (tail : Raw) :
    preludeSteps (literalPair input cert ++ none :: tail) =
      3 * input.length + 2 * cert.length + tail.length + 5 := by
  rw [preludeSteps, repeated_length, workLength_repeated]
  omega

theorem preludeSteps_repeated_frame (input cert : Bits) (tail : Raw) :
    preludeSteps (literalPair input cert ++ none :: tail) =
      (literalPair input cert ++ none :: tail).length +
        (BitPairFraming.frame input cert).length + 2 := by
  rw [preludeSteps, workLength_repeated, BitPairFraming.frame_length]

theorem handoffWord_missing (input : Bits) : handoffWord (input.map some) = [] := by
  rw [handoffWord, splitLiteral_missing]

theorem handoffWord_repeated (input cert : Bits) (tail : Raw) :
    handoffWord (literalPair input cert ++ none :: tail) = [] := by
  rw [handoffWord, splitLiteral_repeated]

theorem handoffWord_length_le_workLength (raw : Raw) :
    (handoffWord raw).length ≤ workLength raw := by
  rcases protocol_cases raw with ⟨input, rfl⟩ | ⟨input, cert, rfl⟩ | ⟨input, cert, tail, rfl⟩
  · rw [handoffWord_missing, List.length_nil]
    exact Nat.zero_le _
  · simpa only [handoffWord_pair, BitPairFraming.frame_length, workLength_pair] using
      (Nat.le_refl (2 * input.length + cert.length + 1))
  · rw [handoffWord_repeated, List.length_nil]
    exact Nat.zero_le _

theorem handoffWord_length_le (raw : Raw) : (handoffWord raw).length ≤ 2 * raw.length :=
  (handoffWord_length_le_workLength raw).trans (workLength_le raw)

theorem verifyDelimited_accept_iff (raw : Raw) :
    verifyDelimited raw = true ↔
      ∃ input cert : Bits, raw = literalPair input cert ∧ (verifyBitsRun input cert).1 = true := by
  constructor
  · intro accepted
    cases parsed : splitLiteral raw with
    | none => simp [verifyDelimited, parsed] at accepted
    | some pair =>
        rcases pair with ⟨input, cert⟩
        exact ⟨input, cert, (splitLiteral_iff raw input cert).1 parsed,
          by simpa only [verifyDelimited, parsed] using accepted⟩
  · rintro ⟨input, cert, rfl, accepted⟩
    rwa [verifyDelimited_pair]

theorem lastInputPop_cons (seed : Scratch) (a : Option Bool) (rest : Raw) :
    lastInputPop seed (a :: rest) = lastInputPop (some a) rest := by
  unfold lastInputPop
  rw [List.reverse_cons]
  cases rest.reverse <;> rfl

theorem lastBitPop_cons (seed : Scratch) (b : Bool) (rest : Bits) :
    lastBitPop seed (b :: rest) = lastBitPop (some (some b)) rest := by
  exact lastInputPop_cons seed (some b) (rest.map some)

theorem lastInputPop_append (seed : Scratch) (left right : Raw) :
    lastInputPop seed (left ++ right) = lastInputPop (lastInputPop seed left) right := by
  induction left generalizing seed with
  | nil => rfl
  | cons a left ih =>
      simp only [List.cons_append, lastInputPop_cons, ih]

theorem lastBitPop_append (seed : Scratch) (left right : Bits) :
    lastBitPop seed (left ++ right) = lastBitPop (lastBitPop seed left) right := by
  unfold lastBitPop
  rw [List.map_append, lastInputPop_append]

theorem frame_reverse (input cert : Bits) :
    (BitPairFraming.frame input cert).reverse =
      cert.reverse ++ true :: (BitPairFraming.escapeBits input).reverse := by
  simp only [BitPairFraming.frame, List.reverse_append, List.reverse_cons,
    List.append_assoc, List.singleton_append]

end Resources.RotationCertificate.DelimiterPreludeDraft.GeneralProof1
