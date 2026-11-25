import Applications.Resources.RotationCertificate.DelimiterMachine

set_option autoImplicit false
set_option warningAsError true

/-!
# Literal delimiter execution

Protocol classification, actual source loops and their composition
retain cleanup branches, complete endpoints and exact clocks.
-/

/- Complete preserved component: protocol. -/
section

namespace Resources.RotationCertificate.DelimiterMachine.Execution

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

end Resources.RotationCertificate.DelimiterMachine.Execution

end

/- Complete preserved component: native_loops. -/
section

namespace Resources.RotationCertificate.DelimiterMachine.Execution

open Resources.BinaryCounter (Bits)

variable {R : Type}

theorem next_some (c : Cfg R) : next (some c) = step c := rfl

theorem run_one {a b : Cfg R} (executed : step a = some b) :
    next^[1] (some a) = some b := by
  simpa only [Function.iterate_one, next_some] using executed

theorem run_trans {a b c : Cfg R} {m n : Nat}
    (first : next^[m] (some a) = some b)
    (second : next^[n] (some b) = some c) :
    next^[m + n] (some a) = some c := by
  calc
    next^[m + n] (some a) = next^[n] (next^[m] (some a)) := by
      rw [Nat.add_comm m n, Function.iterate_add_apply]
    _ = some c := by rw [first, second]

theorem run_count {a b : Cfg R} {m n : Nat} (count : m = n)
    (executed : next^[m] (some a) = some b) : next^[n] (some a) = some b :=
  count ▸ executed

theorem bits_split_append (input : Bits) (tail : Raw) (n : Nat) :
    input.map some ++ tail =
      (input.take n).map some ++ ((input.drop n).map some ++ tail) := by
  calc
    input.map some ++ tail = (input.take n ++ input.drop n).map some ++ tail := by
      rw [List.take_append_drop]
    _ = _ := by rw [List.map_append, List.append_assoc]

theorem pair_split_append (input cert : Bits) (tail : Raw) (n : Nat) :
    literalPair input cert ++ tail =
      literalPair input (cert.take n) ++ ((cert.drop n).map some ++ tail) := by
  simpa only [literalPair, List.append_assoc] using
    congrArg (fun rest : Raw => input.map some ++ ([none] ++ rest))
      (bits_split_append cert tail n)

theorem prefix_bits (initial : R) (seen : Scratch) (input : Bits)
    (tail : Raw) (work framed : Bits) :
    next^[input.length] (some (state .prefix initial seen (input.map some ++ tail) work framed)) =
      some (state .prefix initial (lastBitPop seen input) tail
        ((BitPairFraming.escapeBits input).reverse ++ work) framed) := by
  induction input generalizing seen work with
  | nil => rfl
  | cons b input ih =>
      rw [List.map_cons, List.cons_append, List.length_cons,
        Function.iterate_succ_apply, next_some, step_prefix_bit]
      simpa only [lastBitPop_cons, BitPairFraming.escapeBits_cons,
        List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using
        ih (seen := some (some b)) (work := b :: false :: work)

theorem certificate_bits (initial : R) (seen : Scratch) (cert : Bits)
    (tail : Raw) (work framed : Bits) :
    next^[cert.length]
        (some (state .certificate initial seen (cert.map some ++ tail) work framed)) =
      some (state .certificate initial (lastBitPop seen cert) tail
        (cert.reverse ++ work) framed) := by
  induction cert generalizing seen work with
  | nil => rfl
  | cons b cert ih =>
      rw [List.map_cons, List.cons_append, List.length_cons,
        Function.iterate_succ_apply, next_some, step_certificate_bit]
      simpa only [lastBitPop_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using ih (seen := some (some b)) (work := b :: work)

theorem reverse_bits (initial : R) (seen : Scratch) (bits rest framed : Bits) :
    next^[bits.length]
        (some (state .reverse initial seen [] (bits ++ rest) framed)) =
      some (state .reverse initial (lastBitPop seen bits) [] rest
        (bits.reverse ++ framed)) := by
  induction bits generalizing seen framed with
  | nil => rfl
  | cons b bits ih =>
      rw [List.cons_append, List.length_cons, Function.iterate_succ_apply,
        next_some, step_reverse_bit]
      simpa only [lastBitPop_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using ih (seen := some (some b)) (framed := b :: framed)

theorem drain_input_words (initial : R) (seen : Scratch) (letters rest : Raw)
    (work framed : Bits) :
    next^[letters.length]
        (some (state .drainInput initial seen (letters ++ rest) work framed)) =
      some (state .drainInput initial (lastInputPop seen letters) rest work framed) := by
  induction letters generalizing seen with
  | nil => rfl
  | cons a letters ih =>
      rw [List.cons_append, List.length_cons, Function.iterate_succ_apply,
        next_some, step_drainInput_cons]
      simpa only [lastInputPop_cons] using ih (seen := some a)

theorem drain_work_bits (initial : R) (seen : Scratch) (bits rest : Bits) :
    next^[bits.length]
        (some (state .drainWork initial seen [] (bits ++ rest) [])) =
      some (state .drainWork initial (lastBitPop seen bits) [] rest []) := by
  induction bits generalizing seen with
  | nil => rfl
  | cons b bits ih =>
      rw [List.cons_append, List.length_cons, Function.iterate_succ_apply,
        next_some, step_drainWork_bit]
      simpa only [lastBitPop_cons] using ih (seen := some (some b))

theorem prefix_take (initial : R) (seen : Scratch) (input : Bits)
    (tail : Raw) (work framed : Bits) (n : Nat) (within : n ≤ input.length) :
    next^[n] (some (state .prefix initial seen (input.map some ++ tail) work framed)) =
      some (state .prefix initial (lastBitPop seen (input.take n))
        ((input.drop n).map some ++ tail)
        ((BitPairFraming.escapeBits (input.take n)).reverse ++ work) framed) := by
  have run := prefix_bits initial seen (input.take n)
    ((input.drop n).map some ++ tail) work framed
  rw [← bits_split_append input tail n] at run
  simpa only [List.length_take, Nat.min_eq_left within] using run

theorem certificate_take (initial : R) (seen : Scratch) (cert : Bits)
    (tail : Raw) (work framed : Bits) (n : Nat) (within : n ≤ cert.length) :
    next^[n]
        (some (state .certificate initial seen (cert.map some ++ tail) work framed)) =
      some (state .certificate initial (lastBitPop seen (cert.take n))
        ((cert.drop n).map some ++ tail) ((cert.take n).reverse ++ work) framed) := by
  have run := certificate_bits initial seen (cert.take n)
    ((cert.drop n).map some ++ tail) work framed
  rw [← bits_split_append cert tail n] at run
  simpa only [List.length_take, Nat.min_eq_left within] using run

theorem reverse_take (initial : R) (seen : Scratch) (work framed : Bits)
    (n : Nat) (within : n ≤ work.length) :
    next^[n] (some (state .reverse initial seen [] work framed)) =
      some (state .reverse initial (lastBitPop seen (work.take n)) [] (work.drop n)
        ((work.take n).reverse ++ framed)) := by
  have run := reverse_bits initial seen (work.take n) (work.drop n) framed
  rw [List.take_append_drop] at run
  simpa only [List.length_take, Nat.min_eq_left within] using run

theorem drain_input_take (initial : R) (seen : Scratch) (raw : Raw)
    (work framed : Bits) (n : Nat) (within : n ≤ raw.length) :
    next^[n] (some (state .drainInput initial seen raw work framed)) =
      some (state .drainInput initial (lastInputPop seen (raw.take n))
        (raw.drop n) work framed) := by
  have run := drain_input_words initial seen (raw.take n) (raw.drop n) work framed
  rw [List.take_append_drop] at run
  simpa only [List.length_take, Nat.min_eq_left within] using run

theorem drain_work_take (initial : R) (seen : Scratch) (work : Bits)
    (n : Nat) (within : n ≤ work.length) :
    next^[n] (some (state .drainWork initial seen [] work [])) =
      some (state .drainWork initial (lastBitPop seen (work.take n)) [] (work.drop n) []) := by
  have run := drain_work_bits initial seen (work.take n) (work.drop n)
  rw [List.take_append_drop] at run
  simpa only [List.length_take, Nat.min_eq_left within] using run

section FinitePackage

variable [Fintype R]

theorem init_transport (initial : R) (raw : Raw) (n : Nat) :
    next^[n] (some (Turing.initList (machine initial) raw)) =
      next^[n] (some (state .prefix initial none raw [] [])) :=
  congrArg (fun c : Cfg R => next^[n] (some c)) (machine_initList_eq initial raw)

theorem old_init_word_congr (initial : R) (left right : Bits) (same : left = right) :
    (some (Turing.initList (oldMachine initial) left) : Option (Cfg R)) =
      some (Turing.initList (oldMachine initial) right) :=
  congrArg (fun word : Bits => (some (Turing.initList (oldMachine initial) word) : Option (Cfg R))) same

theorem prefix_from_init (initial : R) (input : Bits) (tail : Raw)
    (n : Nat) (within : n ≤ input.length) :
    next^[n] (some (Turing.initList (machine initial) (input.map some ++ tail))) =
      some (state .prefix initial (lastBitPop none (input.take n))
        ((input.drop n).map some ++ tail)
        (BitPairFraming.escapeBits (input.take n)).reverse []) := by
  have executed : next^[n]
      (some (state .prefix initial none (input.map some ++ tail) [] [])) =
      some (state .prefix initial (lastBitPop none (input.take n))
        ((input.drop n).map some ++ tail)
        (BitPairFraming.escapeBits (input.take n)).reverse []) := by
    simpa only [List.append_nil] using prefix_take initial none input tail [] [] n within
  exact (init_transport initial (input.map some ++ tail) n).trans executed

theorem certificate_prefix (initial : R) (input cert : Bits) (tail : Raw)
    (n : Nat) (within : n ≤ cert.length) :
    next^[input.length + 1 + n]
        (some (Turing.initList (machine initial) (literalPair input cert ++ tail))) =
      some (state .certificate initial (lastBitPop (some none) (cert.take n))
        ((cert.drop n).map some ++ tail)
        (BitPairFraming.frame input (cert.take n)).reverse []) := by
  have shape : literalPair input cert ++ tail =
      input.map some ++ none :: (cert.map some ++ tail) := by
    simp only [literalPair, List.append_assoc, List.singleton_append]
    rfl
  have first : next^[input.length]
      (some (Turing.initList (machine initial)
        (input.map some ++ none :: (cert.map some ++ tail)))) =
      some (state .prefix initial (lastBitPop none input)
        (none :: (cert.map some ++ tail)) (BitPairFraming.escapeBits input).reverse []) := by
    have executed : next^[input.length]
        (some (state .prefix initial none
          (input.map some ++ none :: (cert.map some ++ tail)) [] [])) =
        some (state .prefix initial (lastBitPop none input)
          (none :: (cert.map some ++ tail)) (BitPairFraming.escapeBits input).reverse []) := by
      simpa only [List.append_nil] using
        prefix_bits initial none input (none :: (cert.map some ++ tail)) [] []
    exact (init_transport initial (input.map some ++ none :: (cert.map some ++ tail))
      input.length).trans executed
  have delimiter := run_one (step_prefix_delimiter initial (lastBitPop none input)
    (cert.map some ++ tail) (BitPairFraming.escapeBits input).reverse [])
  have suffix := certificate_take initial (some none) cert tail
    (true :: (BitPairFraming.escapeBits input).reverse) [] n within
  have composed := run_trans (run_trans first delimiter) suffix
  simpa only [← shape, frame_reverse] using composed

theorem valid_reverse_entry (initial : R) (input cert : Bits) :
    next^[(literalPair input cert).length + 1]
        (some (Turing.initList (machine initial) (literalPair input cert))) =
      some (state .reverse initial none [] (BitPairFraming.frame input cert).reverse []) := by
  have scanned : next^[input.length + 1 + cert.length]
      (some (Turing.initList (machine initial) (literalPair input cert))) =
      some (state .certificate initial (lastBitPop (some none) cert) []
        (BitPairFraming.frame input cert).reverse []) := by
    simpa only [List.append_nil, List.take_length, List.drop_length,
      List.map_nil, List.nil_append] using
      certificate_prefix initial input cert [] cert.length (Nat.le_refl _)
  have emptyProbe := run_one (step_certificate_empty initial
    (lastBitPop (some none) cert) (BitPairFraming.frame input cert).reverse [])
  have count : (input.length + 1 + cert.length) + 1 = (literalPair input cert).length + 1 := by
    rw [literalPair_length]
    omega
  exact run_count count (run_trans scanned emptyProbe)

theorem valid_reverse_prefix (initial : R) (input cert : Bits) (n : Nat)
    (within : n ≤ (BitPairFraming.frame input cert).length) :
    next^[(literalPair input cert).length + 1 + n]
        (some (Turing.initList (machine initial) (literalPair input cert))) =
      some (state .reverse initial
        (lastBitPop none ((BitPairFraming.frame input cert).reverse.take n)) []
        ((BitPairFraming.frame input cert).reverse.drop n)
        ((BitPairFraming.frame input cert).reverse.take n).reverse) := by
  have hrev : n ≤ (BitPairFraming.frame input cert).reverse.length := by
    simpa only [List.length_reverse] using within
  simpa only [List.append_nil] using run_trans
    (valid_reverse_entry initial input cert)
    (reverse_take initial none (BitPairFraming.frame input cert).reverse [] n hrev)

theorem reverse_finish (initial : R) (seen : Scratch) (work framed : Bits) :
    next^[work.length + 1] (some (state .reverse initial seen [] work framed)) =
      some (Turing.initList (oldMachine initial) (work.reverse ++ framed)) := by
  have before : next^[work.length] (some (state .reverse initial seen [] work framed)) =
      some (state .reverse initial (lastBitPop seen work) [] [] (work.reverse ++ framed)) := by
    simpa only [List.append_nil] using reverse_bits initial seen work [] framed
  exact run_trans before
    (run_one (step_reverse_empty initial (lastBitPop seen work) (work.reverse ++ framed)))

theorem drain_work_finish (initial : R) (seen : Scratch) (work : Bits) :
    next^[work.length + 1] (some (state .drainWork initial seen [] work [])) =
      some (Turing.initList (oldMachine initial) []) := by
  have before : next^[work.length] (some (state .drainWork initial seen [] work [])) =
      some (state .drainWork initial (lastBitPop seen work) [] [] []) := by
    simpa only [List.append_nil] using drain_work_bits initial seen work []
  exact run_trans before (run_one (step_drainWork_empty initial (lastBitPop seen work)))

theorem valid_handoff (initial : R) (input cert : Bits) :
    next^[preludeSteps (literalPair input cert)]
        (some (Turing.initList (machine initial) (literalPair input cert))) =
      some (Turing.initList (oldMachine initial) (BitPairFraming.frame input cert)) := by
  have composed := run_trans (valid_reverse_entry initial input cert)
    (reverse_finish initial none (BitPairFraming.frame input cert).reverse [])
  have count : ((literalPair input cert).length + 1) +
      ((BitPairFraming.frame input cert).reverse.length + 1) =
      preludeSteps (literalPair input cert) := by
    rw [List.length_reverse, preludeSteps_pair_frame]
    omega
  have word : (BitPairFraming.frame input cert).reverse.reverse ++ [] =
      BitPairFraming.frame input cert := by rw [List.reverse_reverse, List.append_nil]
  exact (run_count count composed).trans (old_init_word_congr initial _ _ word)

theorem missing_drain_entry (initial : R) (input : Bits) :
    next^[input.length + 1] (some (Turing.initList (machine initial) (input.map some))) =
      some (state .drainWork initial none [] (BitPairFraming.escapeBits input).reverse []) := by
  have scanned : next^[input.length]
      (some (Turing.initList (machine initial) (input.map some))) =
      some (state .prefix initial (lastBitPop none input) []
        (BitPairFraming.escapeBits input).reverse []) := by
    have executed : next^[input.length]
        (some (state .prefix initial none (input.map some) [] [])) =
        some (state .prefix initial (lastBitPop none input) []
          (BitPairFraming.escapeBits input).reverse []) := by
      simpa only [List.append_nil] using prefix_bits initial none input [] [] []
    exact (init_transport initial (input.map some) input.length).trans executed
  exact run_trans scanned
    (run_one (step_prefix_empty initial (lastBitPop none input)
      (BitPairFraming.escapeBits input).reverse []))

theorem missing_drain_prefix (initial : R) (input : Bits) (n : Nat)
    (within : n ≤ (BitPairFraming.escapeBits input).length) :
    next^[input.length + 1 + n]
        (some (Turing.initList (machine initial) (input.map some))) =
      some (state .drainWork initial
        (lastBitPop none ((BitPairFraming.escapeBits input).reverse.take n)) []
        ((BitPairFraming.escapeBits input).reverse.drop n) []) := by
  have hrev : n ≤ (BitPairFraming.escapeBits input).reverse.length := by
    simpa only [List.length_reverse] using within
  exact run_trans (missing_drain_entry initial input)
    (drain_work_take initial none (BitPairFraming.escapeBits input).reverse n hrev)

theorem missing_handoff (initial : R) (input : Bits) :
    next^[preludeSteps (input.map some)]
        (some (Turing.initList (machine initial) (input.map some))) =
      some (Turing.initList (oldMachine initial) []) := by
  have composed := run_trans (missing_drain_entry initial input)
    (drain_work_finish initial none (BitPairFraming.escapeBits input).reverse)
  have count : input.length + 1 + ((BitPairFraming.escapeBits input).reverse.length + 1) =
      preludeSteps (input.map some) := by
    rw [List.length_reverse, BitPairFraming.escapeBits_length, preludeSteps_missing]
    omega
  exact run_count count composed

theorem repeated_input_entry (initial : R) (input cert : Bits) (tail : Raw) :
    next^[input.length + cert.length + 2]
        (some (Turing.initList (machine initial) (literalPair input cert ++ none :: tail))) =
      some (state .drainInput initial (some none) tail
        (BitPairFraming.frame input cert).reverse []) := by
  have scanned : next^[input.length + 1 + cert.length]
      (some (Turing.initList (machine initial) (literalPair input cert ++ none :: tail))) =
      some (state .certificate initial (lastBitPop (some none) cert) (none :: tail)
        (BitPairFraming.frame input cert).reverse []) := by
    simpa only [List.take_length, List.drop_length, List.map_nil, List.nil_append] using
      certificate_prefix initial input cert (none :: tail) cert.length (Nat.le_refl _)
  have delimiter := run_one (step_certificate_delimiter initial
    (lastBitPop (some none) cert) tail (BitPairFraming.frame input cert).reverse [])
  have count : (input.length + 1 + cert.length) + 1 = input.length + cert.length + 2 := by omega
  exact run_count count (run_trans scanned delimiter)

theorem repeated_input_prefix (initial : R) (input cert : Bits) (tail : Raw)
    (n : Nat) (within : n ≤ tail.length) :
    next^[input.length + cert.length + 2 + n]
        (some (Turing.initList (machine initial) (literalPair input cert ++ none :: tail))) =
      some (state .drainInput initial (lastInputPop (some none) (tail.take n))
        (tail.drop n) (BitPairFraming.frame input cert).reverse []) :=
  run_trans (repeated_input_entry initial input cert tail)
    (drain_input_take initial (some none) tail (BitPairFraming.frame input cert).reverse [] n within)

theorem repeated_work_entry (initial : R) (input cert : Bits) (tail : Raw) :
    next^[(literalPair input cert ++ none :: tail).length + 1]
        (some (Turing.initList (machine initial) (literalPair input cert ++ none :: tail))) =
      some (state .drainWork initial none [] (BitPairFraming.frame input cert).reverse []) := by
  have drained : next^[input.length + cert.length + 2 + tail.length]
      (some (Turing.initList (machine initial) (literalPair input cert ++ none :: tail))) =
      some (state .drainInput initial (lastInputPop (some none) tail) []
        (BitPairFraming.frame input cert).reverse []) := by
    simpa only [List.take_length, List.drop_length] using
      repeated_input_prefix initial input cert tail tail.length (Nat.le_refl _)
  have emptyProbe := run_one (step_drainInput_empty initial (lastInputPop (some none) tail)
    (BitPairFraming.frame input cert).reverse [])
  have count : (input.length + cert.length + 2 + tail.length) + 1 =
      (literalPair input cert ++ none :: tail).length + 1 := by
    rw [repeated_length]
    omega
  exact run_count count (run_trans drained emptyProbe)

theorem repeated_work_prefix (initial : R) (input cert : Bits) (tail : Raw)
    (n : Nat) (within : n ≤ (BitPairFraming.frame input cert).length) :
    next^[(literalPair input cert ++ none :: tail).length + 1 + n]
        (some (Turing.initList (machine initial) (literalPair input cert ++ none :: tail))) =
      some (state .drainWork initial
        (lastBitPop none ((BitPairFraming.frame input cert).reverse.take n)) []
        ((BitPairFraming.frame input cert).reverse.drop n) []) := by
  have hrev : n ≤ (BitPairFraming.frame input cert).reverse.length := by
    simpa only [List.length_reverse] using within
  exact run_trans (repeated_work_entry initial input cert tail)
    (drain_work_take initial none (BitPairFraming.frame input cert).reverse n hrev)

theorem repeated_handoff (initial : R) (input cert : Bits) (tail : Raw) :
    next^[preludeSteps (literalPair input cert ++ none :: tail)]
        (some (Turing.initList (machine initial) (literalPair input cert ++ none :: tail))) =
      some (Turing.initList (oldMachine initial) []) := by
  have composed := run_trans (repeated_work_entry initial input cert tail)
    (drain_work_finish initial none (BitPairFraming.frame input cert).reverse)
  have count : ((literalPair input cert ++ none :: tail).length + 1) +
      ((BitPairFraming.frame input cert).reverse.length + 1) =
      preludeSteps (literalPair input cert ++ none :: tail) := by
    rw [List.length_reverse, preludeSteps_repeated_frame]
    omega
  exact run_count count composed

/-- Actual native handoff for every raw word, assembled from the real loops. -/
theorem prelude_handoff (initial : R) (raw : Raw) :
    next^[preludeSteps raw] (some (Turing.initList (machine initial) raw)) =
      some (Turing.initList (oldMachine initial) (handoffWord raw)) := by
  rcases protocol_cases raw with ⟨input, rfl⟩ | ⟨input, cert, rfl⟩ | ⟨input, cert, tail, rfl⟩
  · exact (missing_handoff initial input).trans
      (old_init_word_congr initial [] (handoffWord (input.map some))
        (handoffWord_missing input).symm)
  · exact (valid_handoff initial input cert).trans
      (old_init_word_congr initial (BitPairFraming.frame input cert)
        (handoffWord (literalPair input cert)) (handoffWord_pair input cert).symm)
  · exact (repeated_handoff initial input cert tail).trans
      (old_init_word_congr initial [] (handoffWord (literalPair input cert ++ none :: tail))
        (handoffWord_repeated input cert tail).symm)

theorem handoff_obligation : HandoffObligation (R := R) := prelude_handoff

end FinitePackage

end Resources.RotationCertificate.DelimiterMachine.Execution

end

/- Complete preserved component: prefix_composition. -/
section

namespace Resources.RotationCertificate.DelimiterMachine.Execution

open Resources.BinaryCounter (Bits)

variable {R : Type} [Fintype R]

def BoundaryWitness (initial : R) (raw : Raw) (n : Nat) : Prop :=
  ∃ reached, next^[n] (some (Turing.initList (machine initial) raw)) = some reached ∧
    PreludeInvariant initial raw n reached

theorem prefix_witness (initial : R) (input : Bits) (tail : Raw)
    (n : Nat) (within : n ≤ input.length) :
    BoundaryWitness initial (input.map some ++ tail) n := by
  refine ⟨_, prefix_from_init initial input tail n within, ?_⟩
  simpa only [List.length_take, Nat.min_eq_left within] using
    (PreludeInvariant.prefix (initial := initial) (raw := input.map some ++ tail)
      (input.take n) ((input.drop n).map some ++ tail) (bits_split_append input tail n))

theorem certificate_witness (initial : R) (input cert : Bits) (tail : Raw)
    (n : Nat) (within : n ≤ cert.length) :
    BoundaryWitness initial (literalPair input cert ++ tail) (input.length + 1 + n) := by
  refine ⟨_, certificate_prefix initial input cert tail n within, ?_⟩
  simpa only [List.length_take, Nat.min_eq_left within] using
    (PreludeInvariant.certificate (initial := initial) (raw := literalPair input cert ++ tail)
      input (cert.take n) ((cert.drop n).map some ++ tail) (pair_split_append input cert tail n))

theorem reverse_witness (initial : R) (input cert : Bits) (n : Nat)
    (within : n ≤ (BitPairFraming.frame input cert).length) :
    BoundaryWitness initial (literalPair input cert) ((literalPair input cert).length + 1 + n) := by
  exact ⟨_, valid_reverse_prefix initial input cert n within,
    PreludeInvariant.reverse input cert n rfl within⟩

theorem drain_input_witness (initial : R) (input cert : Bits) (tail : Raw)
    (n : Nat) (within : n ≤ tail.length) :
    BoundaryWitness initial (literalPair input cert ++ none :: tail)
      (input.length + cert.length + 2 + n) := by
  exact ⟨_, repeated_input_prefix initial input cert tail n within,
    PreludeInvariant.drainInput input cert tail n rfl within⟩

theorem drain_missing_witness (initial : R) (input : Bits) (n : Nat)
    (within : n ≤ (BitPairFraming.escapeBits input).length) :
    BoundaryWitness initial (input.map some) (input.length + 1 + n) := by
  refine ⟨_, missing_drain_prefix initial input n within, ?_⟩
  simpa only [List.length_map] using
    (PreludeInvariant.drainMissing (initial := initial) (raw := input.map some) input n rfl within)

theorem drain_repeated_witness (initial : R) (input cert : Bits) (tail : Raw)
    (n : Nat) (within : n ≤ (BitPairFraming.frame input cert).length) :
    BoundaryWitness initial (literalPair input cert ++ none :: tail)
      ((literalPair input cert ++ none :: tail).length + 1 + n) := by
  exact ⟨_, repeated_work_prefix initial input cert tail n within,
    PreludeInvariant.drainRepeated input cert tail n rfl within⟩

theorem handoff_invariant (initial : R) (raw : Raw) :
    PreludeInvariant initial raw (preludeSteps raw)
      (Turing.initList (oldMachine initial) (handoffWord raw)) := by
  rcases protocol_cases raw with ⟨input, rfl⟩ | ⟨input, cert, rfl⟩ | ⟨input, cert, tail, rfl⟩
  · have count : (input.map some : Raw).length + 2 * input.length + 2 =
        preludeSteps (input.map some) := by
      rw [List.length_map, preludeSteps_missing]
      omega
    have timed : PreludeInvariant initial (input.map some) (preludeSteps (input.map some))
        (Turing.initList (oldMachine initial) [] : Cfg R) :=
      count ▸ (PreludeInvariant.handoffMissing (initial := initial)
        (raw := input.map some) input rfl)
    have transported := congrArg
      (fun word : Bits => PreludeInvariant initial (input.map some)
        (preludeSteps (input.map some)) (Turing.initList (oldMachine initial) word : Cfg R))
      (handoffWord_missing input)
    exact transported.mpr timed
  · have timed : PreludeInvariant initial (literalPair input cert)
        (preludeSteps (literalPair input cert))
        (Turing.initList (oldMachine initial) (BitPairFraming.frame input cert) : Cfg R) :=
      (preludeSteps_pair_frame input cert).symm ▸
        (PreludeInvariant.handoffValid (initial := initial) (raw := literalPair input cert)
          input cert rfl)
    have transported := congrArg
      (fun word : Bits => PreludeInvariant initial (literalPair input cert)
        (preludeSteps (literalPair input cert))
        (Turing.initList (oldMachine initial) word : Cfg R)) (handoffWord_pair input cert)
    exact transported.mpr timed
  · have timed : PreludeInvariant initial (literalPair input cert ++ none :: tail)
        (preludeSteps (literalPair input cert ++ none :: tail))
        (Turing.initList (oldMachine initial) [] : Cfg R) :=
      (preludeSteps_repeated_frame input cert tail).symm ▸
        (PreludeInvariant.handoffRepeated (initial := initial)
          (raw := literalPair input cert ++ none :: tail) input cert tail rfl)
    have transported := congrArg
      (fun word : Bits => PreludeInvariant initial (literalPair input cert ++ none :: tail)
        (preludeSteps (literalPair input cert ++ none :: tail))
        (Turing.initList (oldMachine initial) word : Cfg R))
      (handoffWord_repeated input cert tail)
    exact transported.mpr timed

theorem handoff_witness (initial : R) (raw : Raw) :
    BoundaryWitness initial raw (preludeSteps raw) :=
  ⟨_, prelude_handoff initial raw, handoff_invariant initial raw⟩

/-- Every inclusive native prefix is one of the exact complete-state rows.
The phase split uses the independently fixed clocks from the actual loops. -/
theorem prelude_boundary (initial : R) (raw : Raw) (n : Nat)
    (within : n ≤ preludeSteps raw) : BoundaryWitness initial raw n := by
  by_cases final : n = preludeSteps raw
  · subst n
    exact handoff_witness initial raw
  have strict : n < preludeSteps raw := by omega
  rcases protocol_cases raw with ⟨input, rfl⟩ | ⟨input, cert, rfl⟩ | ⟨input, cert, tail, rfl⟩
  · by_cases prefixPart : n ≤ input.length
    · simpa only [List.append_nil] using prefix_witness initial input [] n prefixPart
    · have work : n - (input.length + 1) ≤ (BitPairFraming.escapeBits input).length := by
        rw [BitPairFraming.escapeBits_length]
        rw [preludeSteps_missing] at strict
        omega
      have count : input.length + 1 + (n - (input.length + 1)) = n := by omega
      simpa only [count] using
        drain_missing_witness initial input (n - (input.length + 1)) work
  · by_cases prefixPart : n ≤ input.length
    · simpa only [literalPair, List.append_assoc, List.singleton_append] using
        prefix_witness initial input (none :: cert.map some) n prefixPart
    · by_cases certPart : n ≤ input.length + 1 + cert.length
      · have suffix : n - (input.length + 1) ≤ cert.length := by omega
        have count : input.length + 1 + (n - (input.length + 1)) = n := by omega
        simpa only [List.append_nil, count] using
          certificate_witness initial input cert [] (n - (input.length + 1)) suffix
      · have lengthEq := literalPair_length input cert
        have start : (literalPair input cert).length + 1 ≤ n := by omega
        have work : n - ((literalPair input cert).length + 1) ≤
            (BitPairFraming.frame input cert).length := by
          rw [preludeSteps_pair_frame] at strict
          omega
        have count : (literalPair input cert).length + 1 +
            (n - ((literalPair input cert).length + 1)) = n := by omega
        simpa only [count] using reverse_witness initial input cert
          (n - ((literalPair input cert).length + 1)) work
  · by_cases prefixPart : n ≤ input.length
    · simpa only [literalPair, List.append_assoc, List.cons_append, List.nil_append] using
        prefix_witness initial input (none :: (cert.map some ++ none :: tail)) n prefixPart
    · by_cases certPart : n ≤ input.length + 1 + cert.length
      · have suffix : n - (input.length + 1) ≤ cert.length := by omega
        have count : input.length + 1 + (n - (input.length + 1)) = n := by omega
        simpa only [count] using certificate_witness initial input cert (none :: tail)
          (n - (input.length + 1)) suffix
      · by_cases inputPart : n ≤ input.length + cert.length + 2 + tail.length
        · have suffix : n - (input.length + cert.length + 2) ≤ tail.length := by omega
          have count : input.length + cert.length + 2 +
              (n - (input.length + cert.length + 2)) = n := by omega
          simpa only [count] using drain_input_witness initial input cert tail
            (n - (input.length + cert.length + 2)) suffix
        · have lengthEq := repeated_length input cert tail
          have start : (literalPair input cert ++ none :: tail).length + 1 ≤ n := by omega
          have work : n - ((literalPair input cert ++ none :: tail).length + 1) ≤
              (BitPairFraming.frame input cert).length := by
            rw [preludeSteps_repeated_frame] at strict
            omega
          have count : (literalPair input cert ++ none :: tail).length + 1 +
              (n - ((literalPair input cert ++ none :: tail).length + 1)) = n := by omega
          simpa only [count] using drain_repeated_witness initial input cert tail
            (n - ((literalPair input cert ++ none :: tail).length + 1)) work

theorem callerContext_cells (raw : Raw) (work : Bits) :
    FrontEndStreamMachine.contextCells (callerContext raw work) = raw.length + work.length := by
  change (∑ k ∈ ({.input, .work} : Finset CallerStore), (callerContext raw work k).length) = _
  simp [callerContext]

omit [Fintype R] in
theorem state_stackCells (q : CallerPhase) (initial : R) (seen : Scratch)
    (raw : Raw) (work framed : Bits) :
    FrontEndStreamMachine.stackCells (state q initial seen raw work framed) =
      raw.length + work.length + framed.length := by
  rw [state, FrontEndStreamMachine.stackCells_cfg, callerContext_cells]
  simp only [FrontEndStreamMachine.localCells, List.length_nil, Nat.add_zero]
  omega

theorem old_init_stackCells (initial : R) (framed : Bits) :
    FrontEndStreamMachine.stackCells (Turing.initList (oldMachine initial) framed) = framed.length := by
  have transported := congrArg (fun c : Cfg R => FrontEndStreamMachine.stackCells c)
    (oldMachine_initList_eq initial framed)
  calc
    FrontEndStreamMachine.stackCells (Turing.initList (oldMachine initial) framed) =
        FrontEndStreamMachine.stackCells
          (FrontEndStreamMachine.cfg (some oldMain)
            (FrontEndStreamMachine.initialRegisters (none, initial))
            { framedRaw := framed } (callerContext [] [])) := transported
    _ = framed.length := by
      rw [FrontEndStreamMachine.stackCells_cfg, callerContext_cells]
      simp only [FrontEndStreamMachine.localCells, List.length_nil, Nat.add_zero]

/-- Physical total occupancy follows from the complete invariant, including
the actual input/work stores and all sixteen original stores. -/
theorem invariant_stackCells (initial : R) (raw : Raw) (n : Nat) (reached : Cfg R)
    (shape : PreludeInvariant initial raw n reached) :
    FrontEndStreamMachine.stackCells reached ≤ 2 * raw.length := by
  cases shape with
  | «prefix» before rest whole =>
      have hlength := congrArg List.length whole
      simp only [List.length_map, List.length_append] at hlength
      simp only [state_stackCells, List.length_reverse, BitPairFraming.escapeBits_length,
        List.length_nil]
      omega
  | certificate input before rest whole =>
      have hlength := congrArg List.length whole
      simp only [List.length_append, literalPair_length] at hlength
      simp only [state_stackCells, List.length_reverse, BitPairFraming.frame_length,
        List.length_nil]
      omega
  | reverse input cert j whole within =>
      have hlength := congrArg List.length whole
      rw [literalPair_length] at hlength
      have frameLength := BitPairFraming.frame_length input cert
      simp only [state_stackCells, List.length_nil, List.length_reverse, List.length_drop,
        List.length_take, Nat.min_eq_left within]
      omega
  | drainInput input cert tail j whole within =>
      have hlength := congrArg List.length whole
      simp only [List.length_append, literalPair_length, List.length_cons] at hlength
      simp only [state_stackCells, List.length_drop, List.length_reverse,
        BitPairFraming.frame_length, List.length_nil]
      omega
  | drainMissing input j whole within =>
      have hlength := congrArg List.length whole
      rw [List.length_map] at hlength
      simp only [state_stackCells, List.length_nil, List.length_drop, List.length_reverse,
        BitPairFraming.escapeBits_length]
      omega
  | drainRepeated input cert tail j whole within =>
      have hlength := congrArg List.length whole
      simp only [List.length_append, literalPair_length, List.length_cons] at hlength
      simp only [state_stackCells, List.length_nil, List.length_drop, List.length_reverse,
        BitPairFraming.frame_length]
      omega
  | handoffValid input cert whole =>
      have hlength := congrArg List.length whole
      rw [literalPair_length] at hlength
      rw [old_init_stackCells, BitPairFraming.frame_length]
      omega
  | handoffMissing input whole =>
      have emptyCells : FrontEndStreamMachine.stackCells
          (Turing.initList (oldMachine initial) ([] : Bits) : Cfg R) = 0 :=
        old_init_stackCells initial []
      exact emptyCells.le.trans (Nat.zero_le _)
  | handoffRepeated input cert tail whole =>
      have emptyCells : FrontEndStreamMachine.stackCells
          (Turing.initList (oldMachine initial) ([] : Bits) : Cfg R) = 0 :=
        old_init_stackCells initial []
      exact emptyCells.le.trans (Nat.zero_le _)

/-- The original proposed prefix proposition is supplied by actual loop runs
and the complete invariant, not by the independent reference model. -/
theorem prefix_obligation : PrefixObligation (R := R) := by
  intro initial raw n within
  obtain ⟨reached, executed, shape⟩ := prelude_boundary initial raw n within
  exact ⟨reached, executed, shape, invariant_stackCells initial raw n reached shape⟩

theorem prelude_prefix_cells (initial : R) (raw : Raw) (n : Nat)
    (within : n ≤ preludeSteps raw) (reached : Cfg R)
    (executed : next^[n] (some (Turing.initList (machine initial) raw)) = some reached) :
    FrontEndStreamMachine.stackCells reached ≤ 2 * raw.length := by
  obtain ⟨actual, actualRun, _, cells⟩ := prefix_obligation initial raw n within
  have same : actual = reached := Option.some.inj (actualRun.symm.trans executed)
  simpa only [same] using cells

/-- Literal complete native run: paid preprocessing followed by the old
genuine initializer theorem on the exact word produced by preprocessing. -/
theorem total_iterate (initial : R) (raw : Raw) :
    next^[totalSourceSteps raw] (some (Turing.initList (machine initial) raw)) =
      some (Turing.haltList (machine initial) [verifyDelimited raw]) := by
  have suffix : next^[FrontEndStreamMachine.runSteps (handoffWord raw)]
      (some (Turing.initList (oldMachine initial) (handoffWord raw))) =
      some (Turing.haltList (oldMachine initial)
        [BitPairFraming.verifyFramed (handoffWord raw)]) :=
    FrontEndStreamMachine.init_iterate caller (none, initial) (handoffWord raw)
  have answerEq := congrArg (fun b : Bool => [b]) (verifyFramed_handoffWord raw)
  have oldAnswer := congrArg
    (fun word : Bits => (Turing.haltList (oldMachine initial) word : Cfg R)) answerEq
  have endpoint := congrArg (fun c : Cfg R => some c)
    (oldAnswer.trans (haltList_eq_old initial [verifyDelimited raw]).symm)
  exact (run_trans (prelude_handoff initial raw) suffix).trans endpoint

/-- The source time polynomial follows from the real prelude clock and the
existing universal controller bound. No input-validity premise is needed. -/
theorem totalSourceSteps_le (raw : Raw) : totalSourceSteps raw ≤ sourceTimeBound raw.length := by
  have prelude := preludeSteps_le raw
  have controller := FrontEndStreamMachine.runSteps_le (handoffWord raw)
  have lengthBound := handoffWord_length_le raw
  have squareBound := Nat.mul_le_mul lengthBound lengthBound
  unfold totalSourceSteps sourceTimeBound
  nlinarith

/-- Compose the actual old peak theorem after the proved complete handoff.
Every reached configuration, including live halt, has bounded total occupancy. -/
theorem total_prefix_cells (initial : R) (raw : Raw) :
    FrontEndStreamMachine.PrefixProperty caller
      (fun c => FrontEndStreamMachine.stackCells c ≤ max (2 * raw.length) 1)
      (Turing.initList (machine initial) raw) (totalSourceSteps raw) := by
  have before : FrontEndStreamMachine.PrefixProperty caller
      (fun c => FrontEndStreamMachine.stackCells c ≤ max (2 * raw.length) 1)
      (Turing.initList (machine initial) raw) (preludeSteps raw) := by
    intro n within reached executed
    exact (prelude_prefix_cells initial raw n within reached executed).trans (Nat.le_max_left _ _)
  have after : FrontEndStreamMachine.PrefixProperty caller
      (fun c => FrontEndStreamMachine.stackCells c ≤ max (2 * raw.length) 1)
      (Turing.initList (oldMachine initial) (handoffWord raw))
      (FrontEndStreamMachine.runSteps (handoffWord raw)) := by
    intro n within reached executed
    have bound : FrontEndStreamMachine.stackCells reached ≤ max (handoffWord raw).length 1 :=
      (FrontEndStreamMachine.init_peak caller (none, initial) (handoffWord raw)).1
        n within reached executed
    exact bound.trans (max_le_max (handoffWord_length_le raw) (Nat.le_refl 1))
  exact FrontEndStreamMachine.PrefixProperty.trans caller (prelude_handoff initial raw) before after

def outputsInTime (initial : R) (raw : Raw) :
    Turing.TM2OutputsInTime (machine initial) raw (some [verifyDelimited raw])
      (sourceTimeBound raw.length) where
  steps := totalSourceSteps raw
  evals_in_steps := total_iterate initial raw
  steps_le_m := totalSourceSteps_le raw

theorem outputsInTime_steps (initial : R) (raw : Raw) :
    (outputsInTime initial raw).steps = totalSourceSteps raw := rfl

theorem total_outer_none (initial : R) (raw : Raw) :
    next^[totalSourceSteps raw + 1] (some (Turing.initList (machine initial) raw)) = none := by
  rw [Function.iterate_succ_apply', total_iterate]
  rfl

theorem literal_pair_output (initial : R) (input cert : Bits) :
    next^[totalSourceSteps (literalPair input cert)]
        (some (Turing.initList (machine initial) (literalPair input cert))) =
      some (Turing.haltList (machine initial) [(verifyBitsRun input cert).1]) := by
  have endpoint := congrArg
    (fun b : Bool => (some (Turing.haltList (machine initial) [b]) : Option (Cfg R)))
    (verifyDelimited_pair input cert)
  exact (total_iterate initial (literalPair input cert)).trans endpoint

theorem malformed_output (initial : R) (raw : Raw) (malformed : splitLiteral raw = none) :
    next^[totalSourceSteps raw] (some (Turing.initList (machine initial) raw)) =
      some (Turing.haltList (machine initial) [false]) := by
  have answerEq : verifyDelimited raw = false := by rw [verifyDelimited, malformed]
  have endpoint := congrArg
    (fun b : Bool => (some (Turing.haltList (machine initial) [b]) : Option (Cfg R))) answerEq
  exact (total_iterate initial raw).trans endpoint

end Resources.RotationCertificate.DelimiterMachine.Execution

end
