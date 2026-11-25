import Protocol144b

/-!
Actual native TM2 loop composition for the frozen delimiter prelude.
UNCOMPILED repair2. The twelve local transition lemmas are implementation dependencies
from DelimiterPrelude144; every larger run below is constructed by induction
and optional-iteration composition. No run/time premise is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.DelimiterPreludeDraft.GeneralProof1

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

end Resources.RotationCertificate.DelimiterPreludeDraft.GeneralProof1
