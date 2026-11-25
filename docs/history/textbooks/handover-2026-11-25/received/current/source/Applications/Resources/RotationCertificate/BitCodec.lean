import Applications.Resources.RotationCertificate.Encoding
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Actual fixed-four-bit rotation-certificate codec

Every tag has a four-bit, least-significant-bit-first code, including the five
reserved syntax tags. Actual packing constructs four conses by finite dispatch;
actual complete unpacking consumes four list heads at a time. An incomplete
final block fails before any preceding block is decoded during the unwind.

The declared tariff charges one entry/dispatch per primitive, one per new cons,
and one per returned Option constructor. Boolean payloads in bit conses and
finite tag constants add no separate result charge. Thus tag packing costs five
and tag decoding costs one. The complete decoder reads the entire raw suffix;
its failure equations do not assert an untouched bit tail. These observations
are source-event costs, not a computational-model simulation or an NP result.
Correspondence: `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate
open Resources.BinaryCounter (Bits value)
open Trees.Rotations (RotationMove)

/-- Independent fixed-width code; displayed list order is least significant first. -/
def tagBits (tag : Tag) : Bits :=
  match tag.val with
  | 0 => [false, false, false, false]
  | 1 => [true, false, false, false]
  | 2 => [false, true, false, false]
  | 3 => [true, true, false, false]
  | 4 => [false, false, true, false]
  | 5 => [true, false, true, false]
  | 6 => [false, true, true, false]
  | 7 => [true, true, true, false]
  | 8 => [false, false, false, true]
  | 9 => [true, false, false, true]
  | 10 => [false, true, false, true]
  | 11 => [true, true, false, true]
  | 12 => [false, false, true, true]
  | 13 => [true, false, true, true]
  | 14 => [false, true, true, true]
  | _ => [true, true, true, true]

@[simp] theorem tagBits_length (tag : Tag) : (tagBits tag).length = 4 := by
  fin_cases tag <;> rfl

/-- Numeric meaning is a theorem about the table, not an executable decoder. -/
theorem tagBits_value (tag : Tag) : value (tagBits tag) = tag.val := by
  fin_cases tag <;> rfl

def wordBits : Word → Bits
  | [] => []
  | tag :: word => tagBits tag ++ wordBits word

@[simp] theorem wordBits_nil : wordBits [] = [] := rfl

@[simp] theorem wordBits_cons (tag : Tag) (word : Word) :
    wordBits (tag :: word) = tagBits tag ++ wordBits word := rfl

@[simp] theorem wordBits_length (word : Word) :
    (wordBits word).length = 4 * word.length := by
  induction word with
  | nil => rfl
  | cons tag word ih => simp [ih, Nat.mul_add, Nat.add_comm]

theorem wordBits_append (left right : Word) :
    wordBits (left ++ right) = wordBits left ++ wordBits right := by
  induction left with
  | nil => rfl
  | cons tag left ih => simp only [List.cons_append, wordBits_cons, ih, List.append_assoc]

/-- One finite dispatch and four actual conses onto the supplied suffix. -/
def packTagRun (tag : Tag) (suffix : Bits) : Measured Bits Nat :=
  match tag.val with
  | 0 => (false :: false :: false :: false :: suffix, 5)
  | 1 => (true :: false :: false :: false :: suffix, 5)
  | 2 => (false :: true :: false :: false :: suffix, 5)
  | 3 => (true :: true :: false :: false :: suffix, 5)
  | 4 => (false :: false :: true :: false :: suffix, 5)
  | 5 => (true :: false :: true :: false :: suffix, 5)
  | 6 => (false :: true :: true :: false :: suffix, 5)
  | 7 => (true :: true :: true :: false :: suffix, 5)
  | 8 => (false :: false :: false :: true :: suffix, 5)
  | 9 => (true :: false :: false :: true :: suffix, 5)
  | 10 => (false :: true :: false :: true :: suffix, 5)
  | 11 => (true :: true :: false :: true :: suffix, 5)
  | 12 => (false :: false :: true :: true :: suffix, 5)
  | 13 => (true :: false :: true :: true :: suffix, 5)
  | 14 => (false :: true :: true :: true :: suffix, 5)
  | _ => (true :: true :: true :: true :: suffix, 5)

theorem packTagRun_eq (tag : Tag) (suffix : Bits) :
    packTagRun tag suffix = (tagBits tag ++ suffix, 5) := by
  fin_cases tag <;> rfl

/-- Pack the actual recursive result; the mathematical append code is not run. -/
def packWordRun : Word → Bits → Measured Bits Nat
  | [], suffix => (suffix, 1)
  | tag :: word, suffix =>
      CallCount.tick (bind (packWordRun word suffix) (fun tail => packTagRun tag tail))

theorem packWordRun_eq (word : Word) (suffix : Bits) :
    packWordRun word suffix = (wordBits word ++ suffix, 6 * word.length + 1) := by
  induction word with
  | nil => rfl
  | cons tag word ih =>
      simp only [packWordRun, ih, packTagRun_eq, CallCount.tick, bind,
        wordBits_cons, List.append_assoc, List.length_cons]
      congr 1

@[simp] theorem packWordRun_value (word : Word) (suffix : Bits) :
    (packWordRun word suffix).1 = wordBits word ++ suffix := by rw [packWordRun_eq]

@[simp] theorem packWordRun_cost (word : Word) (suffix : Bits) :
    (packWordRun word suffix).2 = 6 * word.length + 1 := by rw [packWordRun_eq]

/-- Exhaustive finite dispatch preserves all sixteen tags, including reserved ones. -/
def decodeTagRun : Bool → Bool → Bool → Bool → Measured Tag Nat
  | false, false, false, false => (0, 1)
  | true, false, false, false => (1, 1)
  | false, true, false, false => (2, 1)
  | true, true, false, false => (3, 1)
  | false, false, true, false => (4, 1)
  | true, false, true, false => (5, 1)
  | false, true, true, false => (6, 1)
  | true, true, true, false => (7, 1)
  | false, false, false, true => (8, 1)
  | true, false, false, true => (9, 1)
  | false, true, false, true => (10, 1)
  | true, true, false, true => (11, 1)
  | false, false, true, true => (12, 1)
  | true, false, true, true => (13, 1)
  | false, true, true, true => (14, 1)
  | true, true, true, true => (15, 1)

@[simp] theorem decodeTagRun_cost (b0 b1 b2 b3 : Bool) :
    (decodeTagRun b0 b1 b2 b3).2 = 1 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl

theorem decodeTagRun_value (b0 b1 b2 b3 : Bool) :
    (decodeTagRun b0 b1 b2 b3).1.val = value [b0, b1, b2, b3] := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl

@[simp] theorem tagBits_decodeTagRun (b0 b1 b2 b3 : Bool) :
    tagBits (decodeTagRun b0 b1 b2 b3).1 = [b0, b1, b2, b3] := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl

/-- Decode the complete suffix before constructing this block's tag and Option. -/
def unpackWordRun : Bits → Measured (Option Word) Nat
  | [] => (some [], 2)
  | [_] => (none, 2)
  | [_, _] => (none, 2)
  | [_, _, _] => (none, 2)
  | b0 :: b1 :: b2 :: b3 :: raw =>
      CallCount.tick (bind (unpackWordRun raw) (fun result => match result with
        | none => (none, 1)
        | some word => bind (decodeTagRun b0 b1 b2 b3)
            (fun tag => (some (tag :: word), 2))))

@[simp] theorem unpackWordRun_nil : unpackWordRun [] = (some [], 2) := rfl

theorem unpackWordRun_cons4 (b0 b1 b2 b3 : Bool) (raw : Bits) :
    unpackWordRun (b0 :: b1 :: b2 :: b3 :: raw) =
      match unpackWordRun raw with
      | (none, cost) => (none, cost + 2)
      | (some word, cost) =>
          (some ((decodeTagRun b0 b1 b2 b3).1 :: word), cost + 4) := by
  simp only [unpackWordRun, CallCount.tick, bind]
  cases returned : unpackWordRun raw with
  | mk result cost => cases result with
    | none => rfl
    | some word => simp only [decodeTagRun_cost]

/-- A finite table block preserves arbitrary successful or failed continuation. -/
theorem unpackWordRun_tagBits (tag : Tag) (raw : Bits) :
    unpackWordRun (tagBits tag ++ raw) =
      match unpackWordRun raw with
      | (none, cost) => (none, cost + 2)
      | (some word, cost) => (some (tag :: word), cost + 4) := by
  fin_cases tag <;> simp only [tagBits, List.cons_append, List.nil_append,
    unpackWordRun_cons4, decodeTagRun] <;> rfl

/-- A whole encoded prefix transports both outcomes of an arbitrary raw suffix. -/
theorem unpackWordRun_prefix (pref : Word) (raw : Bits) :
    unpackWordRun (wordBits pref ++ raw) =
      match unpackWordRun raw with
      | (none, cost) => (none, cost + 2 * pref.length)
      | (some suffix, cost) => (some (pref ++ suffix), cost + 4 * pref.length) := by
  induction pref with
  | nil =>
      cases returned : unpackWordRun raw with
      | mk result cost => cases result <;> simp [returned]
  | cons tag pref ih =>
      rw [wordBits_cons, List.append_assoc, unpackWordRun_tagBits, ih]
      cases returned : unpackWordRun raw with
      | mk result cost => cases result <;> simp [Nat.mul_add, Nat.add_assoc]

theorem unpackWordRun_code (word : Word) :
    unpackWordRun (wordBits word) = (some word, 4 * word.length + 2) := by
  simpa only [List.append_nil, unpackWordRun_nil, Nat.add_comm] using
    unpackWordRun_prefix word []

/-- Complete recognition, in the direction that covers arbitrary raw bits. -/
theorem unpackWordRun_sound (raw : Bits) (word : Word)
    (returned : (unpackWordRun raw).1 = some word) : raw = wordBits word := by
  induction raw using unpackWordRun.induct generalizing word with
  | case1 =>
      simp only [unpackWordRun_nil, Option.some.injEq] at returned
      subst word
      rfl
  | case2 b => cases returned
  | case3 b0 b1 => cases returned
  | case4 b0 b1 b2 => cases returned
  | case5 b0 b1 b2 b3 raw ih =>
      rw [unpackWordRun_cons4] at returned
      cases tailResult : unpackWordRun raw with
      | mk result cost =>
          rw [tailResult] at returned
          cases result with
          | none => cases returned
          | some suffix =>
              have suffixCode := ih suffix (congrArg Prod.fst tailResult)
              have wordEq := Option.some.inj returned
              rw [← wordEq, wordBits_cons, tagBits_decodeTagRun, ← suffixCode]
              rfl

/-- There are no extra accepted raw words and no normalization of zero bits. -/
theorem unpackWordRun_iff (raw : Bits) (word : Word) :
    (unpackWordRun raw).1 = some word ↔ raw = wordBits word := by
  constructor
  · exact unpackWordRun_sound raw word
  · intro encoded
    rw [encoded, unpackWordRun_code]

theorem wordBits_injective : Function.Injective wordBits := by
  intro left right equal
  have returned : (unpackWordRun (wordBits left)).1 = some right := by
    rw [equal, unpackWordRun_code]
  rw [unpackWordRun_code] at returned
  exact Option.some.inj returned

/-- Every complete block is valid, so only the final partial block causes failure. -/
theorem unpackWordRun_none_iff (raw : Bits) :
    (unpackWordRun raw).1 = none ↔ raw.length % 4 ≠ 0 := by
  induction raw using unpackWordRun.induct with
  | case1 => simp [unpackWordRun]
  | case2 b => simp [unpackWordRun]
  | case3 b0 b1 => simp [unpackWordRun]
  | case4 b0 b1 b2 => simp [unpackWordRun]
  | case5 b0 b1 b2 b3 raw ih =>
      have sameRemainder : (b0 :: b1 :: b2 :: b3 :: raw).length % 4 =
          raw.length % 4 := by
        simp only [List.length_cons]
        omega
      rw [sameRemainder, ← ih, unpackWordRun_cons4]
      cases returned : unpackWordRun raw with
      | mk result cost => cases result <;> simp

theorem unpackWordRun_short (raw : Bits) (positive : 0 < raw.length)
    (incomplete : raw.length < 4) : unpackWordRun raw = (none, 2) := by
  cases raw with
  | nil => simp only [List.length_nil] at positive; omega
  | cons b0 raw => cases raw with
    | nil => rfl
    | cons b1 raw => cases raw with
      | nil => rfl
      | cons b2 raw => cases raw with
        | nil => rfl
        | cons b3 raw => simp only [List.length_cons] at incomplete; omega

/-- Exact failure cost for any number of complete blocks and any partial final one. -/
theorem unpackWordRun_partial (word : Word) (short : Bits)
    (positive : 0 < short.length) (incomplete : short.length < 4) :
    unpackWordRun (wordBits word ++ short) = (none, 2 * word.length + 2) := by
  simpa only [unpackWordRun_short short positive incomplete, Nat.add_comm] using
    unpackWordRun_prefix word short

/-- Universal raw-bit cost, including every incomplete final-block failure. -/
theorem unpackWordRun_cost_le (raw : Bits) :
    (unpackWordRun raw).2 ≤ raw.length + 2 := by
  induction raw using unpackWordRun.induct with
  | case1 => decide
  | case2 b => simp [unpackWordRun]
  | case3 b0 b1 => simp [unpackWordRun]
  | case4 b0 b1 b2 => simp [unpackWordRun]
  | case5 b0 b1 b2 b3 raw ih =>
      rw [unpackWordRun_cons4]
      cases returned : unpackWordRun raw with
      | mk result cost =>
          rw [returned] at ih
          cases result <;> simp only [List.length_cons] at ih ⊢ <;> omega

/-- Actual packing followed by actual unpacking has an exact combined observation. -/
theorem pack_unpack_eq (word : Word) :
    bind (packWordRun word []) unpackWordRun = (some word, 10 * word.length + 3) := by
  rw [packWordRun_eq]
  simp only [List.append_nil, bind, unpackWordRun_code]
  congr 1
  omega

/-- Repacking any successfully decoded raw word reproduces every original bit. -/
theorem packWordRun_of_unpacked (raw : Bits) (word : Word)
    (returned : (unpackWordRun raw).1 = some word) :
    packWordRun word [] = (raw, 6 * word.length + 1) := by
  rw [packWordRun_eq, List.append_nil, (unpackWordRun_iff raw word).1 returned]

/-- Free nonrecursive composition of the actual input emitter and actual packer. -/
def emitPackedInputRun (source target : BinaryTree Unit) (bs : Bits) :
    Measured Bits Nat :=
  bind (emitInputRun source target bs) (fun word => packWordRun word [])

/-- Free nonrecursive composition; certificate construction feeds actual packing. -/
def emitPackedCertificateRun (moves : List RotationMove) : Measured Bits Nat :=
  bind (emitCertificateRun moves []) (fun word => packWordRun word [])

theorem emitPackedInputRun_eq (source target : BinaryTree Unit) (bs : Bits) :
    emitPackedInputRun source target bs =
      (wordBits (inputCode source target bs), 8 * (inputCode source target bs).length) := by
  have cost := emitInputRun_cost_add_one source target bs
  simp only [emitPackedInputRun, bind, packWordRun_value, packWordRun_cost,
    emitInputRun_value, List.append_nil]
  congr 1
  omega

theorem emitPackedCertificateRun_eq (moves : List RotationMove) :
    emitPackedCertificateRun moves =
      (wordBits (certCode moves), 8 * (certCode moves).length + 2) := by
  simp only [emitPackedCertificateRun, bind, packWordRun_value, packWordRun_cost,
    emitCertificateRun_value, emitCertificateRun_cost, List.append_nil]
  congr 1
  omega

@[simp] theorem emitPackedInputRun_value (source target : BinaryTree Unit) (bs : Bits) :
    (emitPackedInputRun source target bs).1 = wordBits (inputCode source target bs) := by
  rw [emitPackedInputRun_eq]

@[simp] theorem emitPackedInputRun_cost (source target : BinaryTree Unit) (bs : Bits) :
    (emitPackedInputRun source target bs).2 = 8 * (inputCode source target bs).length := by
  rw [emitPackedInputRun_eq]

@[simp] theorem emitPackedCertificateRun_value (moves : List RotationMove) :
    (emitPackedCertificateRun moves).1 = wordBits (certCode moves) := by
  rw [emitPackedCertificateRun_eq]

@[simp] theorem emitPackedCertificateRun_cost (moves : List RotationMove) :
    (emitPackedCertificateRun moves).2 = 8 * (certCode moves).length + 2 := by
  rw [emitPackedCertificateRun_eq]

end Resources.RotationCertificate
