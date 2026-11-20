import Applications.Sorting.DecodedInsertion
import Examples.InsertionSorting

/-!
# Source sorting programs through proved signed comparisons

These are the Nat, mathematical-Int and abstract-word sorting interfaces of
VFA 2.1 Extract. They call the existing insertion algorithms; the executable
word interfaces receive only their Boolean comparison. Theorems connect each
realization to original-value permutation, adjacent decoded order and stability.

The concrete cases distinguish signed from unsigned order, finite representation
from unbounded integers, and noninjective decoding from loss of original data.
They are kernel-checked mathematical clients, not native performance observations.
The chapter's tree interfaces and standalone workload remain separate obligations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ExtractedPrograms
open Applications.Sorting
open Representations.SignedComparison

universe u v

/-- The source Nat programs are exactly the accepted Sort implementations. -/
abbrev ins := Examples.InsertionSorting.insert
abbrev sort := Examples.InsertionSorting.sort

theorem ins_nil (a : Nat) : ins a [] = [a] := Examples.InsertionSorting.insert_nil a

theorem ins_cons (a b : Nat) (xs : List Nat) :
    ins a (b :: xs) = if decide (a ≤ b) then a :: b :: xs else b :: ins a xs := by
  simp [ins]

theorem sort_nil : sort [] = [] := rfl

theorem sort_cons (a : Nat) (xs : List Nat) :
    sort (a :: xs) = ins a (sort xs) := Examples.InsertionSorting.sort_cons a xs

theorem sort_correct (xs : List Nat) :
    xs.Perm (sort xs) ∧ (sort xs).IsChain (· ≤ ·) :=
  Examples.InsertionSorting.insertion_sort_correct xs

/-- All later interfaces call the same Boolean-only insertion adapter. -/
abbrev ins_int {W : Type u} (leb : W → W → Bool) : W → List W → List W :=
  DecodedInsertion.insert leb

abbrev sort_int {W : Type u} (leb : W → W → Bool) : List W → List W :=
  DecodedInsertion.sort leb

abbrev sorted {W : Type u} (decode : W → Int) : List W → Prop :=
  DecodedInsertion.Sorted decode

theorem sort_int_correct {W : Type u} (decode : W → Int) (leb : W → W → Bool)
    (hle : ∀ a b, leb a b = true ↔ decode a ≤ decode b) (xs : List W) :
    xs.Perm (sort_int leb xs) ∧ sorted decode (sort_int leb xs) :=
  DecodedInsertion.sort_correct decode leb hle xs

theorem sort_int_stable {W : Type u} (decode : W → Int) (leb : W → W → Bool)
    (hle : ∀ a b, leb a b = true ↔ decode a ≤ decode b) (xs : List W) :
    StableSort decode xs (sort_int leb xs) :=
  DecodedInsertion.sort_spec decode leb hle xs

theorem nat_sort_adapter (xs : List Nat) :
    sort_int (fun a b : Nat => decide (a ≤ b)) xs = sort xs := by
  change DecodedInsertion.sort (fun a b : Nat => decide (a ≤ b)) xs = sort xs
  rw [DecodedInsertion.sort_eq_insertionOn (fun n : Nat => (n : Int)) _
    (by intro a b; simp)]
  simp only [insertionOn, Int.ofNat_le, sort, Examples.InsertionSorting.sort]

abbrev insZ : Int → List Int → List Int := ins_int intLeb
abbrev sortZ : List Int → List Int := sort_int intLeb

theorem insZ_cons (a b : Int) (xs : List Int) :
    insZ a (b :: xs) = if intLeb a b then a :: b :: xs else b :: insZ a xs :=
  DecodedInsertion.insert_cons intLeb a b xs

theorem sortZ_cons (a : Int) (xs : List Int) : sortZ (a :: xs) = insZ a (sortZ xs) :=
  DecodedInsertion.sort_cons intLeb a xs

/-- The chapter's prose requires this unbounded-Int correctness result too. -/
theorem sortZ_correct (xs : List Int) : xs.Perm (sortZ xs) ∧ sorted id (sortZ xs) :=
  sort_int_correct id intLeb intLeb_true_iff xs

theorem sortZ_stable (xs : List Int) : StableSort id xs (sortZ xs) :=
  sort_int_stable id intLeb intLeb_true_iff xs

theorem sort_decode {W : Type u} (decode : W → Int) (leb : W → W → Bool)
    (hle : ∀ a b, leb a b = true ↔ decode a ≤ decode b) (xs : List W) :
    (sort_int leb xs).map decode = sortZ (xs.map decode) :=
  DecodedInsertion.map_decode_sort decode leb hle xs

theorem sortZ_empty : sortZ [] = [] := DecodedInsertion.sort_nil intLeb

theorem sortZ_singleton (n : Int) : sortZ [n] = [n] := by
  rw [sortZ_cons, sortZ_empty]
  exact DecodedInsertion.insert_nil intLeb n

theorem sortZ_signed_repeats : sortZ [-3, 2, -3, 0, 1] = [-3, -3, 0, 1, 2] := rfl

theorem sortZ_signed_repeats_contract :
    ([-3, 2, -3, 0, 1] : List Int).Perm [-3, -3, 0, 1, 2] ∧
      sorted id [-3, -3, 0, 1, 2] := by
  simpa only [sortZ_signed_repeats] using sortZ_correct [-3, 2, -3, 0, 1]

/-- Distinct originals can share a decoded key without breaking sorting. -/
theorem constant_decoder_not_injective :
    ¬ Function.Injective (fun _ : Bool => (0 : Int)) := by
  intro h
  have impossible : false = true := h rfl
  cases impossible

theorem constant_decoder_preserves_originals :
    sort_int (fun _ _ : Bool => true) [false, true, false] = [false, true, false] ∧
      StableSort (fun _ : Bool => (0 : Int)) [false, true, false]
        (sort_int (fun _ _ : Bool => true) [false, true, false]) :=
  DecodedInsertion.sort_constant 0 [false, true, false]

theorem constant_decoder_source_contract (xs : List Bool) :
    xs.Perm (sort_int (fun _ _ : Bool => true) xs) ∧
      sorted (fun _ : Bool => (0 : Int)) (sort_int (fun _ _ : Bool => true) xs) :=
  sort_int_correct (fun _ => 0) (fun _ _ => true) (by intros; simp) xs

/-- Three arbitrary payloads distinguish the earlier and later equal-key records. -/
theorem labelled_payloads {V : Type v} (first middle last : V) :
    sort_int (fun a b : Int × V => intLeb a.1 b.1)
      [(2, first), (1, middle), (2, last)] = [(1, middle), (2, first), (2, last)] ∧
      StableSort Prod.fst [(2, first), (1, middle), (2, last)]
        (sort_int (fun a b : Int × V => intLeb a.1 b.1)
          [(2, first), (1, middle), (2, last)]) := by
  constructor
  · simp [sort_int, DecodedInsertion.sort_cons, DecodedInsertion.sort_nil,
      DecodedInsertion.insert_cons, DecodedInsertion.insert_nil, intLeb]
  · exact sort_int_stable Prod.fst _ (fun a b => intLeb_true_iff a.1 b.1) _

theorem word_sort_correct {w : Nat} (xs : List (BitVec w)) :
    xs.Perm (sort_int wordLeb xs) ∧ sorted BitVec.toInt (sort_int wordLeb xs) :=
  sort_int_correct BitVec.toInt wordLeb wordLeb_true_iff xs

theorem word_sort_decode {w : Nat} (xs : List (BitVec w)) :
    (sort_int wordLeb xs).map BitVec.toInt = sortZ (xs.map BitVec.toInt) :=
  DecodedInsertion.word_decode_sort xs

/-- This observation uses signed minimum, maximum, negative repeats and zero. -/
theorem four_bit_signed_sort :
    (sort_int wordLeb [BitVec.ofInt 4 (-1), BitVec.ofInt 4 7, BitVec.ofInt 4 (-8),
      BitVec.ofInt 4 0, BitVec.ofInt 4 (-1)]).map BitVec.toInt = [-8, -1, -1, 0, 7] := by
  rw [word_sort_decode]
  decide

theorem four_bit_original_permutation :
    ([BitVec.ofInt 4 (-1), BitVec.ofInt 4 7, BitVec.ofInt 4 (-8),
      BitVec.ofInt 4 0, BitVec.ofInt 4 (-1)]).Perm
      (sort_int wordLeb [BitVec.ofInt 4 (-1), BitVec.ofInt 4 7, BitVec.ofInt 4 (-8),
        BitVec.ofInt 4 0, BitVec.ofInt 4 (-1)]) :=
  (word_sort_correct _).1

theorem zero_width_sort (xs : List (BitVec 0)) : sort_int wordLeb xs = xs := by
  apply DecodedInsertion.sort_eq_self_of_sorted BitVec.toInt wordLeb wordLeb_true_iff
  apply (DecodedInsertion.sorted_iff_keySorted BitVec.toInt xs).mpr
  apply List.pairwise_of_forall_mem_list
  intro a _ b _
  simp only [BitVec.toInt_zero_length, le_refl]

/-- No fixed word width represents the natural number at its upper signed bound. -/
theorem word_upper_bound_unrepresentable (w : Nat) :
    ¬ ∃ x : BitVec w, x.toInt = (2 : Int) ^ (w - 1) := by
  rintro ⟨x, hx⟩
  have h := (word_toInt_range x).2
  rw [hx] at h
  exact (lt_irrefl _ h)

theorem word_decoder_not_surjective (w : Nat) :
    ¬ Function.Surjective (@BitVec.toInt w) :=
  fun h => word_upper_bound_unrepresentable w (h _)

theorem int64_sort_correct (xs : List Int64) :
    xs.Perm (sort_int int64Leb xs) ∧ sorted Int64.toInt (sort_int int64Leb xs) :=
  sort_int_correct Int64.toInt int64Leb int64Leb_true_iff xs

theorem int64_sort_decode (xs : List Int64) :
    (sort_int int64Leb xs).map Int64.toInt = sortZ (xs.map Int64.toInt) :=
  DecodedInsertion.int64_decode_sort xs

theorem int64_signed_endpoints_sort :
    (sort_int int64Leb [Int64.ofInt ((2 : Int) ^ 63 - 1), Int64.ofInt 0,
      Int64.ofInt (-(2 : Int) ^ 63), Int64.ofInt (-1)]).map Int64.toInt =
      [-(2 : Int) ^ 63, -1, 0, (2 : Int) ^ 63 - 1] := by
  rw [int64_sort_decode]
  decide

theorem int64_upper_bound_unrepresentable :
    ¬ ∃ x : Int64, x.toInt = (2 : Int) ^ 63 := by
  rintro ⟨x, hx⟩
  have h := (int64_toInt_range x).2
  rw [hx] at h
  exact (lt_irrefl _ h)

/-- Ordinary branch proofs replace the source's custom Boolean-destruct tactics. -/
theorem choose_minimum {W : Type u} (decode : W → Int) (leb : W → W → Bool)
    (hle : ∀ a b, leb a b = true ↔ decode a ≤ decode b) (a b : W) :
    (if leb a b then decode a else decode b) = min (decode a) (decode b) := by
  by_cases h : leb a b = true
  · simp [h, min_eq_left ((hle a b).mp h)]
  · have hf : leb a b = false := Bool.eq_false_iff.mpr h
    have hlt := (nonstrict_false_iff decode leb hle a b).mp hf
    simp [hf, min_eq_right (le_of_lt hlt)]

theorem comparison_equality_branch {W : Type u} (decode : W → Int)
    (ltb : W → W → Bool) (hinj : Function.Injective decode)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b) (a b : W)
    (hab : ltb a b = false) (hba : ltb b a = false) : a = b :=
  hinj (le_antisymm ((strict_false_iff decode ltb hlt b a).mp hba)
    ((strict_false_iff decode ltb hlt a b).mp hab))

theorem integer_reflection_orientations :
    intLtb (-1) 0 = true ∧ intGtb (-1) 0 = false ∧
      intLeb 0 0 = true ∧ intGeb (-1) 0 = false ∧ intEqb (-1) 0 = false := by
  simp [intLtb, intGtb, intLeb, intGeb, intEqb]

end Examples.ExtractedPrograms
