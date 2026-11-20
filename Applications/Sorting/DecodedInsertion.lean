import Applications.Representations.SignedComparison
import Applications.Sorting.Sort
import Applications.Sorting.Specification
import Squares

/-!
# Insertion sorting through a decoder

The executable adapters take only the supplied Boolean comparison and use the
existing `List.orderedInsert`/`List.insertionSort` recurrence. Reflection connects
their results to decoded integer order. Neither correctness, stability nor
mapping compatibility needs an injective decoder or any order on payloads.

Permutation retains the original elements in the source input-to-output
orientation. The adjacent source observation is explicitly related to the
independent all-pairs stable-sorting contract through integer transitivity.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting.DecodedInsertion
open Representations.SignedComparison

universe u v
variable {α : Type u} {β : Type v}

def insert (cmp : α → α → Bool) (a : α) (xs : List α) : List α :=
  xs.orderedInsert (fun x y => cmp x y = true) a

def sort (cmp : α → α → Bool) (xs : List α) : List α :=
  xs.insertionSort (fun x y => cmp x y = true)

theorem insert_nil (cmp : α → α → Bool) (a : α) : insert cmp a [] = [a] := rfl

theorem insert_cons (cmp : α → α → Bool) (a b : α) (xs : List α) :
    insert cmp a (b :: xs) = if cmp a b then a :: b :: xs else b :: insert cmp a xs := rfl

theorem sort_nil (cmp : α → α → Bool) : sort cmp [] = [] := rfl

theorem sort_cons (cmp : α → α → Bool) (a : α) (xs : List α) :
    sort cmp (a :: xs) = insert cmp a (sort cmp xs) := rfl

theorem insert_perm (cmp : α → α → Bool) (a : α) (xs : List α) :
    (a :: xs).Perm (insert cmp a xs) := (List.perm_orderedInsert _ a xs).symm

theorem sort_perm (cmp : α → α → Bool) (xs : List α) :
    xs.Perm (sort cmp xs) := (List.perm_insertionSort _ xs).symm

theorem sort_length (cmp : α → α → Bool) (xs : List α) :
    (sort cmp xs).length = xs.length := (sort_perm cmp xs).length_eq.symm

def Sorted (decode : α → Int) (xs : List α) : Prop :=
  xs.IsChain (fun a b => decode a ≤ decode b)

theorem sorted_nil (decode : α → Int) : Sorted decode [] := .nil
theorem sorted_singleton (decode : α → Int) (a : α) : Sorted decode [a] := .singleton a

theorem sorted_cons (decode : α → Int) (a b : α) (xs : List α)
    (hab : decode a ≤ decode b) (hs : Sorted decode (b :: xs)) :
    Sorted decode (a :: b :: xs) := List.isChain_cons_cons.mpr ⟨hab, hs⟩

theorem sorted_cons_iff (decode : α → Int) (a b : α) (xs : List α) :
    Sorted decode (a :: b :: xs) ↔ decode a ≤ decode b ∧ Sorted decode (b :: xs) :=
  List.isChain_cons_cons

theorem sorted_iff_keySorted (decode : α → Int) (xs : List α) :
    Sorted decode xs ↔ KeySorted decode xs := by
  let : Trans (fun a b : α => decode a ≤ decode b)
      (fun a b : α => decode a ≤ decode b) (fun a b : α => decode a ≤ decode b) :=
    ⟨fun hab hbc => le_trans hab hbc⟩
  exact List.isChain_iff_pairwise

theorem insert_eq_orderedInsert (decode : α → Int) (cmp : α → α → Bool)
    (hc : ∀ a b, cmp a b = true ↔ decode a ≤ decode b) (a : α) (xs : List α) :
    insert cmp a xs = xs.orderedInsert (fun x y => decode x ≤ decode y) a := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    rw [insert_cons, List.orderedInsert_cons]
    by_cases h : cmp a b = true
    · simp [h, (hc a b).mp h]
    · have hn : ¬ decode a ≤ decode b := fun hab => h ((hc a b).mpr hab)
      simp [h, hn, ih]

theorem sort_eq_insertionOn (decode : α → Int) (cmp : α → α → Bool)
    (hc : ∀ a b, cmp a b = true ↔ decode a ≤ decode b) (xs : List α) :
    sort cmp xs = insertionOn decode xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [sort_cons, insert_eq_orderedInsert decode cmp hc, ih]
    rfl

theorem sort_spec (decode : α → Int) (cmp : α → α → Bool)
    (hc : ∀ a b, cmp a b = true ↔ decode a ≤ decode b) (xs : List α) :
    StableSort decode xs (sort cmp xs) := by
  rw [sort_eq_insertionOn decode cmp hc]
  exact insertionOn_spec decode xs

/-- Exact source correctness, with permutation of original values. -/
theorem sort_correct (decode : α → Int) (cmp : α → α → Bool)
    (hc : ∀ a b, cmp a b = true ↔ decode a ≤ decode b) (xs : List α) :
    xs.Perm (sort cmp xs) ∧ Sorted decode (sort cmp xs) :=
  ⟨sort_perm cmp xs, (sorted_iff_keySorted decode _).mpr (sort_spec decode cmp hc xs).sorted⟩

theorem sort_stable (decode : α → Int) (cmp : α → α → Bool)
    (hc : ∀ a b, cmp a b = true ↔ decode a ≤ decode b) (xs : List α) :
    Stable decode xs (sort cmp xs) := (sort_spec decode cmp hc xs).stable

/-- Agreement with independent stable merge sort is a value observation. -/
theorem sort_eq_sortOn (decode : α → Int) (cmp : α → α → Bool)
    (hc : ∀ a b, cmp a b = true ↔ decode a ≤ decode b) (xs : List α) :
    sort cmp xs = sortOn decode xs := (sort_spec decode cmp hc xs).unique (sortOn_spec decode xs)

theorem sort_eq_self_of_sorted (decode : α → Int) (cmp : α → α → Bool)
    (hc : ∀ a b, cmp a b = true ↔ decode a ≤ decode b) (xs : List α)
    (hs : Sorted decode xs) : sort cmp xs = xs := by
  rw [sort_eq_sortOn decode cmp hc]
  exact sortOn_sorted_fixed decode xs ((sorted_iff_keySorted decode xs).mp hs)

/-- Compatible maps may identify elements and may change their universe. -/
theorem map_insert (f : α → β) (cmp : α → α → Bool) (other : β → β → Bool)
    (hc : ∀ a b, cmp a b = other (f a) (f b)) (a : α) (xs : List α) :
    (insert cmp a xs).map f = insert other (f a) (xs.map f) := by
  apply List.map_orderedInsert
  · intro b _
    rw [hc]
  · intro b _
    rw [hc]

theorem map_sort (f : α → β) (cmp : α → α → Bool) (other : β → β → Bool)
    (hc : ∀ a b, cmp a b = other (f a) (f b)) (xs : List α) :
    (sort cmp xs).map f = sort other (xs.map f) := by
  apply List.map_insertionSort
  intro a _ b _
  rw [hc]

private theorem comparison_eq_intLeb (decode : α → Int) (cmp : α → α → Bool)
    (hc : ∀ a b, cmp a b = true ↔ decode a ≤ decode b) (a b : α) :
    cmp a b = intLeb (decode a) (decode b) := by
  apply Bool.eq_iff_iff.mpr
  rw [intLeb_true_iff]
  exact hc a b

theorem map_decode_insert (decode : α → Int) (cmp : α → α → Bool)
    (hc : ∀ a b, cmp a b = true ↔ decode a ≤ decode b) (a : α) (xs : List α) :
    (insert cmp a xs).map decode = insert intLeb (decode a) (xs.map decode) :=
  map_insert decode cmp intLeb (comparison_eq_intLeb decode cmp hc) a xs

theorem map_decode_sort (decode : α → Int) (cmp : α → α → Bool)
    (hc : ∀ a b, cmp a b = true ↔ decode a ≤ decode b) (xs : List α) :
    (sort cmp xs).map decode = sort intLeb (xs.map decode) :=
  map_sort decode cmp intLeb (comparison_eq_intLeb decode cmp hc) xs

/-- Concrete square packages use `Type 0`, since `Squares.Rep` shares one
universe between its carriers. The operation theorems above retain their universes. -/
def listRep {W : Type} (decode : W → Int) : Squares.Rep where
  R := List W
  S := List Int
  decode := List.map decode

def insertSquare {W : Type} (decode : W → Int) (cmp : W → W → Bool)
    (hc : ∀ a b, cmp a b = true ↔ decode a ≤ decode b) (a : W) :
    Squares.Square (listRep decode) (listRep decode) where
  impl := insert cmp a
  spec := insert intLeb (decode a)
  commutes := map_decode_insert decode cmp hc a

def sortSquare {W : Type} (decode : W → Int) (cmp : W → W → Bool)
    (hc : ∀ a b, cmp a b = true ↔ decode a ≤ decode b) :
    Squares.Square (listRep decode) (listRep decode) where
  impl := sort cmp
  spec := sort intLeb
  commutes := map_decode_sort decode cmp hc

theorem sort_constant (c : Int) (xs : List α) :
    sort (fun _ _ : α => true) xs = xs ∧
      StableSort (fun _ : α => c) xs (sort (fun _ _ : α => true) xs) := by
  have hc : ∀ a b : α, true = true ↔ c ≤ c := by intros; simp
  refine ⟨sort_eq_self_of_sorted (fun _ => c) _ hc xs ?_, sort_spec (fun _ => c) _ hc xs⟩
  apply (sorted_iff_keySorted (fun _ : α => c) xs).mpr
  apply List.pairwise_of_forall_mem_list
  intro a _ b _
  exact le_rfl

/-- The earlier key-2 record stays before the later key-2 record; payloads have
no equality, ordering or inhabitance requirement. -/
theorem labelled_ties (first second : β) :
    sort (fun a b : Int × β => intLeb a.1 b.1) [(2, first), (1, second), (2, second)] =
      [(1, second), (2, first), (2, second)] := by
  simp [sort_cons, sort_nil, insert_cons, insert_nil, intLeb]

theorem word_decode_sort {w : Nat} (xs : List (BitVec w)) :
    (sort wordLeb xs).map BitVec.toInt = sort intLeb (xs.map BitVec.toInt) :=
  map_decode_sort BitVec.toInt wordLeb wordLeb_true_iff xs

theorem int64_decode_sort (xs : List Int64) :
    (sort int64Leb xs).map Int64.toInt = sort intLeb (xs.map Int64.toInt) :=
  map_decode_sort Int64.toInt int64Leb int64Leb_true_iff xs

end Applications.Sorting.DecodedInsertion
