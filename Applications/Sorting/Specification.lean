import Applications.Sorting.Stable

/-!
Equivalent ordering observations, independent of sorting implementations.
The optional-index and bounded-default forms reconstruct VFA Sort's two indexed
specifications. Their equivalence with Pairwise needs no relation laws; the
adjacent-chain bridge needs transitivity. Recovered ordering material from the
preserved VFA sorting-specification draft; contents/bag observations remain with
their separate chapter obligations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting.Specification

universe u v
variable {α : Type u} {κ : Type v}

/-- Every pair of successful optional lookups in increasing positions is related.
This is the generic form of VFA's `sorted'`; no default value is needed. -/
def Indexed (R : α → α → Prop) (xs : List α) : Prop :=
  ∀ (i j : Nat) (a b : α), i < j → xs[i]? = some a → xs[j]? = some b → R a b

/-- The default-valued form of indexed ordering, with explicit valid bounds.
This is the generic form of VFA's `sorted''`. -/
def BoundedIndexed (R : α → α → Prop) (defaultValue : α) (xs : List α) : Prop :=
  ∀ i j : Nat, i < j → j < xs.length →
    R ((xs[i]?).getD defaultValue) ((xs[j]?).getD defaultValue)

/-- The optional-lookup presentation is also the ordinary default-valued
list lookup used by the source's `nth` specification. -/
theorem boundedIndexed_iff_getD (R : α → α → Prop)
    (defaultValue : α) (xs : List α) :
    BoundedIndexed R defaultValue xs ↔
      ∀ i j : Nat, i < j → j < xs.length →
        R (xs.getD i defaultValue) (xs.getD j defaultValue) := by
  simp only [BoundedIndexed, List.getD_eq_getElem?_getD]

/-- Indexed ordering and pairwise ordering agree without any order laws. -/
theorem pairwise_iff_indexed (R : α → α → Prop) (xs : List α) :
    xs.Pairwise R ↔ Indexed R xs := by
  constructor
  · intro hp i j a b hij hi hj
    obtain ⟨hi', ha⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hj', hb⟩ := List.getElem?_eq_some_iff.mp hj
    rw [← ha, ← hb]
    exact (List.pairwise_iff_getElem.mp hp) i j hi' hj' hij
  · intro hi
    apply List.pairwise_iff_getElem.mpr
    intro i j hib hjb hij
    exact hi i j xs[i] xs[j] hij
      (List.getElem?_eq_getElem hib) (List.getElem?_eq_getElem hjb)

/-- Successful bounded lookups never consult their default value. -/
theorem pairwise_iff_boundedIndexed (R : α → α → Prop)
    (defaultValue : α) (xs : List α) :
    xs.Pairwise R ↔ BoundedIndexed R defaultValue xs := by
  constructor
  · intro hp i j hij hj
    have hi : i < xs.length := Nat.lt_trans hij hj
    simpa only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
      Option.getD_some] using (List.pairwise_iff_getElem.mp hp) i j hi hj hij
  · intro hb
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
      Option.getD_some] using hb i j hij hj

theorem indexed_iff_boundedIndexed (R : α → α → Prop)
    (defaultValue : α) (xs : List α) :
    Indexed R xs ↔ BoundedIndexed R defaultValue xs :=
  (pairwise_iff_indexed R xs).symm.trans
    (pairwise_iff_boundedIndexed R defaultValue xs)

theorem boundedIndexed_default_irrelevant (R : α → α → Prop)
    (defaultValue otherDefault : α) (xs : List α) :
    BoundedIndexed R defaultValue xs ↔ BoundedIndexed R otherDefault xs :=
  (pairwise_iff_boundedIndexed R defaultValue xs).symm.trans
    (pairwise_iff_boundedIndexed R otherDefault xs)

/-- Adjacent ordering requires transitivity to imply all earlier/later pairs.
No totality, reflexivity, decidable order, or antisymmetry is used. -/
theorem adjacent_iff_indexed (R : α → α → Prop) [Trans R R R] (xs : List α) :
    xs.IsChain R ↔ Indexed R xs :=
  List.isChain_iff_pairwise.trans (pairwise_iff_indexed R xs)

theorem adjacent_iff_boundedIndexed (R : α → α → Prop) [Trans R R R]
    (defaultValue : α) (xs : List α) :
    xs.IsChain R ↔ BoundedIndexed R defaultValue xs :=
  List.isChain_iff_pairwise.trans (pairwise_iff_boundedIndexed R defaultValue xs)

/-- The existing key-order contract admits the same optional-index observation.
No order on payloads or order laws on keys are required for this equivalence. -/
theorem keySorted_iff_indexed [LE κ] (key : α → κ) (xs : List α) :
    KeySorted key xs ↔
      Indexed (fun a b => key a ≤ key b) xs :=
  pairwise_iff_indexed _ xs

end Applications.Sorting.Specification
