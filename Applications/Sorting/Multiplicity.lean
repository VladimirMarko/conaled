import Applications.Sequences.Multiplicity
import Applications.Sorting.Specification
import Applications.Sorting.Uniqueness

/-!
Transport occurrence observations in sorting contracts, keeping their ordering
observation unchanged. List multiplicities are owned by Sequences.Multiplicity;
ordering observations and sorting uniqueness remain in their existing modules.
These bridges do not add stability or identify execution costs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting.Multiplicity
open Sequences.Multiplicity

universe u
variable {α : Type u} [BEq α] [LawfulBEq α]

/-- Any identical output observation can accompany the occurrence equivalence.
In particular, the source adjacent-order predicate needs no strengthening. -/
theorem contract_equivalent (P : List α → Prop) (f : List α → List α) :
    (∀ xs, xs.Perm (f xs) ∧ P (f xs)) ↔
      (∀ xs, contents xs = contents (f xs) ∧ P (f xs)) := by
  constructor
  · intro h xs
    exact ⟨perm_contents (h xs).1, (h xs).2⟩
  · intro h xs
    exact ⟨perm_of_contents_eq (h xs).1, (h xs).2⟩

/-- Both count and ordering observations can be transported by existing bridges. -/
theorem indexed_contract_equivalent (R : α → α → Prop) (f : List α → List α) :
    (∀ xs, xs.Perm (f xs) ∧ (f xs).Pairwise R) ↔
      (∀ xs, contents xs = contents (f xs) ∧ Specification.Indexed R (f xs)) := by
  constructor
  · intro h xs
    exact ⟨perm_contents (h xs).1, (Specification.pairwise_iff_indexed R _).mp (h xs).2⟩
  · intro h xs
    exact ⟨perm_of_contents_eq (h xs).1,
      (Specification.pairwise_iff_indexed R _).mpr (h xs).2⟩

/-- Existing sorting uniqueness consumes the multiplicity contract. Antisymmetry
is on the actual element relation, not merely on noninjective record keys. -/
theorem sorters_eq_of_contents (R : α → α → Prop) [Std.Antisymm R]
    (f g : List α → List α)
    (hf : ∀ xs, (f xs).Pairwise R ∧ contents (f xs) = contents xs)
    (hg : ∀ xs, (g xs).Pairwise R ∧ contents (g xs) = contents xs) : f = g :=
  sorters_eq R f g
    (fun xs => ⟨(hf xs).1, perm_of_contents_eq (hf xs).2⟩)
    (fun xs => ⟨(hg xs).1, perm_of_contents_eq (hg xs).2⟩)

end Applications.Sorting.Multiplicity
