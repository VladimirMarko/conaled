import Applications.Search.AbstractSet.Deletion
import Mathlib.Data.List.Sort

/-!
# The source strict-list set model

Insertion suppresses equality at the encountered head. Deletion removes the
first equal head and otherwise scans on, even if the query is smaller. These
raw operations are defined before strictness; duplicate removal semantics is
conditional on uniqueness. `Strict` reuses the standard pairwise relation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedList
universe u
variable {α : Type u}

def Strict [LT α] (xs : List α) : Prop := xs.Pairwise (· < ·)

@[simp] theorem strict_nil [LT α] : Strict ([] : List α) := List.Pairwise.nil

@[simp] theorem strict_singleton [LT α] (x : α) : Strict [x] := by
  simp [Strict]

theorem strict_iff_adjacent [Preorder α] (xs : List α) :
    Strict xs ↔ List.IsChain (· < ·) xs :=
  List.sortedLT_iff_pairwise.symm.trans List.sortedLT_iff_isChain

theorem strict_iff_nodup_nonstrict [PartialOrder α] (xs : List α) :
    Strict xs ↔ xs.Nodup ∧ xs.Pairwise (· ≤ ·) := by
  rw [Strict, ← List.sortedLT_iff_pairwise, List.sortedLT_iff_nodup_and_sortedLE,
    List.sortedLE_iff_pairwise]

section Equality
variable [DecidableEq α]

def delete (x : α) : List α → List α
  | [] => []
  | a :: xs => if x = a then xs else a :: delete x xs

theorem delete_eq_erase (x : α) (xs : List α) : delete x xs = xs.erase x := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases heq : x = a
      · subst x
        simp [delete]
      · simp [delete, heq, Ne.symm heq, ih]

theorem delete_of_not_mem (x : α) {xs : List α} (h : x ∉ xs) : delete x xs = xs := by
  rw [delete_eq_erase, List.erase_of_not_mem h]

theorem mem_delete_of_nodup (x z : α) {xs : List α} (h : xs.Nodup) :
    z ∈ delete x xs ↔ z ≠ x ∧ z ∈ xs := by
  rw [delete_eq_erase]
  exact h.mem_erase_iff

theorem strict_delete [LT α] (x : α) {xs : List α} (h : Strict xs) :
    Strict (delete x xs) := by
  rw [delete_eq_erase]
  exact h.erase x

end Equality

section LinearOrder
variable [LinearOrder α]

def insert (x : α) : List α → List α
  | [] => [x]
  | a :: xs =>
      if x < a then x :: a :: xs
      else if x = a then a :: xs
      else a :: insert x xs

theorem mem_insert (x z : α) (xs : List α) :
    z ∈ insert x xs ↔ z = x ∨ z ∈ xs := by
  induction xs with
  | nil => simp [insert]
  | cons a xs ih =>
      by_cases hlt : x < a
      · simp [insert, hlt]
      · by_cases heq : x = a
        · subst x
          simp [insert]
        · simp only [insert, ite_eq_right hlt, ite_eq_right heq, List.mem_cons, ih]
          tauto

theorem strict_insert (x : α) {xs : List α} (h : Strict xs) :
    Strict (insert x xs) := by
  induction xs with
  | nil => exact strict_singleton x
  | cons a xs ih =>
      have hs := List.pairwise_cons.mp h
      by_cases hlt : x < a
      · rw [insert, ite_eq_left hlt]
        apply List.pairwise_cons.mpr
        refine ⟨?_, h⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hlt
        · exact lt_trans hlt (hs.1 z hz)
      · by_cases heq : x = a
        · simpa only [insert, ite_eq_right hlt, ite_eq_left heq] using h
        · rw [insert, ite_eq_right hlt, ite_eq_right heq]
          apply List.pairwise_cons.mpr
          refine ⟨?_, ih hs.2⟩
          intro z hz
          rcases (mem_insert x z xs).mp hz with rfl | hz
          · exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
          · exact hs.1 z hz

theorem mem_delete (x z : α) {xs : List α} (h : Strict xs) :
    z ∈ delete x xs ↔ z ≠ x ∧ z ∈ xs :=
  mem_delete_of_nodup x z ((strict_iff_nodup_nonstrict xs).mp h).1

def ops : AbstractSet.DeleteOps α (List α) where
  empty := []
  insert := insert
  member x xs := decide (x ∈ xs)
  delete := delete

theorem laws : AbstractSet.DeleteLaws (ops : AbstractSet.DeleteOps α (List α))
    (fun xs x => x ∈ xs) Strict where
  empty_valid := strict_nil
  empty _ := List.not_mem_nil
  insert_valid x _ h := strict_insert x h
  insert x xs _ z := mem_insert x z xs
  member _ _ _ := decide_eq_true_iff
  delete_valid x _ h := strict_delete x h
  delete x _ h z := mem_delete x z h

end LinearOrder
end Search.OrderedList
