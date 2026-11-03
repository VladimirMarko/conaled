import Applications.Sorting.TopDown
import Mathlib.Data.Multiset.Basic

/-! Source-split, duplicate-occurrence and keyed-stability clients for floor-left
top-down merge sort. Comparison counts belong to the separate measured model.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.TopDownSorting
open Applications.Sorting
universe u

theorem source_three_split :
    sortFloorBy (fun a b : Nat => decide (a ≤ b)) [2, 1, 0] =
      List.merge (sortFloorBy (fun a b : Nat => decide (a ≤ b)) [2])
        (sortFloorBy (fun a b : Nat => decide (a ≤ b)) [1, 0])
        (fun a b : Nat => decide (a ≤ b)) := by
  simpa using sortFloorBy_step (fun a b : Nat => decide (a ≤ b)) [2, 1, 0] (by decide)

theorem source_three_value : sortFloorOn id ([2, 1, 0] : List Nat) = [0, 1, 2] := by
  rw [sortFloorOn_eq_sortOn]
  rfl

theorem full_multiset (cmp : Nat → Nat → Bool) :
    ((sortFloorBy cmp [2, 1, 2] : List Nat) : Multiset Nat) =
      (([2, 1, 2] : List Nat) : Multiset Nat) :=
  Quot.sound (sortFloorBy_perm cmp [2, 1, 2])

/-- The key order alone sorts arbitrary payloads, including equal-key occurrences. -/
theorem arbitrary_payload_order {α : Type u} (first middle last : α) :
    sortFloorOn Prod.fst [(1, first), (0, middle), (1, last)] =
      [(0, middle), (1, first), (1, last)] := by
  rw [sortFloorOn_eq_sortOn]
  rfl

theorem stable_across_split {α : Type u} (first middle last : α) :
    (sortFloorOn Prod.fst [(1, first), (0, middle), (1, last)]).filter
        (fun x => decide (x.1 = (1 : Nat))) = [(1, first), (1, last)] := by
  calc
    _ = ([(1, first), (0, middle), (1, last)] : List (Nat × α)).filter
        (fun x => decide (x.1 = 1)) := (sortFloorOn_spec Prod.fst _).stable 1
    _ = _ := rfl

theorem empty_payload :
    sortFloorOn (Empty.elim : Empty → Nat) [] = [] := sortFloorBy_nil _

theorem singleton_payload {α : Type u} (x : α) :
    sortFloorOn (fun _ : α => (0 : Nat)) [x] = [x] := sortFloorBy_singleton _ x

theorem arbitrary_comparator_preserves_occurrences (xs : List Nat) :
    (sortFloorBy (fun _ _ => false) xs).Perm xs ∧
    (sortFloorBy (fun _ _ => false) xs).length = xs.length :=
  ⟨sortFloorBy_perm _ xs, sortFloorBy_length _ xs⟩

end Examples.TopDownSorting
