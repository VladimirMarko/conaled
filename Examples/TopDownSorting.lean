import Applications.Sorting.TopDown
import Examples.StableSorting
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
  have h := sortFloorOn_correct id ([2, 1, 0] : List Nat)
  exact List.Perm.eq_of_pairwise' (r := fun a b : Nat => a ≤ b) h.1 (by decide)
    (h.2.trans (by decide : ([2, 1, 0] : List Nat).Perm [0, 1, 2]))

theorem full_multiset (cmp : Nat → Nat → Bool) :
    ((sortFloorBy cmp [2, 1, 2] : List Nat) : Multiset Nat) =
      (([2, 1, 2] : List Nat) : Multiset Nat) :=
  Quot.sound (sortFloorBy_perm cmp [2, 1, 2])

/-- Independent sortedness, permutation and retained equal-key occurrences. -/
theorem payload_expected_spec {α : Type u} (first middle last : α) :
    StableSort Prod.fst ([(1, first), (0, middle), (1, last)] : List (Nat × α))
      [(0, middle), (1, first), (1, last)] where
  sorted := by simp [KeySorted]
  perm := List.Perm.swap _ _ _
  stable := by
    intro k
    by_cases h0 : (0 : Nat) = k
    · subst k; simp
    · by_cases h1 : (1 : Nat) = k
      · subst k; simp
      · simp [h0, h1]

/-- The key order alone sorts arbitrary payloads, including equal-key occurrences. -/
theorem arbitrary_payload_order {α : Type u} (first middle last : α) :
    sortFloorOn Prod.fst [(1, first), (0, middle), (1, last)] =
      [(0, middle), (1, first), (1, last)] :=
  (sortFloorOn_spec Prod.fst _).unique (payload_expected_spec first middle last)

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

/-- A comparator contract on this input suffices even when it fails elsewhere. -/
theorem local_comparator_keys :
    KeySorted Prod.fst
      (sortFloorBy StableSorting.nonnegativeCompare StableSorting.nonnegativeInput) :=
  sortFloorBy_sorted_compatible_on Prod.fst _ _ StableSorting.nonnegative_compatible

/-- Reuse the existing independent signed-record specification through value agreement. -/
theorem signed_record_value :
    sortFloorOn Prod.fst StableSorting.input = StableSorting.expected :=
  (sortFloorOn_eq_sortOn Prod.fst StableSorting.input).trans StableSorting.merge_sort_records

end Examples.TopDownSorting
