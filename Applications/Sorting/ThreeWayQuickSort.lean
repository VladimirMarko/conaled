import Applications.Sequences.Partition
import Applications.Sorting.Stable
import Mathlib.Data.Multiset.Defs

/-! The literal three-filter quicksort from FDSA Exercise 2.3.
Only the strict tail buckets recurse. One held pivot precedes every equal
tail occurrence. The shared partition operation supplies value observations;
its different traversal and measured realizations are not cost dependencies.
The ordinary sorting contract is nondecreasing order plus full permutation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting
open Sequences.Partition
universe u
variable {α : Type u} [LinearOrder α]

/-- The source executes three filters of the tail and returns the equal block
directly. The source's two appends retain their right association. -/
def threeWayQuickSort : List α → List α
  | [] => []
  | pivot :: xs =>
      threeWayQuickSort (xs.filter (fun x => decide (x < pivot))) ++
        ((pivot :: xs.filter (fun x => decide (x = pivot))) ++
          threeWayQuickSort (xs.filter (fun x => decide (pivot < x))))
termination_by xs => xs.length
decreasing_by
  all_goals
    apply Nat.lt_succ_of_le
    rw [List.length_unattach, ← List.length_attach (l := xs)]
    exact List.length_filter_le _ _

@[simp] theorem threeWayQuickSort_nil : threeWayQuickSort ([] : List α) = [] := by
  rw [threeWayQuickSort]

/-- The printed source recurrence has no recursive call on the equal bucket. -/
theorem threeWayQuickSort_cons (pivot : α) (xs : List α) :
    threeWayQuickSort (pivot :: xs) =
      threeWayQuickSort (xs.filter (fun x => decide (x < pivot))) ++
        ((pivot :: xs.filter (fun x => decide (x = pivot))) ++
          threeWayQuickSort (xs.filter (fun x => decide (pivot < x)))) := by
  rw [threeWayQuickSort]

@[simp] theorem threeWayQuickSort_singleton (x : α) : threeWayQuickSort [x] = [x] := by
  simp [threeWayQuickSort_cons]

/-- The exact value bridge reuses the independent shared partition facts.
It does not identify three-filter execution with the shared two-partition body. -/
theorem threeWayQuickSort_cons_partition (pivot : α) (xs : List α) :
    threeWayQuickSort (pivot :: xs) =
      threeWayQuickSort (partition3 pivot xs).1 ++
        ((pivot :: (partition3 pivot xs).2.1) ++
          threeWayQuickSort (partition3 pivot xs).2.2) := by
  simp only [threeWayQuickSort_cons, partition3_eq_filters]

/-- Every occurrence is retained, including the held pivot and the whole
equal-tail block. No pivot-membership premise is needed for the tail. -/
theorem threeWayQuickSort_perm (xs : List α) : (threeWayQuickSort xs).Perm xs := by
  match xs with
  | [] => simp
  | pivot :: ys =>
      rw [threeWayQuickSort_cons_partition]
      have hp := partition3_perm pivot ys
      rw [List.append_assoc] at hp
      exact ((threeWayQuickSort_perm (partition3 pivot ys).1).append
        (((List.Perm.refl (partition3 pivot ys).2.1).append
          (threeWayQuickSort_perm (partition3 pivot ys).2.2)).cons pivot)).trans
        (List.perm_middle.trans (hp.cons pivot))
termination_by xs.length
decreasing_by
  all_goals simp only [partition3_eq_filters]
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem threeWayQuickSort_length (xs : List α) :
    (threeWayQuickSort xs).length = xs.length := (threeWayQuickSort_perm xs).length_eq

theorem mem_threeWayQuickSort (xs : List α) (x : α) :
    x ∈ threeWayQuickSort xs ↔ x ∈ xs := (threeWayQuickSort_perm xs).mem_iff

/-- This is the source multiset observation, stronger than support equality. -/
theorem threeWayQuickSort_multiset (xs : List α) :
    (threeWayQuickSort xs : Multiset α) = (xs : Multiset α) :=
  Quot.sound (threeWayQuickSort_perm xs)

theorem threeWayQuickSort_support (xs : List α) :
    {x | x ∈ threeWayQuickSort xs} = {x | x ∈ xs} := by
  ext x
  exact mem_threeWayQuickSort xs x

/-- The recursive outputs inherit strict bucket bounds through permutation.
The complete middle block consists of values equal to the held pivot. -/
theorem threeWayQuickSort_sorted (xs : List α) :
    KeySorted id (threeWayQuickSort xs) := by
  match xs with
  | [] => simp [KeySorted]
  | pivot :: ys =>
      rw [threeWayQuickSort_cons_partition]
      have hleft := threeWayQuickSort_sorted (partition3 pivot ys).1
      have hright := threeWayQuickSort_sorted (partition3 pivot ys).2.2
      have hlow : ∀ a ∈ threeWayQuickSort (partition3 pivot ys).1, a < pivot := by
        intro a ha
        exact ((partition_left_mem pivot ys a).mp
          ((threeWayQuickSort_perm (partition3 pivot ys).1).mem_iff.mp ha)).2
      have hhigh : ∀ b ∈ threeWayQuickSort (partition3 pivot ys).2.2, pivot < b := by
        intro b hb
        exact ((partition_right_mem pivot ys b).mp
          ((threeWayQuickSort_perm (partition3 pivot ys).2.2).mem_iff.mp hb)).2
      have hmiddle : ∀ a ∈ pivot :: (partition3 pivot ys).2.1, a = pivot := by
        intro a ha
        rcases List.mem_cons.mp ha with ha | ha
        · exact ha
        · exact ((partition_equal_mem pivot ys a).mp ha).2
      apply List.pairwise_append.mpr
      refine ⟨hleft, ?_, ?_⟩
      · apply List.pairwise_append.mpr
        refine ⟨?_, hright, ?_⟩
        · apply List.pairwise_of_forall_mem_list
          intro a ha b hb
          change a ≤ b
          exact le_of_eq ((hmiddle a ha).trans (hmiddle b hb).symm)
        · intro a ha b hb
          change a ≤ b
          exact le_trans (le_of_eq (hmiddle a ha)) (le_of_lt (hhigh b hb))
      · intro a ha b hb
        change a ≤ b
        rcases List.mem_append.mp hb with hb | hb
        · exact le_trans (le_of_lt (hlow a ha)) (le_of_eq (hmiddle b hb).symm)
        · exact le_of_lt (lt_trans (hlow a ha) (hhigh b hb))
termination_by xs.length
decreasing_by
  all_goals simp only [partition3_eq_filters]
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- The chapter's ordinary sorting contract on every finite input. -/
theorem threeWayQuickSort_correct (xs : List α) :
    KeySorted id (threeWayQuickSort xs) ∧ (threeWayQuickSort xs).Perm xs :=
  ⟨threeWayQuickSort_sorted xs, threeWayQuickSort_perm xs⟩

/-- For an all-equal input, the source strict children are empty and the equal
block is returned directly. This is a value law, not a numerical cost formula. -/
theorem threeWayQuickSort_replicate (n : Nat) (x : α) :
    threeWayQuickSort (List.replicate n x) = List.replicate n x := by
  cases n with
  | zero => simp
  | succ n =>
      rw [List.replicate_succ, threeWayQuickSort_cons]
      simp

end Applications.Sorting
