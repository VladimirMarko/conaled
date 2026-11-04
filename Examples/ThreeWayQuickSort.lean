import Applications.Sorting.ThreeWayQuickSort

/-! Source-connected cases for Exercise 2.3. The mixed input's fixed expected
output is [0,1,1,2,2,2,3,3], retaining multiplicities 1,2,3,2. The pivot-absent
case separates a strict bound below the parent from a false strict tail bound.
The altered-root witnesses keep correct recursive child outputs fixed; they
are not claimed to execute globally modified sorting algorithms.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ThreeWayQuickSort
open Applications.Sorting Sequences.Partition
universe u

/-- The nil case needs no inhabitant or default pivot. -/
theorem empty_input {α : Type u} [LinearOrder α] :
    threeWayQuickSort ([] : List α) = [] := threeWayQuickSort_nil

theorem singleton_input {α : Type u} [LinearOrder α] (x : α) :
    threeWayQuickSort [x] = [x] := threeWayQuickSort_singleton x

theorem all_equal_buckets : partition3 (2 : Nat) [2, 2] = ([], [2, 2], []) := by
  simp [partition3_eq_filters]

/-- This is the actual source body: only the two empty strict lists recurse. -/
theorem all_equal_source_equation :
    threeWayQuickSort ([2, 2, 2] : List Nat) =
      threeWayQuickSort [] ++ ((2 :: [2, 2]) ++ threeWayQuickSort []) := by
  simpa using threeWayQuickSort_cons (2 : Nat) [2, 2]

theorem all_equal_input : threeWayQuickSort ([2, 2, 2] : List Nat) = [2, 2, 2] := by
  simpa using threeWayQuickSort_replicate 3 (2 : Nat)

theorem all_equal_family {α : Type u} [LinearOrder α] (n : Nat) (x : α) :
    threeWayQuickSort (List.replicate n x) = List.replicate n x :=
  threeWayQuickSort_replicate n x

theorem mixed_buckets :
    partition3 (2 : Nat) [3, 1, 2, 0, 3, 2, 1] = ([1, 0, 1], [2, 2], [3, 3]) := by
  simp [partition3_eq_filters]

theorem mixed_source_equation :
    threeWayQuickSort ([2, 3, 1, 2, 0, 3, 2, 1] : List Nat) =
      threeWayQuickSort [1, 0, 1] ++ ((2 :: [2, 2]) ++ threeWayQuickSort [3, 3]) := by
  simpa using threeWayQuickSort_cons (2 : Nat) [3, 1, 2, 0, 3, 2, 1]

theorem mixed_left_child : threeWayQuickSort ([1, 0, 1] : List Nat) = [0, 1, 1] := by
  simp [threeWayQuickSort_cons]

theorem mixed_right_child : threeWayQuickSort ([3, 3] : List Nat) = [3, 3] := by
  simpa using threeWayQuickSort_replicate 2 (3 : Nat)

/-- The independently sorted permutation consumes both general correctness
fields rather than appealing to a separate library sort implementation. -/
theorem mixed_value :
    threeWayQuickSort ([2, 3, 1, 2, 0, 3, 2, 1] : List Nat) = [0, 1, 1, 2, 2, 2, 3, 3] := by
  have h := threeWayQuickSort_correct ([2, 3, 1, 2, 0, 3, 2, 1] : List Nat)
  exact List.Perm.eq_of_pairwise' (r := fun a b : Nat => a ≤ b) h.1 (by decide)
    (h.2.trans (by decide : ([2, 3, 1, 2, 0, 3, 2, 1] : List Nat).Perm
      [0, 1, 1, 2, 2, 2, 3, 3]))

theorem mixed_multiset :
    (threeWayQuickSort ([2, 3, 1, 2, 0, 3, 2, 1] : List Nat) : Multiset Nat) =
      (([2, 3, 1, 2, 0, 3, 2, 1] : List Nat) : Multiset Nat) :=
  threeWayQuickSort_multiset _

theorem mixed_multiplicities :
    (threeWayQuickSort ([2, 3, 1, 2, 0, 3, 2, 1] : List Nat)).count 0 = 1 ∧
      (threeWayQuickSort ([2, 3, 1, 2, 0, 3, 2, 1] : List Nat)).count 1 = 2 ∧
      (threeWayQuickSort ([2, 3, 1, 2, 0, 3, 2, 1] : List Nat)).count 2 = 3 ∧
      (threeWayQuickSort ([2, 3, 1, 2, 0, 3, 2, 1] : List Nat)).count 3 = 2 := by
  have hp := threeWayQuickSort_perm ([2, 3, 1, 2, 0, 3, 2, 1] : List Nat)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hp.count_eq 0
  · simpa using hp.count_eq 1
  · simpa using hp.count_eq 2
  · simpa using hp.count_eq 3

theorem mixed_length :
    (threeWayQuickSort ([2, 3, 1, 2, 0, 3, 2, 1] : List Nat)).length = 8 := by
  simpa using threeWayQuickSort_length ([2, 3, 1, 2, 0, 3, 2, 1] : List Nat)

theorem mixed_support_boundary :
    0 ∈ threeWayQuickSort ([2, 3, 1, 2, 0, 3, 2, 1] : List Nat) ∧
      4 ∉ threeWayQuickSort ([2, 3, 1, 2, 0, 3, 2, 1] : List Nat) := by
  simp [mem_threeWayQuickSort]

theorem absent_pivot_buckets : partition3 (0 : Nat) [2, 1] = ([], [], [2, 1]) := by
  simp [partition3_eq_filters]

theorem absent_pivot_source_equation :
    threeWayQuickSort ([0, 2, 1] : List Nat) =
      threeWayQuickSort [] ++ ([0] ++ threeWayQuickSort [2, 1]) := by
  simpa only [absent_pivot_buckets] using threeWayQuickSort_cons_partition (0 : Nat) [2, 1]

/-- The greater child has the full tail length. It still decreases below the
parent; the existing membership-premised strict-tail theorem is not needed. -/
theorem absent_pivot_child_decrease :
    0 ∉ ([2, 1] : List Nat) ∧
      (partition3 (0 : Nat) [2, 1]).2.2.length = 2 ∧
      (partition3 (0 : Nat) [2, 1]).2.2.length < ([0, 2, 1] : List Nat).length ∧
      ¬ (partition3 (0 : Nat) [2, 1]).2.2.length < ([2, 1] : List Nat).length := by
  rw [absent_pivot_buckets]
  decide

theorem absent_pivot_value : threeWayQuickSort ([0, 2, 1] : List Nat) = [0, 1, 2] := by
  simp [threeWayQuickSort_cons]

/-- Alter only the root assembly after the correct child results: sortedness
survives, but the required pivot occurrence is lost. -/
theorem omitted_pivot_boundary :
    let altered := threeWayQuickSort ([1, 0, 1] : List Nat) ++
      ([2, 2] ++ threeWayQuickSort [3, 3])
    KeySorted id altered ∧ ¬ altered.Perm [2, 3, 1, 2, 0, 3, 2, 1] := by
  simp only [mixed_left_child, mixed_right_child]
  decide

theorem omitted_equal_block_boundary :
    let altered := threeWayQuickSort ([1, 0, 1] : List Nat) ++
      ([2] ++ threeWayQuickSort [3, 3])
    KeySorted id altered ∧ ¬ altered.Perm [2, 3, 1, 2, 0, 3, 2, 1] := by
  simp only [mixed_left_child, mixed_right_child]
  decide

theorem duplicated_pivot_boundary :
    let altered := threeWayQuickSort ([1, 0, 1] : List Nat) ++
      ([2, 2, 2, 2] ++ threeWayQuickSort [3, 3])
    KeySorted id altered ∧ ¬ altered.Perm [2, 3, 1, 2, 0, 3, 2, 1] := by
  simp only [mixed_left_child, mixed_right_child]
  decide

/-- Moving the pivot ahead of the correct left child preserves every
occurrence but destroys the other half of the sorting contract. -/
theorem misplaced_pivot_boundary :
    let altered := 2 :: (threeWayQuickSort ([1, 0, 1] : List Nat) ++
      ([2, 2] ++ threeWayQuickSort [3, 3]))
    altered.Perm [2, 3, 1, 2, 0, 3, 2, 1] ∧ ¬ KeySorted id altered := by
  simp only [mixed_left_child, mixed_right_child]
  decide

end Examples.ThreeWayQuickSort
