import Applications.Sorting.Uniqueness
import Applications.Sorting.QuickSort
import Applications.Sorting.TopDown
import Examples.ThreeWayQuickSort

/-! Connected ordinary-sort uniqueness cases. Generic source sorters agree
through their independent correctness observations. The order boundaries
distinguish antisymmetry from totality and ordinary keys from stable payloads.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SortUniqueness
open Applications.Sorting
universe u
variable {α : Type u}

/-- First-pivot and floor-left recursion have the same ordinary output
function. No agreement of their costs or recursive structure is asserted. -/
theorem first_pivot_eq_floor [LinearOrder α] :
    quickSortOn (id : α → α) = sortFloorOn (id : α → α) :=
  sorters_eq (fun a b : α => a ≤ b) (quickSortOn id) (sortFloorOn id)
    (quickSortOn_correct id) (sortFloorOn_correct id)

/-- Use the literal source multiset specification for a different recursive
algorithm, retaining all equal-pivot occurrences. -/
theorem three_way_eq_floor [LinearOrder α] :
    (threeWayQuickSort : List α → List α) = sortFloorOn (id : α → α) := by
  refine sorters_eq_of_multiset (fun a b : α => a ≤ b)
    threeWayQuickSort (sortFloorOn id) ?_ ?_
  · intro xs
    exact ⟨threeWayQuickSort_sorted xs, threeWayQuickSort_multiset xs⟩
  · intro xs
    exact ⟨(sortFloorOn_correct id xs).1, Quot.sound (sortFloorOn_correct id xs).2⟩

/-- Transfer the retained independent mixed-duplicate expectation through the
new source-specification function equality. -/
theorem floor_mixed_duplicates :
    sortFloorOn (id : Nat → Nat) [2, 3, 1, 2, 0, 3, 2, 1] =
      [0, 1, 1, 2, 2, 2, 3, 3] := by
  calc
    sortFloorOn id [2, 3, 1, 2, 0, 3, 2, 1] =
        threeWayQuickSort [2, 3, 1, 2, 0, 3, 2, 1] :=
      (congrFun (three_way_eq_floor (α := Nat)) _).symm
    _ = [0, 1, 1, 2, 2, 2, 3, 3] := ThreeWayQuickSort.mixed_value

/-- Equality need not be a total relation. Its admissible pairwise lists still
have unique ordinary results; no structure on the payload type is needed. -/
theorem reverse_eq_of_equal (xs : List α)
    (hs : xs.Pairwise (fun a b => a = b)) : xs.reverse = xs := by
  let : Std.Antisymm (fun a b : α => a = b) := ⟨fun _ _ hab _ => hab⟩
  exact sorters_eq_at (fun a b : α => a = b) List.reverse id xs
    ⟨List.pairwise_reverse.mpr (hs.imp (fun h => h.symm)), List.reverse_perm xs⟩
    ⟨hs, List.Perm.refl xs⟩

/-- Non-totality alone is not a failure of antisymmetry. The nonempty example
also supplies a satisfiable local correctness premise to the public theorem. -/
theorem equality_order_boundary :
    (∀ a b : Bool, a = b → b = a → a = b) ∧
      ¬ (∀ a b : Bool, a = b ∨ b = a) ∧
      ([false, false] : List Bool).reverse = [false, false] := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · exact reverse_eq_of_equal _ (by decide)

/-- Constant keys make both identity and reversal ordinary-correct on every
input, but do not make their payload outputs equal or reversal stable. Thus
antisymmetry of keys cannot replace antisymmetry of the observed record relation. -/
theorem constant_key_boundary :
    (∀ xs : List Bool,
      KeySorted (fun _ : Bool => (0 : Nat)) xs ∧ xs.Perm xs) ∧
    (∀ xs : List Bool,
      KeySorted (fun _ : Bool => (0 : Nat)) xs.reverse ∧ xs.reverse.Perm xs) ∧
    (id : List Bool → List Bool) ≠ List.reverse ∧
    ¬ Stable (fun _ : Bool => (0 : Nat)) [false, true] [false, true].reverse := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro xs
    exact ⟨List.pairwise_of_forall (fun _ _ => Nat.le_refl 0), List.Perm.refl xs⟩
  · intro xs
    exact ⟨List.pairwise_of_forall (fun _ _ => Nat.le_refl 0), List.reverse_perm xs⟩
  · intro h
    simpa using congrFun h [false, true]
  · intro hs
    simpa using hs 0

end Examples.SortUniqueness
