import Applications.Resources.InsertionWork
import Examples.InsertionSorting

/-! VFA Sort resource clients of the shared insertion execution. The source
example distinguishes head tests, recursive entries and literal constructors;
it makes no claim about physical allocations or garbage collection. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.InsertionWork
open Resources Resources.InsertionSort
universe u

theorem empty_observations :
    sortMeasured (α := Nat) (· ≤ ·) [] = ([], (0, 1, 0)) := rfl

theorem singleton_observations (x : Nat) :
    sortMeasured (· ≤ ·) [x] = ([x], (0, 3, 1)) := rfl

/-- A terminal nil insertion has an invocation and a constructor, but no test. -/
theorem empty_insertion :
    insertMeasured (α := Nat) (· ≤ ·) 7 [] = ([7], (0, 1, 1)) := rfl

theorem tied_head_ignores_suffix (tail : List Nat) :
    insertComparisons (· ≤ ·) 7 (7 :: tail) = 1 :=
  insertComparisons_of_head _ _ _ _ (by decide)

theorem full_traversal :
    insertComparisons (α := Nat) (· ≤ ·) 4 [1, 2, 3] = 3 := by
  exact insertComparisons_of_all_not _ _ _ (by decide)

/-- The tail can be arbitrary: the comparison with 8 terminates the traversal. -/
theorem source_comparisons (tail : List Nat) :
    insertComparisons (· ≤ ·) 7 ([1, 3, 4, 8] ++ tail) = 4 := by
  simp [insertComparisons_cons]

theorem source_constructor_requests (tail : List Nat) :
    insertConstructors (· ≤ ·) 7 ([1, 3, 4, 8] ++ tail) = 5 := by
  rw [insertConstructors_eq, source_comparisons]

/-- Both value and the legacy FDSA call count are recovered from the same run. -/
theorem source_calls (tail : List Nat) :
    reweight (fun w : Work => w.2.1)
      (insertMeasured (· ≤ ·) 7 ([1, 3, 4, 8] ++ tail)) =
        ([1, 3, 4, 7, 8] ++ tail, 4) := by
  rw [insertMeasured_calls]
  obtain ⟨hv, hc⟩ := InsertionSorting.measured_insert_stopping tail
  exact Prod.ext hv hc

/-- Declared unit prices reweight the observed events, not elapsed runtime. -/
theorem source_tariff (tail : List Nat) (comparison entry constructor : Nat) :
    (reweight (fun w : Work => comparison * w.1 + entry * w.2.1 + constructor * w.2.2)
      (insertMeasured (· ≤ ·) 7 ([1, 3, 4, 8] ++ tail))).2 =
        4 * comparison + 4 * entry + 5 * constructor := by
  have hc : (insertMeasured (· ≤ ·) 7 ([1, 3, 4, 8] ++ tail)).2.2.1 = 4 :=
    congrArg Prod.snd (source_calls tail)
  change comparison * insertComparisons _ _ _ + entry * _ +
    constructor * insertConstructors _ _ _ = _
  rw [source_comparisons, source_constructor_requests, hc]
  simp [Nat.mul_comm]

theorem sorted_duplicates_best :
    sortComparisons (α := Nat) (· ≤ ·) [1, 1, 2] = 2 := by
  exact sortComparisons_of_pairwise _ _ (by decide)

theorem descending_worst :
    sortComparisons (α := Nat) (· ≤ ·) [2, 1, 0] = 3 := by
  exact sortComparisons_reverse_range 3

theorem descending_constructors :
    sortConstructors (α := Nat) (· ≤ ·) [2, 1, 0] = 6 := by
  exact sortConstructors_reverse_range 3

/-- Distinct call and comparison formulas apply to the same executed algorithm. -/
theorem worst_family (n : Nat) :
    sortComparisons (α := Nat) (· ≤ ·) (List.range n).reverse = n * (n - 1) / 2 ∧
    (sortRun (α := Nat) (· ≤ ·) (List.range n).reverse).2 = (n + 1) * (n + 2) / 2 :=
  ⟨sortComparisons_reverse_range n, sortRun_cost_reverse_range n⟩

/-- The measured result meets the source's independently indexed specification. -/
theorem source_contract (xs : List Nat) :
    xs.Perm (sortMeasured (· ≤ ·) xs).1 ∧
    InsertionSorting.sorted' (sortMeasured (· ≤ ·) xs).1 ∧
    xs.length - 1 ≤ sortComparisons (· ≤ ·) xs ∧
    sortComparisons (· ≤ ·) xs ≤ xs.length * (xs.length - 1) / 2 := by
  refine ⟨?_, ?_, sortComparisons_lower _ xs, sortComparisons_le _ xs⟩
  · rw [sortMeasured_value]
    exact InsertionSorting.sort_perm xs
  · rw [sortMeasured_value]
    exact InsertionSorting.sort_sorted' xs

/-- Payloads need no order: the call projection transfers the existing stable contract. -/
theorem keyed_contract {payload : Type u} (xs : List (Nat × payload)) :
    Applications.Sorting.StableSort Prod.fst xs
      (sortMeasured (fun a b => a.1 ≤ b.1) xs).1 ∧
    sortComparisons (fun a b => a.1 ≤ b.1) xs ≤ xs.length * (xs.length - 1) / 2 := by
  refine ⟨?_, sortComparisons_le _ xs⟩
  have hv : (sortMeasured (fun a b => a.1 ≤ b.1) xs).1 =
      (sortRun (fun a b => a.1 ≤ b.1) xs).1 :=
    congrArg Prod.fst (sortMeasured_calls _ xs)
  rw [hv]
  exact sortRun_stable Prod.fst xs

/-- Equal sorted values do not determine the comparisons taken to obtain them. -/
theorem same_value_different_comparisons :
    (sortMeasured (α := Nat) (· ≤ ·) [0, 1, 2]).1 =
      (sortMeasured (α := Nat) (· ≤ ·) [2, 1, 0]).1 ∧
    sortComparisons (α := Nat) (· ≤ ·) [0, 1, 2] ≠
      sortComparisons (α := Nat) (· ≤ ·) [2, 1, 0] := by
  constructor
  · rw [sortMeasured_value, sortMeasured_value]
    rfl
  · rw [sortComparisons_of_pairwise _ _ (by decide), descending_worst]
    decide

end Examples.InsertionWork
