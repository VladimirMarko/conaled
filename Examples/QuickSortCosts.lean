import Applications.Resources.QuickSort
import Examples.QuickSort
import Init.Data.List.Nat.Range

/-! Independently calculated clients of the deterministic quicksort tariffs.
The singleton costs (5,3), the mixed case costs (45,18), and the arbitrary
unsorted suffix are fixed before the resource implementation. The two coordinates
mean exercise calls and additional literal append calls, respectively.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.QuickSortCosts
open Resources Resources.QuickSort Applications.Sorting
universe u

theorem empty_source {α : Type u} (lt : α → α → Bool) :
    run lt [] = ([], (1, 0)) := run_nil lt

theorem empty_worker {α : Type u} (lt : α → α → Bool) (suffix : List α) :
    accumulatorRun lt [] suffix = (suffix, (1, 0)) := accumulatorRun_nil lt suffix

theorem singleton_source {α : Type u} (lt : α → α → Bool) (x : α) :
    run lt [x] = ([x], (5, 3)) := run_singleton lt x

theorem singleton_worker {α : Type u} (lt : α → α → Bool) (x : α) (suffix : List α) :
    accumulatorRun lt [x] suffix = (x :: suffix, (5, 0)) := by
  simp only [accumulatorRun_exact, quickSortAccBy_singleton, exerciseCost_singleton]

/-- Payloads have neither order nor equality instances; only their natural key
is tested. The suffix remains entirely unrestricted. -/
theorem payload_suffix {α : Type u} (xs suffix : List (Nat × α)) :
    accumulatorRun (fun a b => decide (a.1 < b.1)) xs suffix =
      (quickSortOn Prod.fst xs ++ suffix,
        (exerciseCost (fun a b => decide (a.1 < b.1)) xs, 0)) :=
  accumulatorRun_eq_append _ _ _

theorem mixed_costs :
    exerciseCost (fun a b : Nat => decide (a < b)) [2, 1, 2, 3, 0] = 45 ∧
      appendCost (fun a b : Nat => decide (a < b)) [2, 1, 2, 3, 0] = 18 := by
  constructor <;> simp [exerciseCost_cons, appendCost_cons]

theorem mixed_source :
    run (fun a b : Nat => decide (a < b)) [2, 1, 2, 3, 0] =
      ([0, 1, 2, 2, 3], (45, 18)) := by
  rw [run_exact]
  apply Prod.ext
  · exact Examples.QuickSort.mixed_source_value
  · exact Prod.ext mixed_costs.1 mixed_costs.2

/-- This suffix overlaps the input and is not sorted; it is not traversed. -/
theorem mixed_worker :
    accumulatorRun (fun a b : Nat => decide (a < b)) [2, 1, 2, 3, 0] [4, 0, 2] =
      ([0, 1, 2, 2, 3, 4, 0, 2], (45, 0)) := by
  rw [accumulatorRun_exact]
  apply Prod.ext
  · exact Examples.QuickSort.mixed_accumulator_value
  · exact Prod.ext mixed_costs.1 rfl

theorem mixed_full_cost :
    literalCost (fun a b : Nat => decide (a < b)) [2, 1, 2, 3, 0] = 63 := by
  simp only [literalCost, mixed_costs.1, mixed_costs.2]

theorem right_associated_appends :
    appendPivotRun [0, 1] (2 : Nat) [3] = ([0, 1, 2, 3], 5) := by
  simpa using appendPivotRun_exact [0, 1] (2 : Nat) [3]

/-- A comparison execution returns the same value but pays a different count. -/
theorem left_associated_appends :
    bind (ListReversal.appendRun [0, 1] [2])
      (fun middle => ListReversal.appendRun middle [3]) =
        (([0, 1, 2, 3] : List Nat), 7) := by
  simp [bind, ListReversal.appendRun_exact]

/-- The exact source strict/nonstrict split and both unit-filter tariffs. -/
theorem mixed_source_tariff :
    exerciseCost (fun a b : Nat => decide (a < b)) [2, 1, 2, 3, 0] =
      exerciseCost (fun a b : Nat => decide (a < b)) [1, 0] +
        exerciseCost (fun a b : Nat => decide (a < b)) [2, 3] + 19 := by
  simpa [ListCalls.filterRun_cons, ListCalls.filterRun_nil] using
    exerciseCost_cons_on (id : Nat → Nat) 2 [1, 2, 3, 0]

theorem ascending_costs :
    exerciseCost (fun a b : Nat => decide (a < b)) [0, 1, 2] = 25 ∧
      appendCost (fun a b : Nat => decide (a < b)) [0, 1, 2] = 9 := by
  simpa using costs_of_sorted (id : Nat → Nat) [0, 1, 2] (by decide)

theorem ascending_full :
    literalCost (fun a b : Nat => decide (a < b)) [0, 1, 2] = 34 := by
  simpa using literalCost_of_all_right (fun a b : Nat => decide (a < b))
    [0, 1, 2] (by decide)

theorem descending_costs :
    exerciseCost (fun a b : Nat => decide (a < b)) [2, 1, 0] = 25 ∧
      appendCost (fun a b : Nat => decide (a < b)) [2, 1, 0] = 12 := by
  have h := costs_of_strict_descent (id : Nat → Nat) [2, 1, 0] (by decide)
  constructor
  · simpa using h.1
  · have ha : 2 * appendCost (fun a b : Nat => decide (a < b)) [2, 1, 0] = 24 := by
      simpa using h.2
    omega

theorem descending_full :
    literalCost (fun a b : Nat => decide (a < b)) [2, 1, 0] = 37 := by
  simpa using literalCost_of_all_left (fun a b : Nat => decide (a < b))
    [2, 1, 0] (by decide)

/-- The full-cost bound is attained for every size, not only by a numerical
sequence disconnected from a sorting input. -/
theorem descending_range_attains_bound (n : Nat) :
    literalCost (fun a b : Nat => decide (a < b)) (List.range n).reverse =
      (5 * n ^ 2 + 9 * n + 2) / 2 := by
  have hs : (List.range n).reverse.Pairwise
      (fun a b : Nat => decide (b < a) = true) := by
    apply List.pairwise_reverse.mpr
    exact List.pairwise_lt_range.imp (fun h => by simpa only [decide_eq_true_eq] using h)
  simpa only [List.length_reverse, List.length_range] using
    literalCost_of_all_left (fun a b : Nat => decide (a < b)) (List.range n).reverse hs

theorem all_equal_costs :
    exerciseCost (fun a b : Nat => decide (a < b)) [2, 2, 2] = 25 ∧
      appendCost (fun a b : Nat => decide (a < b)) [2, 2, 2] = 9 := by
  simpa using costs_replicate (id : Nat → Nat) 2 3

theorem all_equal_full :
    literalCost (fun a b : Nat => decide (a < b)) [2, 2, 2] = 34 := by
  simpa using literalCost_of_all_right (fun a b : Nat => decide (a < b))
    [2, 2, 2] (by decide)

/-- Arbitrarily large duplicate inputs retain the quadratic exercise tariff. -/
theorem duplicate_family (x n : Nat) :
    exerciseCost (fun a b : Nat => decide (a < b)) (List.replicate n x) =
        2 * n ^ 2 + 2 * n + 1 ∧
      appendCost (fun a b : Nat => decide (a < b)) (List.replicate n x) = 3 * n :=
  costs_replicate (id : Nat → Nat) x n

theorem duplicate_worker (x n : Nat) (suffix : List Nat) :
    (accumulatorRun (fun a b : Nat => decide (a < b)) (List.replicate n x) suffix).2 =
      (2 * n ^ 2 + 2 * n + 1, 0) := by
  rw [accumulatorRun_exact]
  exact Prod.ext (duplicate_family x n).1 rfl

/-- The key collision does not impose an equality or order on the payloads. -/
theorem equal_key_payloads {α : Type u} (first second : α) :
    exerciseCost (fun a b : Nat × α => decide (a.1 < b.1)) [(7, first), (7, second)] = 13 ∧
      appendCost (fun a b : Nat × α => decide (a.1 < b.1)) [(7, first), (7, second)] = 6 := by
  simpa using costs_of_sorted Prod.fst [(7, first), (7, second)] (by simp [KeySorted])

theorem balanced_costs :
    exerciseCost (fun a b : Nat => decide (a < b)) [1, 0, 2] = 21 ∧
      appendCost (fun a b : Nat => decide (a < b)) [1, 0, 2] = 10 := by
  constructor <;> simp [exerciseCost_cons, appendCost_cons]

theorem balanced_full :
    literalCost (fun a b : Nat => decide (a < b)) [1, 0, 2] = 31 := by
  simp only [literalCost, balanced_costs.1, balanced_costs.2]

/-- The comparison-statistic bridge uses the actual measured mixed case. -/
theorem mixed_partition_mass :
    partitionMass (fun a b : Nat => decide (a < b)) [2, 1, 2, 3, 0] = 6 := by
  have h := exerciseCost_eq_partitionMass (fun a b : Nat => decide (a < b)) [2, 1, 2, 3, 0]
  have ht := mixed_costs.1
  simp only [List.length_cons, List.length_nil] at h
  omega

theorem balanced_partition_mass :
    partitionMass (fun a b : Nat => decide (a < b)) [1, 0, 2] = 2 := by
  have h := exerciseCost_eq_partitionMass (fun a b : Nat => decide (a < b)) [1, 0, 2]
  have ht := balanced_costs.1
  simp only [List.length_cons, List.length_nil] at h
  omega

theorem mixed_worker_saving :
    (accumulatorRun (fun a b : Nat => decide (a < b)) [2, 1, 2, 3, 0] [4, 0, 2]).2.1 + 15 ≤
      literalCost (fun a b : Nat => decide (a < b)) [2, 1, 2, 3, 0] := by
  simpa using accumulator_saving (fun a b : Nat => decide (a < b)) [2, 1, 2, 3, 0] [4, 0, 2]

theorem payload_full_bound {α : Type u} (xs : List (Nat × α)) :
    literalCost (fun a b => decide (a.1 < b.1)) xs ≤
      (5 * xs.length ^ 2 + 9 * xs.length + 2) / 2 := literalCost_le _ _

theorem payload_exercise_bound {α : Type u} (xs : List (Nat × α)) :
    exerciseCost (fun a b => decide (a.1 < b.1)) xs ≤
      2 * xs.length ^ 2 + 2 * xs.length + 1 := exerciseCost_le _ _

theorem payload_full_exercise_bridge {α : Type u} (xs : List (Nat × α)) :
    exerciseCost (fun a b => decide (a.1 < b.1)) xs ≤
        literalCost (fun a b => decide (a.1 < b.1)) xs ∧
      literalCost (fun a b => decide (a.1 < b.1)) xs ≤
        2 * exerciseCost (fun a b => decide (a.1 < b.1)) xs :=
  ⟨exerciseCost_le_literalCost _ _, literalCost_le_twice _ _⟩

end Examples.QuickSortCosts
