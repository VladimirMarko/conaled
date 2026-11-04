import Applications.Resources.TopDownSorting

/-!
# Connected top-down comparison cases

The expected three-element counts are independent recurrence calculations:
floor-left ascending/descending costs are 2/3, whereas the reference's
ceiling-left logical split costs 3/2. Both executions return the same sorted
values. The comparison models make no claim about machine runtime.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.TopDownCosts

open Applications.Sorting
open _root_.Resources.TopDownSorting
universe u
variable {α : Type u}

def natCompare (a b : Nat) : Bool := decide (a ≤ b)

theorem pair_run (cmp : α → α → Bool) (a b : α) :
    run cmp [a, b] = Resources.reweight Prod.fst (Resources.ListMerge.run cmp [a] [b]) := by
  rw [run_step cmp [a, b] (by decide)]
  simp [Resources.bind, Resources.reweight]

/-- The source's one-by-two split feeds the actual sorted right half to the root. -/
theorem floor_three_run (cmp : α → α → Bool) (a b c : α) :
    run cmp [a, b, c] =
      Resources.bind (Resources.reweight Prod.fst (Resources.ListMerge.run cmp [b] [c]))
        (fun right => Resources.reweight Prod.fst (Resources.ListMerge.run cmp [a] right)) := by
  rw [run_step cmp [a, b, c] (by decide)]
  simp [pair_run, Resources.bind, Resources.reweight]

/-- The standard logical sort's two-by-one recursion tree, specialized to length three.
It is an explicit measured execution, not a count inferred from its returned list. -/
def ceilThreeRun (cmp : α → α → Bool) (a b c : α) : Resources.Measured (List α) Nat :=
  Resources.bind (Resources.reweight Prod.fst (Resources.ListMerge.run cmp [a] [b]))
    (fun left => Resources.reweight Prod.fst (Resources.ListMerge.run cmp left [c]))

theorem ceilThreeRun_value (cmp : α → α → Bool) (a b c : α) :
    (ceilThreeRun cmp a b c).1 = List.mergeSort [a, b, c] cmp := by
  simp only [ceilThreeRun, Resources.bind_value, Resources.reweight_value,
    Resources.ListMerge.run_value]
  rw [show [a, b, c] = [a, b] ++ [c] from rfl,
    List.mergeSort_append [a, b] [c] (by simp) (by simp)]
  rw [show [a, b] = [a] ++ [b] from rfl,
    List.mergeSort_append [a] [b] (by simp) (by simp)]
  simp only [List.mergeSort_singleton]

theorem floor_ascending : run natCompare [0, 1, 2] = ([0, 1, 2], 2) := by
  simp [floor_three_run, natCompare, Resources.ListMerge.run_cons_cons,
    Resources.ListMerge.run_nil_left, Resources.bind, Resources.reweight]

theorem floor_descending : run natCompare [2, 1, 0] = ([0, 1, 2], 3) := by
  simp [floor_three_run, natCompare, Resources.ListMerge.run_cons_cons,
    Resources.ListMerge.run_nil_right, Resources.bind, Resources.reweight]

theorem ceil_ascending : ceilThreeRun natCompare 0 1 2 = ([0, 1, 2], 3) := by
  simp [ceilThreeRun, natCompare, Resources.ListMerge.run_cons_cons,
    Resources.ListMerge.run_nil_left, Resources.bind, Resources.reweight]

theorem ceil_descending : ceilThreeRun natCompare 2 1 0 = ([0, 1, 2], 2) := by
  simp [ceilThreeRun, natCompare, Resources.ListMerge.run_cons_cons,
    Resources.ListMerge.run_nil_right, Resources.bind, Resources.reweight]

theorem same_values_different_comparisons :
    (run natCompare [0, 1, 2]).1 = (ceilThreeRun natCompare 0 1 2).1 ∧
      (run natCompare [0, 1, 2]).2 ≠ (ceilThreeRun natCompare 0 1 2).2 ∧
      (run natCompare [2, 1, 0]).1 = (ceilThreeRun natCompare 2 1 0).1 ∧
      (run natCompare [2, 1, 0]).2 ≠ (ceilThreeRun natCompare 2 1 0).2 := by
  rw [floor_ascending, floor_descending, ceil_ascending, ceil_descending]
  decide

theorem empty_and_singleton (cmp : α → α → Bool) (a : α) :
    run cmp [] = ([], 0) ∧ run cmp [a] = ([a], 0) := ⟨run_nil cmp, run_singleton cmp a⟩

theorem empty_payload (cmp : Empty → Empty → Bool) (xs : List Empty) :
    run cmp xs = ([], 0) := by
  cases xs with
  | nil => exact run_nil cmp
  | cons x _ => exact Empty.elim x

/-- The stable source value preserves distinct payloads; the work remains an actual count. -/
theorem tagged_exact (first middle last : α) :
    run (fun x y : Nat × α => decide (x.1 ≤ y.1))
        [(1, first), (0, middle), (1, last)] =
      ([(0, middle), (1, first), (1, last)], 3) := by
  simp [floor_three_run, Resources.ListMerge.run_cons_cons,
    Resources.ListMerge.run_nil_left, Resources.ListMerge.run_nil_right,
    Resources.bind, Resources.reweight]

theorem tagged_stable (first middle last : α) :
    StableSort Prod.fst [(1, first), (0, middle), (1, last)]
      (run (fun x y : Nat × α => decide (x.1 ≤ y.1))
        [(1, first), (0, middle), (1, last)]).1 :=
  run_stable_spec Prod.fst _

/-- The raw bound retains arbitrary comparators, including ones that do not sort. -/
theorem raw_occurrences_and_bound (cmp : α → α → Bool) (xs : List α) :
    (run cmp xs).1.Perm xs ∧ (run cmp xs).1.length = xs.length ∧
      comparisons cmp xs ≤ xs.length * Nat.clog 2 xs.length :=
  ⟨run_perm cmp xs, run_length cmp xs, comparisons_le_clog cmp xs⟩

theorem power_zero_boundary : comparisons natCompare [9] ≤ 0 :=
  comparisons_le_of_length_pow natCompare [9] 0 (by decide)

theorem descending_family_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (comparisons natCompare (List.range n).reverse : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) := by
  apply comparisons_isBigO natCompare (fun n => (List.range n).reverse)
  intro n
  simp

end Examples.TopDownCosts
