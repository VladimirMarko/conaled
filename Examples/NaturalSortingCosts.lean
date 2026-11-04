import Applications.Resources.NaturalSorting
import Examples.NaturalSorting
import Examples.NaturalRunComparisons
import Examples.BottomUpCosts

/-!
# Connected natural-sort comparison cases

Independent source calculations give: sorted `[0,1,2]` costs two comparisons;
`[3,1,2]` costs two in detection and two in merging; `[1,3,2,4,0]` costs four
in detection, three in the first merge pass and one in the last merge. The
examples connect these counts to the actual measured composition. They do
not observe builder work, dispatch entries or compiled runtime.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.NaturalSortingCosts

open Applications.Sorting
open _root_.Resources.NaturalSorting
open Examples.NaturalRuns (natLT Record mixedRecords mixedRuns)
open Examples.NaturalSorting (natCompare)
universe u
variable {α : Type u}

theorem empty_payload :
    run (fun a _ : Empty => nomatch a) (fun a _ : Empty => nomatch a) [] = ([], 0) :=
  run_nil _ _

theorem singleton_payload (lt cmp : α → α → Bool) (a : α) :
    run lt cmp [a] = ([a], 0) := run_singleton lt cmp a

theorem ascending : run natLT natCompare [0, 1, 2] = ([0, 1, 2], 2) :=
  run_of_sorted id natCompare [0, 1, 2] (by decide) (by simp)

theorem ascending_zero_merge :
    Resources.BottomUpSorting.allComparisons natCompare (runsBy natLT [0, 1, 2]) = 0 :=
  mergeComparisons_of_sorted id natCompare [0, 1, 2] (by decide) (by simp)

theorem descending : run natLT natCompare [2, 1, 0] = ([0, 1, 2], 2) := by
  simpa using run_of_strictly_descending id natCompare [2, 1, 0] (by decide) (by simp)

theorem three_boundary_scan :
    Resources.NaturalRunComparisons.runsRunBy natLT [3, 1, 2] = ([[1, 3], [2]], 2) := by
  apply Prod.ext
  · rw [Resources.NaturalRunComparisons.runsRunBy_value]
    exact NaturalSorting.three_boundary_runs
  · exact Resources.NaturalRunComparisons.runsRunBy_cost_exact natLT [3, 1, 2]

theorem three_boundary_merge :
    Resources.BottomUpSorting.allRun natCompare [[1, 3], [2]] = ([1, 2, 3], 2) := by
  rw [BottomUpCosts.all_two_runs]
  simp [natCompare, Resources.ListMerge.run_cons_cons,
    Resources.ListMerge.run_nil_right, Resources.bind, Resources.reweight]

theorem three_boundary : run natLT natCompare [3, 1, 2] = ([1, 2, 3], 4) := by
  simp [run, three_boundary_scan, Resources.bind, three_boundary_merge]

theorem restart_merge :
    Resources.BottomUpSorting.allRun natCompare [[1, 3], [2, 4]] = ([1, 2, 3, 4], 3) := by
  rw [BottomUpCosts.all_two_runs]
  simp [natCompare, Resources.ListMerge.run_cons_cons,
    Resources.ListMerge.run_nil_left, Resources.bind, Resources.reweight]

theorem restart_boundary : run natLT natCompare [1, 3, 2, 4] = ([1, 2, 3, 4], 6) := by
  simp [run, NaturalRunComparisons.restart_boundary, Resources.bind, restart_merge]

theorem odd_runs_scan :
    Resources.NaturalRunComparisons.runsRunBy natLT [1, 3, 2, 4, 0] =
      ([[1, 3], [2, 4], [0]], 4) := by
  apply Prod.ext
  · rw [Resources.NaturalRunComparisons.runsRunBy_value]
    exact NaturalSorting.odd_runs
  · exact Resources.NaturalRunComparisons.runsRunBy_cost_exact natLT [1, 3, 2, 4, 0]

/-- The second pass compares 0 with the actual merged first run, then exhausts the right side. -/
theorem odd_runs_merge :
    Resources.BottomUpSorting.allRun natCompare [[1, 3], [2, 4], [0]] =
      ([0, 1, 2, 3, 4], 4) := by
  rw [Resources.BottomUpSorting.allRun_step, Resources.BottomUpSorting.pairsRun_step]
  simp [Resources.bind, Resources.reweight, Resources.pure, BottomUpCosts.all_two_runs,
    natCompare, Resources.ListMerge.run_cons_cons,
    Resources.ListMerge.run_nil_left, Resources.ListMerge.run_nil_right]

theorem odd_runs : run natLT natCompare [1, 3, 2, 4, 0] = ([0, 1, 2, 3, 4], 8) := by
  simp [run, odd_runs_scan, Resources.bind, odd_runs_merge]

theorem odd_runs_adaptive_budget : comparisons natLT natCompare [1, 3, 2, 4, 0] ≤ 14 := by
  calc
    _ ≤ ([1, 3, 2, 4, 0] : List Nat).length - 1 +
        ([1, 3, 2, 4, 0] : List Nat).length *
          Nat.clog 2 (runsBy natLT [1, 3, 2, 4, 0]).length :=
      comparisons_le_adaptive natLT natCompare _
    _ = 14 := by rw [NaturalSorting.odd_runs]; decide

theorem mixed_records_merge :
    Resources.BottomUpSorting.allRun (fun a b : Record => decide (a.1 ≤ b.1)) mixedRuns =
      ([(1, "D"), (2, "B"), (2, "C"), (3, "A")], 3) := by
  rw [mixedRuns, BottomUpCosts.all_two_runs]
  simp [Resources.ListMerge.run_cons_cons, Resources.ListMerge.run_nil_right,
    Resources.bind, Resources.reweight]

theorem mixed_records :
    run (fun a b : Record => decide (a.1 < b.1))
      (fun a b => decide (a.1 ≤ b.1)) mixedRecords =
        ([(1, "D"), (2, "B"), (2, "C"), (3, "A")], 6) := by
  simp [run, NaturalRunComparisons.mixed_records, Resources.bind, mixed_records_merge]

theorem weak_descent_merge :
    Resources.BottomUpSorting.allRun (fun a b : Record => decide (a.1 ≤ b.1))
      [[(3, "A"), (3, "B")], [(2, "C")]] =
        ([(2, "C"), (3, "A"), (3, "B")], 1) := by
  rw [BottomUpCosts.all_two_runs]
  simp [Resources.ListMerge.run_cons_cons, Resources.ListMerge.run_nil_right,
    Resources.bind, Resources.reweight]

theorem weak_descent_with_ties :
    run (fun a b : Record => decide (a.1 < b.1))
      (fun a b => decide (a.1 ≤ b.1)) [(3, "A"), (3, "B"), (2, "C")] =
        ([(2, "C"), (3, "A"), (3, "B")], 3) := by
  simp [run, NaturalRunComparisons.weak_descent_with_ties, Resources.bind, weak_descent_merge]

/-- The weakly descending tied input requires more than the attained one-run minimum. -/
theorem weak_descent_not_best_case :
    2 < comparisons (fun a b : Record => decide (a.1 < b.1))
      (fun a b => decide (a.1 ≤ b.1)) [(3, "A"), (3, "B"), (2, "C")] := by
  rw [comparisons, weak_descent_with_ties]
  decide

/-- The reused merger still permits empty inner runs, which the scanner itself never emits. -/
theorem empty_inner_runs :
    Resources.BottomUpSorting.allRun natCompare [[], [2], [], [1, 3]] = ([1, 2, 3], 2) := by
  rw [Resources.BottomUpSorting.allRun_step, Resources.BottomUpSorting.pairsRun_step,
    Resources.BottomUpSorting.pairsRun_step]
  simp [Resources.bind, Resources.reweight, Resources.pure, BottomUpCosts.all_two_runs,
    natCompare, Resources.ListMerge.run_cons_cons,
    Resources.ListMerge.run_nil_left]

theorem arbitrary_payload_correct (xs : List (Nat × α)) :
    KeySorted Prod.fst
        (run (fun a b => decide (a.1 < b.1)) (fun a b => decide (a.1 ≤ b.1)) xs).1 ∧
      (run (fun a b => decide (a.1 < b.1))
        (fun a b => decide (a.1 ≤ b.1)) xs).1.Perm xs :=
  run_correct Prod.fst xs

theorem arbitrary_operations_and_bounds (lt cmp : α → α → Bool) (xs : List α) :
    (run lt cmp xs).1.Perm xs ∧ (run lt cmp xs).1.length = xs.length ∧
      xs.length - 1 ≤ comparisons lt cmp xs ∧
      comparisons lt cmp xs ≤ xs.length - 1 + xs.length * Nat.clog 2 (runsBy lt xs).length :=
  ⟨run_perm lt cmp xs, run_length lt cmp xs,
    comparisons_lower lt cmp xs, comparisons_le_adaptive lt cmp xs⟩

theorem integer_zero_one_bound :
    (comparisons natLT natCompare [] : ℤ) ≤ 0 ∧
      (comparisons natLT natCompare [7] : ℤ) ≤ 1 := by
  constructor
  · simpa using comparisons_le_int_ceil natLT natCompare []
  · simpa using comparisons_le_int_ceil natLT natCompare [7]

/-- Every payload type and comparator is allowed: the constant key produces only one run. -/
theorem repeated_payload_exact (cmp : α → α → Bool) (a : α) (n : Nat) :
    comparisons (fun _ _ => false) cmp (List.replicate n a) = n - 1 := by
  simpa only [List.length_replicate] using
    comparisons_of_sorted (fun _ : α => (0 : Nat)) cmp (List.replicate n a)
      (by simp [KeySorted])

theorem constant_key_run_count (xs : List α) :
    (runsBy (fun _ _ => false) xs).length ≤ 1 := by
  cases xs with
  | nil => simp
  | cons a xs =>
    have hr : runsBy (fun _ _ => false) (a :: xs) = [a :: xs] :=
      runsOn_of_sorted (fun _ : α => (0 : Nat)) (a :: xs) (by simp [KeySorted]) (by simp)
    calc
      (runsBy (fun _ _ => false) (a :: xs)).length = 1 := by rw [hr]
      _ ≤ 1 := Nat.le_refl 1

/-- The adaptive growth theorem is exercised with a proved run budget, including n=0. -/
theorem repeated_payload_bounded_runs (cmp : α → α → Bool) (a : α) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (comparisons (fun _ _ => false) cmp (List.replicate n a) : ℝ))
      (fun n => (n : ℝ)) := by
  refine comparisons_isBigO_of_bounded_runs _ cmp (fun n => List.replicate n a)
    ?_ 1 (fun n => constant_key_run_count (List.replicate n a))
  intro n
  simp

theorem repeated_payload_linear (cmp : α → α → Bool) (a : α) :
    Asymptotics.IsTheta Filter.atTop
      (fun n => (comparisons (fun _ _ => false) cmp (List.replicate n a) : ℝ))
      (fun n => (n : ℝ)) := by
  apply sorted_comparisons_isTheta (fun _ : α => (0 : Nat)) cmp
    (fun n => List.replicate n a)
  · intro n
    simp
  · intro n
    simp [KeySorted]

theorem ascending_range_exact (n : Nat) :
    comparisons natLT natCompare (List.range n) = n - 1 := by
  simpa only [List.length_range] using
    comparisons_of_sorted id natCompare (List.range n)
      (List.pairwise_lt_range.imp (fun _ _ h => Nat.le_of_lt h))

theorem ascending_range_linear :
    Asymptotics.IsTheta Filter.atTop
      (fun n => (comparisons natLT natCompare (List.range n) : ℝ))
      (fun n => (n : ℝ)) := by
  apply sorted_comparisons_isTheta id natCompare (fun n => List.range n)
  · intro n
    simp
  · intro n
    exact List.pairwise_lt_range.imp (fun _ _ h => Nat.le_of_lt h)

/-- This oscillating family has length n; the general bound needs no run-count estimate. -/
theorem periodic_family_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (comparisons natLT natCompare ((List.range n).map (fun k => k % 3)) : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) := by
  apply comparisons_isBigO natLT natCompare (fun n => (List.range n).map (fun k => k % 3))
  intro n
  simp

end Examples.NaturalSortingCosts
