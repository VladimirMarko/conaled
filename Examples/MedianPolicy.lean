import Applications.Resources.MedianPolicy

/-! Connected FDSA-3-80 cases for the actual charged median policy.
Concrete pivots use the public small-input equation of the measured selector.
Concrete outer executions use the public policy step equation. General bounds
are also consumed for an infinite size family and arbitrary integer inputs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MedianPolicy
open Resources.MedianPolicy

theorem pivot_two : pivotRun ([6, 7] : List Nat) = (some 6, 14) := by
  rw [pivotRun_small _ (by decide) (by decide)]
  decide

theorem pivot_four : pivotRun ([4, 5, 6, 7] : List Nat) = (some 5, 23) := by
  rw [pivotRun_small _ (by decide) (by decide)]
  decide

theorem pivot_eight : pivotRun (List.range 8) = (some 3, 41) := by
  rw [pivotRun_small _ (by decide) (by decide)]
  decide

theorem pivot_three : pivotRun ([4, 5, 6] : List Nat) = (some 5, 19) := by
  rw [pivotRun_small _ (by decide) (by decide)]
  decide

theorem pivot_seven : pivotRun (List.range 7) = (some 3, 37) := by
  rw [pivotRun_small _ (by decide) (by decide)]
  decide

theorem pivot_four_initial : pivotRun (List.range 4) = (some 1, 23) := by
  rw [pivotRun_small _ (by decide) (by decide)]
  decide

theorem pivot_duplicates : pivotRun ([4, 4, 4, 4] : List Nat) = (some 4, 23) := by
  rw [pivotRun_small _ (by decide) (by decide)]
  decide

theorem two_execution (fuel : Nat) :
    run (fuel + 2) 1 ([6, 7] : List Nat) = ((some 7, [2, 1]), 43) := by
  have hp : (pivotRun ([6, 7] : List Nat)).1 = some 6 := by rw [pivot_two]
  rw [run, Resources.SelectionPolicy.runWith_step pivotRun (fuel + 1) 1
    [6, 7] (by decide) 6 hp, pivot_two]
  change Resources.SelectionPolicy.prepend 2 24 (run (fuel + 1) 0 [7]) = _
  rw [run_singleton]
  rfl

theorem four_tail_execution (fuel : Nat) :
    run (fuel + 3) 3 ([4, 5, 6, 7] : List Nat) = ((some 7, [4, 2, 1]), 81) := by
  have hp : (pivotRun ([4, 5, 6, 7] : List Nat)).1 = some 5 := by rw [pivot_four]
  rw [run, Resources.SelectionPolicy.runWith_step pivotRun (fuel + 2) 3
    [4, 5, 6, 7] (by decide) 5 hp, pivot_four]
  change Resources.SelectionPolicy.prepend 4 38 (run (fuel + 2) 1 [6, 7]) = _
  rw [two_execution]
  rfl

theorem eight_execution : run 8 7 (List.range 8) = ((some 7, [8, 4, 2, 1]), 147) := by
  have hp : (pivotRun (List.range 8)).1 = some 3 := by rw [pivot_eight]
  rw [run, Resources.SelectionPolicy.runWith_step pivotRun 7 7
    (List.range 8) (by decide) 3 hp, pivot_eight]
  change Resources.SelectionPolicy.prepend 8 66 (run 7 3 [4, 5, 6, 7]) = _
  rw [four_tail_execution 4]
  rfl

theorem eight_trace_connected :
    Resources.HalvingTrace.Halves 8 (run 8 7 (List.range 8)).1.2 :=
  run_trace 8 7 (List.range 8) (by decide) (by decide)

theorem eight_scan : (run 8 7 (List.range 8)).1.2.sum = 15 := by
  rw [eight_execution]
  decide

theorem eight_edges : (run 8 7 (List.range 8)).1.2.length - 1 = 3 := by
  rw [eight_execution]
  decide

theorem eight_edges_bound : (run 8 7 (List.range 8)).1.2.length - 1 ≤ Nat.log 2 8 :=
  run_edges_log 8 7 (List.range 8) (by decide) (by decide)

theorem three_tail_execution (fuel : Nat) :
    run (fuel + 2) 2 ([4, 5, 6] : List Nat) = ((some 6, [3, 1]), 51) := by
  have hp : (pivotRun ([4, 5, 6] : List Nat)).1 = some 5 := by rw [pivot_three]
  rw [run, Resources.SelectionPolicy.runWith_step pivotRun (fuel + 1) 2
    [4, 5, 6] (by decide) 5 hp, pivot_three]
  change Resources.SelectionPolicy.prepend 3 32 (run (fuel + 1) 0 [6]) = _
  rw [run_singleton]
  rfl

theorem seven_execution : run 7 6 (List.range 7) = ((some 6, [7, 3, 1]), 111) := by
  have hp : (pivotRun (List.range 7)).1 = some 3 := by rw [pivot_seven]
  rw [run, Resources.SelectionPolicy.runWith_step pivotRun 6 6
    (List.range 7) (by decide) 3 hp, pivot_seven]
  change Resources.SelectionPolicy.prepend 7 60 (run 6 2 [4, 5, 6]) = _
  rw [three_tail_execution 4]
  rfl

theorem seven_scan_bounds :
    7 ≤ (run 7 6 (List.range 7)).1.2.sum ∧ (run 7 6 (List.range 7)).1.2.sum ≤ 14 :=
  run_scan_bounds 7 6 (List.range 7) (by decide) (by decide)

/-- Odd size exposes that the ceiling-log bound need not be attained. -/
theorem seven_edges_strict_clog :
    (run 7 6 (List.range 7)).1.2.length - 1 < Nat.clog 2 7 := by
  rw [seven_execution]
  decide

theorem early_equal_execution : run 4 1 (List.range 4) = ((some 1, [4]), 39) := by
  have hp : (pivotRun (List.range 4)).1 = some 1 := by rw [pivot_four_initial]
  rw [run, Resources.SelectionPolicy.runWith_step pivotRun 3 1
    (List.range 4) (by decide) 1 hp, pivot_four_initial]
  rfl

theorem early_equal_edges : (run 4 1 (List.range 4)).1.2.length - 1 = 0 := by
  rw [early_equal_execution]
  rfl

/-- This case exercises the lower branch, absent from every minimum-pivot run. -/
theorem lower_branch_execution : run 4 0 (List.range 4) = ((some 0, [4, 1]), 57) := by
  have hp : (pivotRun (List.range 4)).1 = some 1 := by rw [pivot_four_initial]
  rw [run, Resources.SelectionPolicy.runWith_step pivotRun 3 0
    (List.range 4) (by decide) 1 hp, pivot_four_initial]
  change Resources.SelectionPolicy.prepend 4 38 (run 3 0 [0]) = _
  rw [run_singleton 2]
  rfl

theorem duplicate_execution :
    run 4 3 ([4, 4, 4, 4] : List Nat) = ((some 4, [4]), 44) := by
  have hp : (pivotRun ([4, 4, 4, 4] : List Nat)).1 = some 4 := by rw [pivot_duplicates]
  rw [run, Resources.SelectionPolicy.runWith_step pivotRun 3 3
    [4, 4, 4, 4] (by decide) 4 hp, pivot_duplicates]
  rfl

theorem duplicate_trace_connected :
    Resources.HalvingTrace.Halves 4 (run 4 3 ([4, 4, 4, 4] : List Nat)).1.2 :=
  run_trace 4 3 [4, 4, 4, 4] (by decide) (by decide)

theorem singleton_execution : run 1 0 ([-4] : List Int) = ((some (-4), [1]), 19) :=
  run_singleton 0 (-4)

theorem singleton_trace_connected : (run 1 0 ([-4] : List Int)).1.2 = [1] :=
  run_singleton_trace 0 (-4)

theorem singleton_active_and_edges :
    (run 1 0 ([-4] : List Int)).1.2.length = 1 ∧
      (run 1 0 ([-4] : List Int)).1.2.length - 1 = 0 := by
  rw [singleton_trace_connected]
  decide

theorem empty_execution : run 3 0 ([] : List Nat) = ((none, []), 1) := rfl

theorem invalid_value : (run 4 4 (List.range 4)).1.1 = none :=
  (run_none 4 4 (List.range 4) (by decide)).mpr (by decide)

/-- All ranks in an infinite growing family use the actual trace bound. -/
theorem range_scan_bound (n k : Nat) (hk : k < n + 1) :
    n + 1 ≤ (run (n + 1) k (List.range (n + 1))).1.2.sum ∧
      (run (n + 1) k (List.range (n + 1))).1.2.sum ≤ 2 * (n + 1) := by
  simpa only [List.length_range] using
    run_scan_bounds (n + 1) k (List.range (n + 1)) (by simpa using hk) (by simp)

theorem range_edge_bound (n k : Nat) (hk : k < n + 1) :
    (run (n + 1) k (List.range (n + 1))).1.2.length - 1 ≤ Nat.clog 2 (n + 1) := by
  simpa only [List.length_range] using
    run_edges_clog (n + 1) k (List.range (n + 1)) (by simpa using hk) (by simp)

/-- One coefficient works for all integer inputs and valid ranks, including
duplicates and arbitrary order; the actual median construction is charged. -/
theorem all_integer_inputs_linear :
    ∃ D : Nat, 0 < D ∧ ∀ (xs : List Int) (k : Nat), k < xs.length →
      xs.length ≤ (run xs.length k xs).2 ∧ (run xs.length k xs).2 ≤ D * xs.length := by
  obtain ⟨D, hp, bound⟩ := run_exists_uniform_linear_bound
  exact ⟨D, hp, fun xs k hk => bound Int xs.length k xs hk (by omega)⟩

end Examples.MedianPolicy
