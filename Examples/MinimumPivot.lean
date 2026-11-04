import Applications.Resources.MinimumPivot

/-! Connected p35 examples. The policy actually computes a minimum each time.
The explicit call tariff includes the measured size traversals; scan volume and
recursive depth remain separate observations of that same execution. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MinimumPivot
open Resources.MinimumPivot

def input : List Nat := [3, 1, 4, 2]

theorem input_nodup : input.Nodup := by decide

theorem middle_execution : run 4 2 input = ((some 3, [4, 3, 2]), 49) := by decide

theorem middle_trace : (run 4 2 input).1.2 = [4, 3, 2] :=
  run_trace 4 2 input input_nodup (by decide) (by decide)

theorem middle_calls : (run 4 2 input).1.2.length = 3 :=
  active_calls 4 2 input input_nodup (by decide) (by decide)

theorem middle_edges : (run 4 2 input).1.2.length - 1 = 2 :=
  recursive_edges 4 2 input input_nodup (by decide) (by decide)

theorem middle_scan : (run 4 2 input).1.2.sum = 9 :=
  scan_exact 4 2 input input_nodup (by decide) (by decide)

theorem middle_cost : (run 4 2 input).2 = 49 := by
  rw [cost_exact 4 2 input input_nodup (by decide) (by decide), middle_scan]

theorem largest_execution : run 4 3 input = ((some 4, [4, 3, 2, 1]), 59) := by decide

theorem largest_scan_connected : (run 4 3 input).1.2.sum = 10 :=
  largest_scan 4 input input_nodup (by decide) (by decide)

theorem minimum_execution : run 4 0 input = ((some 1, [4]), 20) := by decide

theorem minimum_is_not_four_calls : (run 4 0 input).1.2.length ≠ input.length := by
  rw [active_calls 4 0 input input_nodup (by decide) (by decide)]
  decide

theorem duplicate_execution :
    run 4 3 ([7, 7, 7, 7] : List Nat) = ((some 7, [4]), 26) := by decide

theorem duplicates_are_not_four_calls :
    (run 4 3 ([7, 7, 7, 7] : List Nat)).1.2.length ≠ 4 := by
  rw [duplicate_execution]
  decide

theorem singleton_execution : run 1 0 ([-4] : List Int) = ((some (-4), [1]), 11) := by
  decide

theorem singleton_edges : (run 1 0 ([-4] : List Int)).1.2.length - 1 = 0 :=
  recursive_edges 1 0 [-4] (by decide) (by decide) (by decide)

theorem empty_execution : run 0 0 ([] : List Nat) = ((none, []), 1) := rfl

theorem invalid_value : (run 4 4 input).1.1 = none := by
  rw [run_value 4 4 input (by decide)]
  apply List.getElem?_eq_none_iff.mpr
  rw [(Applications.Selection.ordered_perm input).length_eq]

/-- A genuine infinite distinct family, with growing size and largest rank. -/
theorem range_worst_scan (n : Nat) :
    (run (n + 1) n (List.range (n + 1))).1.2.sum = (n + 1) * (n + 2) / 2 := by
  simpa only [List.length_range, Nat.add_sub_cancel, Nat.add_assoc] using
    largest_scan (n + 1) (List.range (n + 1)) List.nodup_range (by simp) (by simp)

theorem range_worst_calls (n : Nat) :
    (run (n + 1) n (List.range (n + 1))).1.2.length = n + 1 :=
  active_calls (n + 1) n (List.range (n + 1)) List.nodup_range (by simp) (by simp)

theorem range_worst_edges (n : Nat) :
    (run (n + 1) n (List.range (n + 1))).1.2.length - 1 = n :=
  recursive_edges (n + 1) n (List.range (n + 1)) List.nodup_range (by simp) (by simp)

theorem range_worst_quadratic (n : Nat) :
    (n + 1) ^ 2 ≤ 2 * (run (n + 1) n (List.range (n + 1))).2 ∧
      (run (n + 1) n (List.range (n + 1))).2 ≤ 11 * (n + 1) ^ 2 := by
  simpa only [List.length_range, Nat.add_sub_cancel] using
    largest_cost_quadratic (n + 1) (List.range (n + 1))
      List.nodup_range (by simp) (by simp)

/-- Fixed zero-based rank two has one uniform linear coefficient. -/
theorem fixed_third_linear (xs : List Int) (hn : xs.Nodup) (hk : 2 < xs.length) :
    xs.length ≤ (run xs.length 2 xs).2 ∧ (run xs.length 2 xs).2 ≤ 31 * xs.length :=
  fixed_rank_linear xs.length 2 xs hn hk (by omega)

end Examples.MinimumPivot
