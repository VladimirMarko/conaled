import Applications.Resources.SelectionBounds
import Examples.SelectionCosts
import Examples.SelectionRecurrence

/-! Actual execution counts connected to the book's scalar and uniform bounds.
The exact20/21 counts come from the existing public execution examples. The
size25 scalar has its first recursive child above the finite base; the bound
there is asserted for every rank, without claiming a new exact25 count.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SelectionBounds
open Applications.Selection
open Resources.Selection Resources.SelectionMedians Resources.SelectionRecurrence

theorem empty_budget :
    (selectRun 0 ([] : List (Fin 0))).2 = 2 ∧
      (selectRun 0 ([] : List (Fin 0))).2 ≤ 483 := by
  constructor
  · exact congrArg Prod.snd Examples.SelectionCosts.empty_payload
  · simpa only [List.length_nil, Examples.SelectionRecurrence.F_zero] using
      selectRun_cost_le_F 0 ([] : List (Fin 0))

theorem cutoff_descending_budget :
    (selectRun 19 (List.range 20).reverse).2 = 273 ∧
      (selectRun 19 (List.range 20).reverse).2 ≤ 483 := by
  constructor
  · exact congrArg Prod.snd Examples.SelectionCosts.cutoff_descending
  · simpa only [List.length_reverse, List.length_range,
      Examples.SelectionRecurrence.F_twenty] using
      selectRun_cost_le_F 19 (List.range 20).reverse

theorem first_left_budget :
    (selectRun 0 (List.range 21)).2 = 269 ∧
      (selectRun 0 (List.range 21)).2 ≤ 1419 := by
  constructor
  · exact congrArg Prod.snd Examples.SelectionCosts.first_recursive_left
  · simpa only [List.length_range, Examples.SelectionRecurrence.F_twenty_one] using
      selectRun_cost_le_F 0 (List.range 21)

theorem first_equal_budget :
    (selectRun 12 (List.range 21)).2 = 231 ∧
      (selectRun 12 (List.range 21)).2 ≤ 1419 := by
  constructor
  · exact congrArg Prod.snd Examples.SelectionCosts.first_recursive_equal
  · simpa only [List.length_range, Examples.SelectionRecurrence.F_twenty_one] using
      selectRun_cost_le_F 12 (List.range 21)

theorem first_right_budget :
    (selectRun 20 (List.range 21)).2 = 266 ∧
      (selectRun 20 (List.range 21)).2 ≤ 1419 := by
  constructor
  · exact congrArg Prod.snd Examples.SelectionCosts.first_recursive_right
  · simpa only [List.length_range, Examples.SelectionRecurrence.F_twenty_one] using
      selectRun_cost_le_F 20 (List.range 21)

theorem invalid_above_cutoff_budget :
    selectRun 100 (List.range 21) = (none, 23) ∧
      (selectRun 100 (List.range 21)).2 ≤ 1419 := by
  constructor
  · exact selectRun_of_invalid 100 _ (by decide)
  · simpa only [List.length_range, Examples.SelectionRecurrence.F_twenty_one] using
      selectRun_cost_le_F 100 (List.range 21)

theorem all_equal_budget :
    (selectRun 20 (List.replicate 21 4)).2 = 239 ∧
      (selectRun 20 (List.replicate 21 4)).2 ≤ 1419 := by
  constructor
  · exact congrArg Prod.snd Examples.SelectionCosts.all_equal_last
  · simpa only [List.length_replicate, Examples.SelectionRecurrence.F_twenty_one] using
      selectRun_cost_le_F 20 (List.replicate 21 4)

/-- The first recursive scalar child contributes1419 rather than483. -/
theorem next_scalar_level_budget :
    F 25 = 2431 ∧ ∀ k : Nat, (selectRun k (List.range 25)).2 ≤ 2431 := by
  have hf : F 25 = 2431 := by
    rw [F_of_twenty_lt 25 (by decide)]
    change F 5 + F 21 + 475 + 54 = 2431
    rw [F_of_le_twenty 5 (by decide), Examples.SelectionRecurrence.F_twenty_one]
  refine ⟨hf, ?_⟩
  intro k
  simpa only [List.length_range, hf] using selectRun_cost_le_F k (List.range 25)

theorem first_pivot_side_budget :
    (partition3 12 (List.range 21)).1.length ≤ 18 ∧
      (partition3 12 (List.range 21)).2.2.length ≤ 18 := by
  have hp : (selectRun ((((List.range 21).length ⌈/⌉ 5) - 1) / 2)
      (chunkMediansRun 5 (List.range 21)).1).1 = some 12 := by
    rw [Examples.SelectionMedians.first_recursive_size]
    norm_num only [List.length_range, Nat.ceilDiv_eq_add_pred_div]
    exact congrArg Prod.fst Examples.SelectionCosts.first_recursive_pivot
  simpa only [List.length_range, sideSize] using
    selectRun_pivot_size_bounds (List.range 21) 12 hp

theorem first_local_budget :
    1 + (Resources.SymmetricCosts.lengthRun (List.range 21)).2 +
      (chunkMediansRun 5 (List.range 21)).2 +
      (Resources.Partition.partitionRun 12 (List.range 21)).2 +
      (Resources.SymmetricCosts.lengthRun (partition3 12 (List.range 21)).1).2 +
      (Resources.SymmetricCosts.lengthRun (partition3 12 (List.range 21)).2.1).2 ≤ 453 := by
  simpa only [List.length_range] using selectRun_local_cost_bound (List.range 21) 12

/-- The constants are shared by all duplicate-list sizes and all ranks. -/
theorem duplicate_family_uniform :
    ∃ A B : Nat, ∀ n k : Nat,
      (selectRun k (List.replicate n 4)).2 ≤ A * n + B := by
  obtain ⟨A, B, bound⟩ := selectRun_exists_uniform_affine_bound
  refine ⟨A, B, ?_⟩
  intro n k
  simpa only [List.length_replicate] using bound Nat (List.replicate n 4) k

/-- A family with descending inputs and last valid ranks uses actual counts;
the n=0 optional extension is covered by the same proved family theorem. -/
theorem descending_family_linear :
    Asymptotics.IsBigO Filter.atTop
      (fun n : Nat => ((selectRun (n - 1) (List.range n).reverse).2 : ℝ))
      (fun n => (n : ℝ)) :=
  selectRun_family_isBigO (fun n => (List.range n).reverse) (fun n => n - 1)
    (by intro n; simp only [List.length_reverse, List.length_range])

end Examples.SelectionBounds
