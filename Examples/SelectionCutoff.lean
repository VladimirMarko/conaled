import Applications.Resources.SelectionCutoff

/-! Connected boundary cases for the actual and scalar cutoffs. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SelectionCutoff
open Resources.SelectionCutoff Resources.Selection Resources.SelectionMedians
open Resources.SelectionRecurrence

theorem singleton_zero_cutoff :
    0 < ([(-4 : Int)]).length ∧
      ((([(-4 : Int)]).length ⌈/⌉ 5 - 1) / 2,
        (chunkMediansRun 5 [-4]).1) = (0, [-4]) :=
  zero_cutoff_self_pivot 5 (by decide) (-4 : Int)

theorem singleton_guarded_self_call :
    FirstPivotCall 5 0 (0, [(-4 : Int)]) (0, [-4]) :=
  zero_cutoff_self_call 5 (by decide) (-4 : Int)

theorem singleton_positive_cutoff_stops (child : Nat × List Int) :
    ¬ FirstPivotCall 5 1 child (0, [-4]) :=
  no_first_call_of_small 5 1 0 [-4] child (by decide)

theorem singleton_invalid_rank_stops (child : Nat × List Int) :
    ¬ FirstPivotCall 5 0 child (1, [-4]) :=
  no_first_call_of_invalid 5 0 1 [-4] child (by decide)

theorem zero_cutoff_recipe_not_wellFounded :
    ¬ WellFounded (FirstPivotCall (α := Int) 5 0) :=
  zero_cutoff_not_wellFounded 5 (by decide) (-4 : Int)

theorem five_cutoff_is_positive (cutoff : Nat) :
    (∀ xs : List Int, cutoff < xs.length →
      (chunkMediansRun 5 xs).1.length < xs.length) ↔ 1 ≤ cutoff :=
  actual_cutoff_iff 5 cutoff (by decide) (0 : Int)

theorem singleton_groups_preserve_duplicates :
    (chunkMediansRun 1 [(-3 : Int), 4, -3]).1 = [-3, 4, -3] ∧
      (((([(-3 : Int), 4, -3]).length ⌈/⌉ 1) - 1) / 2,
        (chunkMediansRun 1 [(-3 : Int), 4, -3]).1) = (1, [-3, 4, -3]) := by
  exact ⟨group_one_medians _, by
    simpa only [List.length_cons, List.length_nil] using
      group_one_self_pivot [(-3 : Int), 4, -3]⟩

theorem singleton_groups_obstruct_every_cutoff (cutoff : Nat) :
    ∃ xs : List Int, cutoff < xs.length ∧ (chunkMediansRun 1 xs).1 = xs :=
  group_one_has_no_cutoff cutoff (-4 : Int)

theorem singleton_group_duplicate_self_call :
    FirstPivotCall 1 0 (1, [(-3 : Int), 4, -3]) (1, [-3, 4, -3]) := by
  simpa only [List.length_cons, List.length_nil] using
    group_one_self_call 0 [(-3 : Int), 4, -3] (by decide)

theorem singleton_group_recipe_not_wellFounded (cutoff : Nat) :
    ¬ WellFounded (FirstPivotCall (α := Int) 1 cutoff) :=
  group_one_not_wellFounded cutoff (-4 : Int)

theorem two_groups_cutoff_one_value :
    (selectRunWith 2 1 (by decide) (by decide) 2 [3, 1, 2, 2]).1 = some 2 := by
  rw [cutoff_one_value]
  decide

theorem two_group_actual_children :
    ∃ p : Nat, (selectRunWith 2 1 (by decide) (by decide) 0
      (chunkMediansRun 2 [3, 1, 2, 2]).1).1 = some p ∧ p ∈ [3, 1, 2, 2] ∧
      (chunkMediansRun 2 [3, 1, 2, 2]).1.length < 4 ∧
      (Applications.Selection.partition3 p [3, 1, 2, 2]).1.length < 4 ∧
      (Applications.Selection.partition3 p [3, 1, 2, 2]).2.2.length < 4 := by
  simpa only [List.length_cons, List.length_nil] using
    recursive_children_decrease 2 1 (by decide) (by decide)
      ([3, 1, 2, 2] : List Nat) (by decide)

/-- The actual algorithm can use cutoff1 although the scalar side bound is5. -/
theorem actual_and_scalar_sizes_differ :
    (chunkMediansRun 5 ([3, 1] : List Nat)).1.length < 2 ∧ sideSize 2 = 5 := by
  constructor
  · simpa only [List.length_cons, List.length_nil] using
      (first_pivot_length_strict_iff 5 (by decide) ([3, 1] : List Nat)).mpr (by decide)
  · decide

theorem twelve_fails_scalar :
    ¬ (∀ n : Nat, 12 < n → pivotSize n < n ∧ sideSize n < n) := by
  rw [scalar_cutoff_iff]
  decide

theorem thirteen_suffices_scalar :
    ∀ n : Nat, 13 < n → pivotSize n < n ∧ sideSize n < n :=
  (scalar_cutoff_iff 13).mpr (by decide)

theorem twenty_budget_and_next_children :
    (20 * 20 + 4 * 20 + 3 : Nat) = 483 ∧
      (∀ n : Nat, n ≤ 20 → n * n + 4 * n + 3 ≤ 483) ∧
      pivotSize 21 < 21 ∧ sideSize 21 < 21 := by
  exact ⟨by decide, twenty_polynomial_budget, twenty_scalar_safe 21 (by decide)⟩

theorem descending_twenty_actual_budget :
    (selectRun 19 (List.range 20).reverse).2 ≤ 483 := by
  apply twenty_actual_base_budget
  · simp only [List.length_reverse, List.length_range]
    decide
  · simp only [List.length_reverse, List.length_range, le_refl]

end Examples.SelectionCutoff
