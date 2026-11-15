/- Immutable candidate: be8a5ab11040d61f5f2f8aef7abf02da333049fc
Tree: dd9c3d765aabd09d147247aba938e59786244aa4
Prepared public explicit-@ input; source author has not run Lean.
Private logical source claims and generated kernel scope remain in the inventory. -/
import Applications.Resources.SelectionBounds
import Examples.SelectionBounds
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Resources.Selection.selectRunWith
#check @Resources.Selection.selectRun
#check @Resources.Selection.selectRunWith_of_invalid
#check @Resources.Selection.selectRunWith_nil
#check @Resources.Selection.selectRunWith_exists
#check @Resources.Selection.selectRunWith_mem
#check @Resources.Selection.selectRunWith_small
#check @Resources.Selection.selectRunWith_step
#check @Resources.Selection.selectRunWith_cost_step
#check @Resources.Selection.selectRunWith_value
#check @Resources.Selection.selectRunWith_some_iff
#check @Resources.Selection.selectRunWith_none_iff
#check @Resources.Selection.selectRunWith_public
#check @Resources.Selection.selectRun_value
#check @Resources.Selection.selectRun_some_iff
#check @Resources.Selection.selectRun_none_iff
#check @Resources.Selection.selectRun_of_invalid
#check @Resources.Selection.selectRun_nil
#check @Resources.Selection.selectRun_small
#check @Resources.Selection.selectRun_step
#check @Resources.Selection.selectRun_cost_step
#check @Examples.SelectionCosts.empty_payload
#check @Examples.SelectionCosts.empty_arbitrary_rank
#check @Examples.SelectionCosts.singleton
#check @Examples.SelectionCosts.singleton_invalid
#check @Examples.SelectionCosts.cutoff_ascending
#check @Examples.SelectionCosts.cutoff_descending
#check @Examples.SelectionCosts.same_cutoff_value_different_work
#check @Examples.SelectionCosts.first_recursive_pivot
#check @Examples.SelectionCosts.first_recursive_left
#check @Examples.SelectionCosts.first_recursive_equal
#check @Examples.SelectionCosts.first_recursive_right
#check @Examples.SelectionCosts.first_recursive_invalid
#check @Examples.SelectionCosts.all_equal_first
#check @Examples.SelectionCosts.all_equal_last
#check @Examples.SelectionCosts.group_two_cutoff_one
#check @Examples.SelectionCosts.one_based_public_bridge
#check @Examples.SelectionCosts.monotone_payload_selection
#check @Examples.SelectionCosts.collapsed_payload
#check @Resources.Selection.chunkMediansRun_length_eq_pivotSize
#check @Resources.Selection.selectRun_median_value
#check @Resources.Selection.selectRun_pivot_size_bounds
#check @Resources.Selection.selectRun_local_cost_bound
#check @Resources.Selection.selectRun_cost_le_F_of_lt
#check @Resources.Selection.invalid_cost_le_F
#check @Resources.Selection.selectRun_cost_le_F
#check @Resources.Selection.selectRun_exists_uniform_affine_bound
#check @Resources.Selection.selectRun_exists_uniform_linear_bound
#check @Resources.Selection.selectRun_family_isBigO
#check @Examples.SelectionBounds.empty_budget
#check @Examples.SelectionBounds.cutoff_descending_budget
#check @Examples.SelectionBounds.first_left_budget
#check @Examples.SelectionBounds.first_equal_budget
#check @Examples.SelectionBounds.first_right_budget
#check @Examples.SelectionBounds.invalid_above_cutoff_budget
#check @Examples.SelectionBounds.all_equal_budget
#check @Examples.SelectionBounds.next_scalar_level_budget
#check @Examples.SelectionBounds.first_pivot_side_budget
#check @Examples.SelectionBounds.first_local_budget
#check @Examples.SelectionBounds.duplicate_family_uniform
#check @Examples.SelectionBounds.descending_family_linear
