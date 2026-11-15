/- Immutable cutoff candidate 96c99a18a1f4ad28bbb8d13a17cbefb1899d8ab9; tree c80cbd0f056980069634e5b3ad7d53ea429b733e. Prepared input only. -/
import Applications.Resources.SelectionCutoff
import Examples.SelectionCutoff
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Resources.SelectionCutoff.FirstPivotCall
#check @Resources.SelectionCutoff.no_first_call_of_invalid
#check @Resources.SelectionCutoff.no_first_call_of_small
#check @Resources.SelectionCutoff.one_ceil_div
#check @Resources.SelectionCutoff.ceil_div_strict_iff
#check @Resources.SelectionCutoff.first_pivot_length_strict_iff
#check @Resources.SelectionCutoff.actual_cutoff_iff
#check @Resources.SelectionCutoff.lowerMedianValue_singleton
#check @Resources.SelectionCutoff.singleton_medians
#check @Resources.SelectionCutoff.zero_cutoff_self_pivot
#check @Resources.SelectionCutoff.zero_cutoff_self_call
#check @Resources.SelectionCutoff.zero_cutoff_not_wellFounded
#check @Resources.SelectionCutoff.group_one_medians
#check @Resources.SelectionCutoff.group_one_self_pivot
#check @Resources.SelectionCutoff.group_one_has_no_cutoff
#check @Resources.SelectionCutoff.group_one_self_call
#check @Resources.SelectionCutoff.group_one_not_wellFounded
#check @Resources.SelectionCutoff.recursive_children_decrease
#check @Resources.SelectionCutoff.cutoff_one_value
#check @Resources.SelectionCutoff.scalar_cutoff_iff
#check @Resources.SelectionCutoff.twenty_scalar_safe
#check @Resources.SelectionCutoff.twenty_polynomial_budget
#check @Resources.SelectionCutoff.twenty_actual_base_budget
#check @Examples.SelectionCutoff.singleton_zero_cutoff
#check @Examples.SelectionCutoff.singleton_guarded_self_call
#check @Examples.SelectionCutoff.singleton_positive_cutoff_stops
#check @Examples.SelectionCutoff.singleton_invalid_rank_stops
#check @Examples.SelectionCutoff.zero_cutoff_recipe_not_wellFounded
#check @Examples.SelectionCutoff.five_cutoff_is_positive
#check @Examples.SelectionCutoff.singleton_groups_preserve_duplicates
#check @Examples.SelectionCutoff.singleton_groups_obstruct_every_cutoff
#check @Examples.SelectionCutoff.singleton_group_duplicate_self_call
#check @Examples.SelectionCutoff.singleton_group_recipe_not_wellFounded
#check @Examples.SelectionCutoff.two_groups_cutoff_one_value
#check @Examples.SelectionCutoff.two_group_actual_children
#check @Examples.SelectionCutoff.actual_and_scalar_sizes_differ
#check @Examples.SelectionCutoff.twelve_fails_scalar
#check @Examples.SelectionCutoff.thirteen_suffices_scalar
#check @Examples.SelectionCutoff.twenty_budget_and_next_children
#check @Examples.SelectionCutoff.descending_twenty_actual_budget
