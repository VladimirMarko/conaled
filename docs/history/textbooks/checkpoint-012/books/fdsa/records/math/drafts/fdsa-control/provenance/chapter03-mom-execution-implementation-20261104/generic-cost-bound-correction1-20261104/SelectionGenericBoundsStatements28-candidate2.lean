/- Immutable candidate: 9e1c7fc6bce757d7bcfb5d114e2806b566c49330
Tree: f45cdd048ccf08e0ed3be2cc9db3e76d142bbdb3
Prepared public explicit-@ input; source author has not run Lean.
Private logical source claims and generated kernel scope remain in the inventory. -/
import Applications.Resources.SelectionGenericBounds
import Examples.SelectionGenericBounds
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Resources.Selection.chunkMediansRun_length_eq_groupPivotChild
#check @Resources.Selection.selectRunWith_pivot_size_bounds
#check @Resources.Selection.genericSelectionBase
#check @Resources.Selection.genericSelectionMajorant
#check @Resources.Selection.genericSelectionMajorant_small
#check @Resources.Selection.genericSelectionMajorant_large
#check @Resources.Selection.genericSelectionBase_le_majorant
#check @Resources.Selection.genericSelectionMajorant_monotone
#check @Resources.Selection.selectRunWith_cost_le_groupBase_of_prefix
#check @Resources.Selection.invalid_cost_le_groupMajorant
#check @Resources.Selection.selectRunWith_cost_le_groupMajorant_of_lt
#check @Resources.Selection.selectRunWith_cost_le_groupMajorant
#check @Resources.Selection.selectRunWith_exists_uniform_affine_bound
#check @Resources.Selection.selectRunWith_exists_uniform_linear_bound
#check @Resources.Selection.selectRunWith_family_isBigO
#check @Examples.SelectionGenericBounds.empty_every_sufficient_group
#check @Examples.SelectionGenericBounds.five_repeated_prefix
#check @Examples.SelectionGenericBounds.six_repeated_prefix
#check @Examples.SelectionGenericBounds.book_recurses_inside_scalar_prefix
#check @Examples.SelectionGenericBounds.first_five_recursive_budget
#check @Examples.SelectionGenericBounds.first_six_recursive_budget
#check @Examples.SelectionGenericBounds.actual_cutoff_above_scalar
#check @Examples.SelectionGenericBounds.invalid_above_scalar
#check @Examples.SelectionGenericBounds.three_four_threshold_semantics
#check @Examples.SelectionGenericBounds.odd_sufficient_uniform_family
#check @Examples.SelectionGenericBounds.even_sufficient_uniform_family
#check @Examples.SelectionGenericBounds.six_duplicate_integer_family
#check @Examples.SelectionGenericBounds.five_descending_family
