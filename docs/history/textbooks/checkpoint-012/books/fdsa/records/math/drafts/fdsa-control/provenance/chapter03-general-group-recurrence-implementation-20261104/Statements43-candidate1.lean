-- Prepared only; no execution or actual-type credit.
-- Candidate: 451766483f401f737f63184f730a7561deb7ccb3
import Applications.Resources.GroupSelectionRecurrence
import Examples.GroupSelectionRecurrence

set_option autoImplicit false
set_option warningAsError true
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Resources.GroupSelectionRecurrence.pivotFraction
#check @Resources.GroupSelectionRecurrence.sideFraction
#check @Resources.GroupSelectionRecurrence.fractions_pos
#check @Resources.GroupSelectionRecurrence.fraction_sum_eq
#check @Resources.GroupSelectionRecurrence.contracts_iff_half_gap
#check @Resources.GroupSelectionRecurrence.contracts_iff_five_le
#check @Resources.GroupSelectionRecurrence.odd_contracts_iff
#check @Resources.GroupSelectionRecurrence.even_contracts_iff
#check @Resources.GroupSelectionRecurrence.pivotChild
#check @Resources.GroupSelectionRecurrence.sideChild
#check @Resources.GroupSelectionRecurrence.pivotChild_one
#check @Resources.GroupSelectionRecurrence.pivotChild_monotone
#check @Resources.GroupSelectionRecurrence.sideChild_monotone
#check @Resources.GroupSelectionRecurrence.two_group_bound_le_child
#check @Resources.GroupSelectionRecurrence.cutoff
#check @Resources.GroupSelectionRecurrence.cutoff_threshold
#check @Resources.GroupSelectionRecurrence.children_lt
#check @Resources.GroupSelectionRecurrence.majorant
#check @Resources.GroupSelectionRecurrence.majorant_small
#check @Resources.GroupSelectionRecurrence.majorant_large
#check @Resources.GroupSelectionRecurrence.base_le_majorant
#check @Resources.GroupSelectionRecurrence.majorant_monotone
#check @Resources.GroupSelectionRecurrence.majorant_affine_bound
#check @Resources.GroupSelectionRecurrence.majorant_isBigO
#check @Resources.GroupSelectionRecurrence.rounded_group_affine_bound
#check @Examples.GroupSelectionRecurrence.zero_requires_positive_domain
#check @Examples.GroupSelectionRecurrence.singleton_group
#check @Examples.GroupSelectionRecurrence.group_two
#check @Examples.GroupSelectionRecurrence.groups_three_four
#check @Examples.GroupSelectionRecurrence.groups_five_six
#check @Examples.GroupSelectionRecurrence.all_odd_even_thresholds
#check @Examples.GroupSelectionRecurrence.explicit_cutoffs
#check @Examples.GroupSelectionRecurrence.first_five_children
#check @Examples.GroupSelectionRecurrence.first_six_children
#check @Examples.GroupSelectionRecurrence.zero_base_value
#check @Examples.GroupSelectionRecurrence.last_five_base
#check @Examples.GroupSelectionRecurrence.first_five_recurrence
#check @Examples.GroupSelectionRecurrence.first_six_recurrence
#check @Examples.GroupSelectionRecurrence.short_final_group_bound
#check @Examples.GroupSelectionRecurrence.zero_group_count_bound
#check @Examples.GroupSelectionRecurrence.uniform_resizing
#check @Examples.GroupSelectionRecurrence.positive_base_ne_all_input_linear
#check @Examples.GroupSelectionRecurrence.exact_book_F_specialization
