-- Prepared only; no execution or actual-type credit.
-- Candidate: 9d4b622ff74ec012d49733ccc0c4c0849b57ade4
import Applications.Resources.SelectionRecurrence
import Examples.SelectionRecurrence

set_option autoImplicit false
set_option warningAsError true
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Resources.SelectionRecurrence.pivotSize
#check @Resources.SelectionRecurrence.sideSize
#check @Resources.SelectionRecurrence.pivotSize_lt_iff
#check @Resources.SelectionRecurrence.sideSize_lt_iff
#check @Resources.SelectionRecurrence.pivotSize_monotone
#check @Resources.SelectionRecurrence.sideSize_monotone
#check @Resources.SelectionRecurrence.F
#check @Resources.SelectionRecurrence.F_of_le_twenty
#check @Resources.SelectionRecurrence.F_of_twenty_lt
#check @Resources.SelectionRecurrence.base_le_F
#check @Resources.SelectionRecurrence.F_monotone
#check @Resources.SelectionRecurrence.pivotSize_eq_ceil
#check @Resources.SelectionRecurrence.sideSize_eq_ceil
#check @Resources.SelectionRecurrence.F_rounded
#check @Resources.SelectionRecurrence.exists_affine_bound
#check @Resources.SelectionRecurrence.F_isBigO
#check @Examples.SelectionRecurrence.zero_children
#check @Examples.SelectionRecurrence.scalar_cutoff_obstruction
#check @Examples.SelectionRecurrence.scalar_cutoff_fourteen
#check @Examples.SelectionRecurrence.first_recursive_children
#check @Examples.SelectionRecurrence.F_zero
#check @Examples.SelectionRecurrence.F_twenty
#check @Examples.SelectionRecurrence.F_twenty_one
#check @Examples.SelectionRecurrence.F_twenty_two
#check @Examples.SelectionRecurrence.first_recursive_is_not_base
#check @Examples.SelectionRecurrence.resize_across_cutoff
#check @Examples.SelectionRecurrence.all_smaller_children_uniform
#check @Examples.SelectionRecurrence.zero_requires_intercept
