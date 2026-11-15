-- Prepared only; no execution or actual-type credit from this input.
-- Candidate: 95406b83968e5b438e206c06f9797804664e0170
import Applications.Resources.RoundedRecurrence
import Examples.RoundedRecurrence
import Applications.Resources.RoundedRecurrenceBounds
import Examples.RoundedRecurrenceBounds

set_option autoImplicit false
set_option warningAsError true
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Resources.RoundedRecurrence.ceil_affine_lt_add_one
#check @Resources.RoundedRecurrence.ceil_affine_lt_of_threshold
#check @Resources.RoundedRecurrence.thresholds_of_combined_cutoff
#check @Resources.RoundedRecurrence.ceil_children_lt
#check @Resources.RoundedRecurrence.cutoff_denominator_pos
#check @Resources.RoundedRecurrence.slope_nonneg_and_margin
#check @Resources.RoundedRecurrence.sharp_affine_absorption
#check @Resources.RoundedRecurrence.recurrence_step_le
#check @Examples.RoundedRecurrence.negative_argument_truncation
#check @Examples.RoundedRecurrence.signed_offset_descent
#check @Examples.RoundedRecurrence.combined_signed_descent
#check @Examples.RoundedRecurrence.zero_recurrence
#check @Examples.RoundedRecurrence.strict_slope_choice_counterexample
#check @Examples.RoundedRecurrence.zero_recurrence_bound_step
#check @Examples.RoundedRecurrence.negative_intercept_bound_step
#check @Examples.RoundedRecurrence.negative_toll_and_intercept
#check @Resources.RoundedRecurrence.explicit_cutoff_bounds
#check @Resources.RoundedRecurrence.affine_bound_of_prefix
#check @Resources.RoundedRecurrence.bound_with_source_constants
#check @Resources.RoundedRecurrence.exists_affine_bound
#check @Resources.RoundedRecurrence.exists_affine_bound_nat
#check @Examples.RoundedRecurrenceBounds.zero_source_witness_bound
#check @Examples.RoundedRecurrenceBounds.negative_intercept_all_inputs
#check @Examples.RoundedRecurrenceBounds.negative_constant_toll_affine_bound
#check @Examples.RoundedRecurrenceBounds.roundedQuarter
#check @Examples.RoundedRecurrenceBounds.roundedQuarter_of_le_five
#check @Examples.RoundedRecurrenceBounds.roundedQuarter_of_five_lt
#check @Examples.RoundedRecurrenceBounds.roundedQuarter_zero
#check @Examples.RoundedRecurrenceBounds.roundedQuarter_five
#check @Examples.RoundedRecurrenceBounds.roundedQuarter_six
#check @Examples.RoundedRecurrenceBounds.roundedQuarter_twenty_one
#check @Examples.RoundedRecurrenceBounds.roundedQuarter_sharp_affine_bound
#check @Examples.RoundedRecurrenceBounds.roundedQuarter_real_affine_bound
#check @Examples.RoundedRecurrenceBounds.roundedQuarter_nat_affine_bound
#check @Examples.RoundedRecurrenceBounds.noncontracting_affine_step_impossible
