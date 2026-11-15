-- Prepared only: rounded recurrence first slice, no execution or type credit.
-- Candidate: a4cd1b6b53fdab38eab40433c3fd60293fdc054f
import Applications.Resources.RoundedRecurrence
import Examples.RoundedRecurrence

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
