-- Prepared only; exact immutable candidate binding is in candidate2.json.
import Applications.Resources.SelectionEnvelope
import Examples.SelectionEnvelope

set_option autoImplicit false
set_option warningAsError true
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Resources.SelectionEnvelope.tollCoefficient
#check @Resources.SelectionEnvelope.smallBudget
#check @Resources.SelectionEnvelope.envelope
#check @Resources.SelectionEnvelope.envelope_zero
#check @Resources.SelectionEnvelope.envelope_succ
#check @Resources.SelectionEnvelope.recursive_budget_le
#check @Resources.SelectionEnvelope.le_succ
#check @Resources.SelectionEnvelope.envelope_mono
#check @Resources.SelectionEnvelope.small_budget_le
#check @Resources.SelectionEnvelope.invalid_budget_le
#check @Resources.SelectionEnvelope.two_child_budget_le
#check @Resources.SelectionEnvelope.prefix_max_bound
#check @Examples.SelectionEnvelope.group_two_values
#check @Examples.SelectionEnvelope.group_five_values
#check @Examples.SelectionEnvelope.small_budget_values
#check @Examples.SelectionEnvelope.invalid_empty_bound
#check @Examples.SelectionEnvelope.charged_two_child_example
#check @Examples.SelectionEnvelope.nonshrinking_budget_exceeds
#check @Examples.SelectionEnvelope.actual_cutoff_prefix
#check @Examples.SelectionEnvelope.scalar_cutoff_prefix
