/- Immutable candidate: 42885f0d87f795252ee50dd01dc9220cfeb20a35
Tree: 3eaf4978a860921249d40774980f5ae0eaaf2ff5
Prepared public explicit-@ input; source author has not run Lean.
Private logical source claims and generated kernel scope remain in the inventory. -/
import Applications.Resources.SelectionGenericEnvelope
import Examples.SelectionGenericEnvelope
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Resources.Selection.selectRunWith_median_value
#check @Resources.Selection.chunkMediansRun_proper_size
#check @Resources.Selection.selectRunWith_local_cost_bound
#check @Resources.Selection.selectRunWith_cost_le_envelope_of_lt
#check @Resources.Selection.selectRunWith_cost_le_envelope
#check @Resources.Selection.selectRunWith_uniform_prefix_bound
#check @Examples.SelectionGenericEnvelope.empty_any_group
#check @Examples.SelectionGenericEnvelope.group_two_budget
#check @Examples.SelectionGenericEnvelope.group_three_budget
#check @Examples.SelectionGenericEnvelope.group_four_budget
#check @Examples.SelectionGenericEnvelope.group_five_budget
#check @Examples.SelectionGenericEnvelope.group_six_budget
#check @Examples.SelectionGenericEnvelope.group_three_invalid
#check @Examples.SelectionGenericEnvelope.larger_cutoff_budget
#check @Examples.SelectionGenericEnvelope.group_three_left
#check @Examples.SelectionGenericEnvelope.group_three_right
#check @Examples.SelectionGenericEnvelope.integer_prefix
