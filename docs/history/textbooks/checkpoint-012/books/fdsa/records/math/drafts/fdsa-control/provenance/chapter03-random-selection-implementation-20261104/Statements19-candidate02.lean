import Examples.RandomSelection

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Resources.RandomSelection.pivotRun
#check @Resources.RandomSelection.pivotRun_exact
#check @Resources.RandomSelection.stepRun
#check @Resources.RandomSelection.stepRun_eq
#check @Resources.RandomSelection.stepRun_child
#check @Resources.RandomSelection.stepRun_semantics
#check @Resources.RandomSelection.stepRun_ranked
#check @Resources.RandomSelection.stepRun_cost_bounds
#check @Resources.RandomSelection.pivotLaw
#check @Resources.RandomSelection.pivotLaw_support
#check @Resources.RandomSelection.pivotLaw_event
#check @Examples.RandomSelection.singleton_step
#check @Examples.RandomSelection.duplicate_middle
#check @Examples.RandomSelection.selected_side_is_not_larger_side
#check @Examples.RandomSelection.selected_side_valid
#check @Examples.RandomSelection.duplicate_ranked
#check @Examples.RandomSelection.duplicate_source_bound
#check @Examples.RandomSelection.duplicate_zero_probability
#check @Examples.RandomSelection.duplicate_one_probability
