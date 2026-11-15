import Applications.Selection.OutsidePivot
import Examples.OutsidePivot

set_option autoImplicit false
set_option warningAsError true
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Applications.Selection.OutsidePivot.partition3_below
#check @Applications.Selection.OutsidePivot.partition3_above
#check @Applications.Selection.OutsidePivot.dispatch_below
#check @Applications.Selection.OutsidePivot.dispatch_above
#check @Applications.Selection.OutsidePivot.runWith_step_below
#check @Applications.Selection.OutsidePivot.runWith_step_above
#check @Applications.Selection.OutsidePivot.runWith_below_none
#check @Applications.Selection.OutsidePivot.runWith_above_none
#check @Applications.Selection.OutsidePivot.not_pivotValid_below
#check @Applications.Selection.OutsidePivot.not_pivotValid_above
#check @Applications.Selection.OutsidePivot.selectWith_below_none
#check @Applications.Selection.OutsidePivot.selectWith_above_none
#check @Applications.Selection.OutsidePivot.runWith_below_ne_spec
#check @Applications.Selection.OutsidePivot.runWith_above_ne_spec
#check @Examples.OutsidePivot.below_partition
#check @Examples.OutsidePivot.above_partition
#check @Examples.OutsidePivot.below_dispatch_same_state
#check @Examples.OutsidePivot.above_dispatch_same_state
#check @Examples.OutsidePivot.below_both_endpoints
#check @Examples.OutsidePivot.above_both_endpoints
#check @Examples.OutsidePivot.negative_duplicate_input
#check @Examples.OutsidePivot.singleton_never_answers
#check @Examples.OutsidePivot.below_valid_answer_not_obtained
#check @Examples.OutsidePivot.above_valid_answer_not_obtained
#check @Examples.OutsidePivot.below_policy_rejected
#check @Examples.OutsidePivot.above_policy_rejected
#check @Examples.OutsidePivot.public_positive_boundary
#check @Examples.OutsidePivot.empty_has_no_valid_rank
#check @Examples.OutsidePivot.invalid_above_uses_empty_right
#check @Examples.OutsidePivot.in_range_policy_contrast
