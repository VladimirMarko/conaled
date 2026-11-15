/- Candidate-bound explicit public statement input.
Candidate: a9ac654c5dc3454709adc3a519ea82794f42f427
Tree: eabe923655b9536c85d978c967f072577605d591
All39 public declarations;29 private logical source claims remain separately inventoried.
Prepared only; not executed by source author. -/
import Applications.Resources.Selection
import Examples.SelectionCosts
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Resources.Selection.selectRunWith
#check @Resources.Selection.selectRun
#check @Resources.Selection.selectRunWith_of_invalid
#check @Resources.Selection.selectRunWith_nil
#check @Resources.Selection.selectRunWith_exists
#check @Resources.Selection.selectRunWith_mem
#check @Resources.Selection.selectRunWith_small
#check @Resources.Selection.selectRunWith_step
#check @Resources.Selection.selectRunWith_cost_step
#check @Resources.Selection.selectRunWith_value
#check @Resources.Selection.selectRunWith_some_iff
#check @Resources.Selection.selectRunWith_none_iff
#check @Resources.Selection.selectRunWith_public
#check @Resources.Selection.selectRun_value
#check @Resources.Selection.selectRun_some_iff
#check @Resources.Selection.selectRun_none_iff
#check @Resources.Selection.selectRun_of_invalid
#check @Resources.Selection.selectRun_nil
#check @Resources.Selection.selectRun_small
#check @Resources.Selection.selectRun_step
#check @Resources.Selection.selectRun_cost_step
#check @Examples.SelectionCosts.empty_payload
#check @Examples.SelectionCosts.empty_arbitrary_rank
#check @Examples.SelectionCosts.singleton
#check @Examples.SelectionCosts.singleton_invalid
#check @Examples.SelectionCosts.cutoff_ascending
#check @Examples.SelectionCosts.cutoff_descending
#check @Examples.SelectionCosts.same_cutoff_value_different_work
#check @Examples.SelectionCosts.first_recursive_pivot
#check @Examples.SelectionCosts.first_recursive_left
#check @Examples.SelectionCosts.first_recursive_equal
#check @Examples.SelectionCosts.first_recursive_right
#check @Examples.SelectionCosts.first_recursive_invalid
#check @Examples.SelectionCosts.all_equal_first
#check @Examples.SelectionCosts.all_equal_last
#check @Examples.SelectionCosts.group_two_cutoff_one
#check @Examples.SelectionCosts.one_based_public_bridge
#check @Examples.SelectionCosts.monotone_payload_selection
#check @Examples.SelectionCosts.collapsed_payload
