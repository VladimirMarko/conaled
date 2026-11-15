import Applications.Resources.HalvingSelection
import Applications.Resources.MedianPolicy
import Examples.MedianPolicy

/- Prepared explicit-argument type capture for candidate e40d1f7fa71e51946b29bf1415067240e7cc369a.
No capture has run; this file is an input, not emitted type evidence. -/
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.width 120
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Resources.HalvingSelection.HalvingPolicy
#check @Resources.HalvingSelection.runWith_trace
#check @Resources.HalvingSelection.runWith_scan_bounds
#check @Resources.HalvingSelection.runWith_edges_log
#check @Resources.HalvingSelection.runWith_edges_clog
#check @Resources.HalvingSelection.runWith_singleton_trace
#check @Resources.HalvingSelection.runWith_tariff
#check @Resources.HalvingSelection.runWith_linear_cost
#check @Resources.MedianPolicy.pivotRun
#check @Resources.MedianPolicy.pivotRun_value
#check @Resources.MedianPolicy.pivotRun_cost
#check @Resources.MedianPolicy.pivotRun_some_iff
#check @Resources.MedianPolicy.pivotRun_none
#check @Resources.MedianPolicy.pivot_valid
#check @Resources.MedianPolicy.pivot_halving
#check @Resources.MedianPolicy.pivotRun_small
#check @Resources.MedianPolicy.pivotRun_singleton
#check @Resources.MedianPolicy.pivotRun_exists_uniform_linear_bound
#check @Resources.MedianPolicy.run
#check @Resources.MedianPolicy.run_value
#check @Resources.MedianPolicy.run_some_iff
#check @Resources.MedianPolicy.run_none
#check @Resources.MedianPolicy.run_trace
#check @Resources.MedianPolicy.run_scan_bounds
#check @Resources.MedianPolicy.run_edges_log
#check @Resources.MedianPolicy.run_edges_clog
#check @Resources.MedianPolicy.run_singleton_trace
#check @Resources.MedianPolicy.run_singleton
#check @Resources.MedianPolicy.run_exists_uniform_linear_bound
#check @Examples.MedianPolicy.pivot_two
#check @Examples.MedianPolicy.pivot_four
#check @Examples.MedianPolicy.pivot_eight
#check @Examples.MedianPolicy.pivot_three
#check @Examples.MedianPolicy.pivot_seven
#check @Examples.MedianPolicy.pivot_four_initial
#check @Examples.MedianPolicy.pivot_duplicates
#check @Examples.MedianPolicy.two_execution
#check @Examples.MedianPolicy.four_tail_execution
#check @Examples.MedianPolicy.eight_execution
#check @Examples.MedianPolicy.eight_trace_connected
#check @Examples.MedianPolicy.eight_scan
#check @Examples.MedianPolicy.eight_edges
#check @Examples.MedianPolicy.eight_edges_bound
#check @Examples.MedianPolicy.three_tail_execution
#check @Examples.MedianPolicy.seven_execution
#check @Examples.MedianPolicy.seven_scan_bounds
#check @Examples.MedianPolicy.seven_edges_strict_clog
#check @Examples.MedianPolicy.early_equal_execution
#check @Examples.MedianPolicy.early_equal_edges
#check @Examples.MedianPolicy.lower_branch_execution
#check @Examples.MedianPolicy.duplicate_execution
#check @Examples.MedianPolicy.duplicate_trace_connected
#check @Examples.MedianPolicy.singleton_execution
#check @Examples.MedianPolicy.singleton_trace_connected
#check @Examples.MedianPolicy.singleton_active_and_edges
#check @Examples.MedianPolicy.empty_execution
#check @Examples.MedianPolicy.invalid_value
#check @Examples.MedianPolicy.range_scan_bound
#check @Examples.MedianPolicy.range_edge_bound
#check @Examples.MedianPolicy.all_integer_inputs_linear
