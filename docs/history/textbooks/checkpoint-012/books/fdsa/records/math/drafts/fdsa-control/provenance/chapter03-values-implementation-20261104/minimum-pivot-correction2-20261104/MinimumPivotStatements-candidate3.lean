-- Prepared for immutable candidate d0479dd03371f1c1f0b41dff5f1882a36206f40a.
-- Exhaustive public explicit-@ capture input; actual type execution pending.
-- No new named private helpers; generated declarations remain audit scope.
import Examples.MinimumPivot

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.width 120
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Resources.SelectionPolicy.Observed
#check @Resources.SelectionPolicy.prepend
#check @Resources.SelectionPolicy.runWith
#check @Resources.SelectionPolicy.runWith_zero
#check @Resources.SelectionPolicy.runWith_nil
#check @Resources.SelectionPolicy.runWith_step
#check @Resources.SelectionPolicy.runWith_value
#check @Resources.SelectionPolicy.runWith_correct
#check @Resources.MinimumPivot.run
#check @Resources.MinimumPivot.policy_valid
#check @Resources.MinimumPivot.run_value
#check @Resources.MinimumPivot.minimum_bucket_sizes
#check @Resources.MinimumPivot.run_zero_rank
#check @Resources.MinimumPivot.run_succ_rank
#check @Resources.MinimumPivot.sizes
#check @Resources.MinimumPivot.sizes_length
#check @Resources.MinimumPivot.run_observations
#check @Resources.MinimumPivot.run_trace
#check @Resources.MinimumPivot.active_calls
#check @Resources.MinimumPivot.recursive_edges
#check @Resources.MinimumPivot.sizes_sum_double
#check @Resources.MinimumPivot.sizes_sum
#check @Resources.MinimumPivot.sizes_sum_bounds
#check @Resources.MinimumPivot.scan_exact
#check @Resources.MinimumPivot.cost_exact
#check @Resources.MinimumPivot.fixed_rank_linear
#check @Resources.MinimumPivot.largest_scan_double
#check @Resources.MinimumPivot.largest_scan
#check @Resources.MinimumPivot.largest_cost_quadratic
#check @Examples.MinimumPivot.input
#check @Examples.MinimumPivot.input_nodup
#check @Examples.MinimumPivot.middle_execution
#check @Examples.MinimumPivot.middle_trace
#check @Examples.MinimumPivot.middle_calls
#check @Examples.MinimumPivot.middle_edges
#check @Examples.MinimumPivot.middle_scan
#check @Examples.MinimumPivot.middle_cost
#check @Examples.MinimumPivot.largest_execution
#check @Examples.MinimumPivot.largest_scan_connected
#check @Examples.MinimumPivot.minimum_execution
#check @Examples.MinimumPivot.minimum_is_not_four_calls
#check @Examples.MinimumPivot.duplicate_execution
#check @Examples.MinimumPivot.duplicates_are_not_four_calls
#check @Examples.MinimumPivot.singleton_execution
#check @Examples.MinimumPivot.singleton_edges
#check @Examples.MinimumPivot.empty_execution
#check @Examples.MinimumPivot.invalid_value
#check @Examples.MinimumPivot.range_worst_scan
#check @Examples.MinimumPivot.range_worst_calls
#check @Examples.MinimumPivot.range_worst_edges
#check @Examples.MinimumPivot.range_worst_quadratic
#check @Examples.MinimumPivot.fixed_third_linear
