import Examples.RandomSelection
import Examples.RandomSelectionRun

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
#check @Resources.RandomSelection.Trace
#check @Resources.RandomSelection.Outcome
#check @Resources.RandomSelection.scanVolume
#check @Resources.RandomSelection.scanVolume_nil
#check @Resources.RandomSelection.scanVolume_cons
#check @Resources.RandomSelection.prepend
#check @Resources.RandomSelection.run
#check @Resources.RandomSelection.run_nil
#check @Resources.RandomSelection.run_cons
#check @Resources.RandomSelection.run_value
#check @Resources.RandomSelection.run_ranked
#check @Resources.RandomSelection.run_none
#check @Resources.RandomSelection.run_valid
#check @Resources.RandomSelection.run_active_calls_le
#check @Resources.RandomSelection.run_initial_scan_le
#check @Resources.RandomSelection.run_scanVolume_le
#check @Resources.RandomSelection.run_source_bridge
#check @Resources.RandomSelection.run_trace_entries
#check @Resources.RandomSelection.run_source_quadratic
#check @Resources.RandomSelection.select
#check @Resources.RandomSelection.select_value
#check @Resources.RandomSelection.select_none
#check @Resources.RandomSelection.select_some_iff
#check @Resources.RandomSelection.scanLaw
#check @Resources.RandomSelection.sourceLaw
#check @Resources.RandomSelection.scanLaw_support
#check @Resources.RandomSelection.scanLaw_support_finite
#check @Resources.RandomSelection.sourceLaw_support
#check @Resources.RandomSelection.sourceLaw_support_finite
#check @Examples.RandomSelectionRun.empty_failure
#check @Examples.RandomSelectionRun.singleton_execution
#check @Examples.RandomSelectionRun.invalid_singleton
#check @Examples.RandomSelectionRun.rank_zero_public_failure
#check @Examples.RandomSelectionRun.two_key_execution
#check @Examples.RandomSelectionRun.duplicate_execution
#check @Examples.RandomSelectionRun.two_key_first_path
#check @Examples.RandomSelectionRun.two_key_long_path
#check @Examples.RandomSelectionRun.same_value_different_scan
#check @Examples.RandomSelectionRun.maximum_scan_on_pair
#check @Examples.RandomSelectionRun.bounded_actual_pair_calls
#check @Examples.RandomSelectionRun.arbitrary_supported_rank
