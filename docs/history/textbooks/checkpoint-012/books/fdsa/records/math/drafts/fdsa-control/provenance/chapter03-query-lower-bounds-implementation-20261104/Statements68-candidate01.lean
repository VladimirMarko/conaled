import Examples.CoordinateSensitivity
import Examples.CoordinateQueries

/- Prepared for 6c66b545f7f7e2e15a274a67a867d8ddc7f980c3. No actual type output is claimed by this input. -/
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Applications.Selection.CoordinateSensitivity.ordered_index_injective
#check @Applications.Selection.CoordinateSensitivity.exists_fresh_set_changes
#check @Applications.Selection.CoordinateSensitivity.exists_set_changes
#check @Applications.Selection.CoordinateSensitivity.sortSelect_set_changes
#check @Applications.Selection.CoordinateSensitivity.selectWith_set_changes
#check @Applications.Selection.CoordinateSensitivity.ofFn_update
#check @Applications.Selection.CoordinateSensitivity.exists_update_changes
#check @Applications.Selection.CoordinateQueries.Transcript
#check @Applications.Selection.CoordinateQueries.Protocol
#check @Applications.Selection.CoordinateQueries.Runs
#check @Applications.Selection.CoordinateQueries.Runs.done
#check @Applications.Selection.CoordinateQueries.Runs.query
#check @Applications.Selection.CoordinateQueries.Total
#check @Applications.Selection.CoordinateQueries.Runs.answers
#check @Applications.Selection.CoordinateQueries.Runs.replay
#check @Applications.Selection.CoordinateQueries.Runs.replay_update_of_not_mem
#check @Applications.Selection.CoordinateQueries.Runs.deterministic
#check @Applications.Selection.CoordinateQueries.Selects
#check @Applications.Selection.CoordinateQueries.Runs.queries_all
#check @Applications.Selection.CoordinateQueries.Runs.length_lower_bound
#check @Applications.Selection.CoordinateQueries.queryWork
#check @Applications.Selection.CoordinateQueries.queryWork_nil
#check @Applications.Selection.CoordinateQueries.queryWork_cons
#check @Applications.Selection.CoordinateQueries.queryWork_unit
#check @Applications.Selection.CoordinateQueries.queryWork_constant
#check @Applications.Selection.CoordinateQueries.length_le_queryWork
#check @Applications.Selection.CoordinateQueries.Runs.work_lower_bound
#check @Applications.Selection.CoordinateQueries.Runs.resource_lower_bound
#check @Applications.Selection.CoordinateQueries.exists_linear_run
#check @Applications.Selection.CoordinateQueries.linear_worst_case_bound
#check @Applications.Selection.CoordinateQueries.linear_isBigO_of_query_bound
#check @Examples.CoordinateSensitivity.middle_of_triple
#check @Examples.CoordinateSensitivity.every_triple_coordinate
#check @Examples.CoordinateSensitivity.triple_fresh_witness
#check @Examples.CoordinateSensitivity.above_coordinate_replaced
#check @Examples.CoordinateSensitivity.below_coordinate_replaced
#check @Examples.CoordinateSensitivity.selected_coordinate_replaced
#check @Examples.CoordinateSensitivity.singleton_sensitive
#check @Examples.CoordinateSensitivity.valid_ranks_are_injective
#check @Examples.CoordinateSensitivity.invalid_ranks_agree
#check @Examples.CoordinateSensitivity.one_based_middle_changes
#check @Examples.CoordinateSensitivity.last_pivot_middle_changes
#check @Examples.CoordinateSensitivity.finite_coordinate_adapter
#check @Examples.CoordinateSensitivity.increasing_input_sensitive
#check @Examples.CoordinateQueries.oneQuery
#check @Examples.CoordinateQueries.oneQuery_run
#check @Examples.CoordinateQueries.oneQuery_total
#check @Examples.CoordinateQueries.oneQuery_correct
#check @Examples.CoordinateQueries.oneQuery_every_run
#check @Examples.CoordinateQueries.repeatNegative
#check @Examples.CoordinateQueries.repeatNegative_negative_run
#check @Examples.CoordinateQueries.repeatNegative_nonnegative_run
#check @Examples.CoordinateQueries.repeatNegative_total
#check @Examples.CoordinateQueries.repeatNegative_correct
#check @Examples.CoordinateQueries.repeated_negative_charges
#check @Examples.CoordinateQueries.nonnegative_single_charge
#check @Examples.CoordinateQueries.adaptive_run_lower_bound
#check @Examples.CoordinateQueries.pairMinimum
#check @Examples.CoordinateQueries.pairMinimum_run
#check @Examples.CoordinateQueries.pairMinimum_total
#check @Examples.CoordinateQueries.pair_minimum_ranked
#check @Examples.CoordinateQueries.pairMinimum_correct
#check @Examples.CoordinateQueries.pairMinimum_distinct_coverage
#check @Examples.CoordinateQueries.pairMinimum_distinct_lower_bound
#check @Examples.CoordinateQueries.pairMinimum_measured_contract
#check @Examples.CoordinateQueries.unqueried_update_replays
#check @Examples.CoordinateQueries.total_correct_protocol_has_witness
#check @Examples.CoordinateQueries.any_uniform_query_bound_is_linear
