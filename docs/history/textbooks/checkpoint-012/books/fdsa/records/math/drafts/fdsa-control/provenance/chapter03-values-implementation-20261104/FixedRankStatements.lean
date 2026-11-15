-- Prepared, unexecuted type input for immutable candidate fd490573dc6a0ad2ed4a6f3d449e03d9d1b0bb2f.
-- All 86 new public names; source identities are in fixed-rank-inventory.json.
import Applications.Selection.FixedRank
import Applications.Resources.FixedRank
import Examples.FixedRankSelection

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.width 120
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Applications.Selection.FixedRank.minimumLoop
#check @Applications.Selection.FixedRank.select0
#check @Applications.Selection.FixedRank.minimumLoop_spec
#check @Applications.Selection.FixedRank.select0_none_iff
#check @Applications.Selection.FixedRank.select0_some_iff_min
#check @Applications.Selection.FixedRank.select0_value
#check @Applications.Selection.FixedRank.select0_some_iff_ranked
#check @Applications.Selection.FixedRank.select0_pivot_valid
#check @Applications.Selection.FixedRank.select0_spec
#check @Applications.Selection.FixedRank.secondLoop
#check @Applications.Selection.FixedRank.select1
#check @Applications.Selection.FixedRank.boundedInsert
#check @Applications.Selection.FixedRank.boundedInsert_length_le
#check @Applications.Selection.FixedRank.ordered_cons_eq_insert
#check @Applications.Selection.FixedRank.boundedInsert_prefix
#check @Applications.Selection.FixedRank.prefixLoop
#check @Applications.Selection.FixedRank.prefixLoop_prefix
#check @Applications.Selection.FixedRank.takeSort
#check @Applications.Selection.FixedRank.takeSort_value
#check @Applications.Selection.FixedRank.takeSort_length
#check @Applications.Selection.FixedRank.selectFixed
#check @Applications.Selection.FixedRank.selectFixed_value
#check @Applications.Selection.FixedRank.selectFixed_some_iff_ranked
#check @Applications.Selection.FixedRank.selectFixed_some_iff_count_bounds
#check @Applications.Selection.FixedRank.selectFixed_none_iff
#check @Applications.Selection.FixedRank.selectFixed_spec
#check @Applications.Selection.FixedRank.selectFixed_eq_selectWith
#check @Applications.Selection.FixedRank.select0_eq_selectFixed
#check @Applications.Selection.FixedRank.boundedInsert_two
#check @Applications.Selection.FixedRank.prefixLoop_two
#check @Applications.Selection.FixedRank.boundedInsert_singleton
#check @Applications.Selection.FixedRank.select1_eq_selectFixed
#check @Applications.Selection.FixedRank.select1_value
#check @Applications.Selection.FixedRank.select1_some_iff_ranked
#check @Applications.Selection.FixedRank.select1_none_iff
#check @Applications.Selection.FixedRank.select1_spec
#check @Resources.FixedRank.minimumLoopRun
#check @Resources.FixedRank.minimumLoopRun_value
#check @Resources.FixedRank.minimumLoopRun_cost
#check @Resources.FixedRank.select0Run
#check @Resources.FixedRank.select0Run_value
#check @Resources.FixedRank.select0Run_cost
#check @Resources.FixedRank.select0Run_exact
#check @Resources.FixedRank.boundedInsertRun
#check @Resources.FixedRank.boundedInsertRun_value
#check @Resources.FixedRank.boundedInsertRun_cost
#check @Resources.FixedRank.boundedInsertRun_cost_le
#check @Resources.FixedRank.boundedInsertRun_length_le
#check @Resources.FixedRank.prefixLoopRun
#check @Resources.FixedRank.prefixLoopRun_value
#check @Resources.FixedRank.prefixLoopRun_cost_le
#check @Resources.FixedRank.takeSortRun
#check @Resources.FixedRank.takeSortRun_value
#check @Resources.FixedRank.takeSortRun_cost_le
#check @Resources.FixedRank.selectFixedRun
#check @Resources.FixedRank.selectFixedRun_value
#check @Resources.FixedRank.selectFixedRun_cost
#check @Resources.FixedRank.selectFixedRun_cost_le
#check @Resources.FixedRank.selectFixedRun_uniform_bound
#check @Examples.FixedRankSelection.minimum_example
#check @Examples.FixedRankSelection.minimum_duplicate
#check @Examples.FixedRankSelection.minimum_empty
#check @Examples.FixedRankSelection.minimum_execution
#check @Examples.FixedRankSelection.minimum_empty_execution
#check @Examples.FixedRankSelection.duplicate_prefix
#check @Examples.FixedRankSelection.zero_width_prefix
#check @Examples.FixedRankSelection.prefix_with_history
#check @Examples.FixedRankSelection.two_loop_correspondence
#check @Examples.FixedRankSelection.second_duplicate
#check @Examples.FixedRankSelection.second_distinct
#check @Examples.FixedRankSelection.second_singleton
#check @Examples.FixedRankSelection.second_exists
#check @Examples.FixedRankSelection.fixed_zero_is_minimum
#check @Examples.FixedRankSelection.fixed_last_occurrence
#check @Examples.FixedRankSelection.fixed_invalid_rank
#check @Examples.FixedRankSelection.book_index_two_is_public_rank_three
#check @Examples.FixedRankSelection.bounded_insert_at_head
#check @Examples.FixedRankSelection.bounded_insert_after_accumulator
#check @Examples.FixedRankSelection.bounded_step_for_rank
#check @Examples.FixedRankSelection.measured_rank_and_bound
#check @Examples.FixedRankSelection.fixed_zero_execution
#check @Examples.FixedRankSelection.fixed_zero_bound
#check @Examples.FixedRankSelection.minimum_and_fixed_costs_differ
#check @Examples.FixedRankSelection.fixed_second_execution
#check @Examples.FixedRankSelection.duplicate_second_with_bound
#check @Examples.FixedRankSelection.uniform_constants_include_minimum
