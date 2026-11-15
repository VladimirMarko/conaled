import Examples.CoordinateSelection

/- Prepared explicit-@ input only; no execution/printed-type credit. -/
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Applications.Selection.CoordinateSelection.observedSelect
#check @Applications.Selection.CoordinateSelection.observedSelect_run
#check @Applications.Selection.CoordinateSelection.observedSelect_total
#check @Applications.Selection.CoordinateSelection.observedSelect_run_iff
#check @Applications.Selection.CoordinateSelection.observedSelect_acquired
#check @Applications.Selection.CoordinateSelection.observedSelect_on_acquired
#check @Applications.Selection.CoordinateSelection.observedSelect_some_iff
#check @Applications.Selection.CoordinateSelection.observedSelect_of_invalid
#check @Applications.Selection.CoordinateSelection.observedSelect_length
#check @Applications.Selection.CoordinateSelection.observedSelect_query_work
#check @Applications.Selection.CoordinateSelection.work
#check @Applications.Selection.CoordinateSelection.work_acquisition
#check @Applications.Selection.CoordinateSelection.work_exact
#check @Applications.Selection.CoordinateSelection.work_covers_queries
#check @Applications.Selection.CoordinateSelection.source_cost_le_F
#check @Applications.Selection.CoordinateSelection.work_le_F
#check @Applications.Selection.CoordinateSelection.work_exists_uniform_affine_bound
#check @Applications.Selection.CoordinateSelection.work_exists_uniform_linear_bound
#check @Applications.Selection.CoordinateSelection.work_lower_acquisition
#check @Applications.Selection.CoordinateSelection.work_lower_input
#check @Applications.Selection.CoordinateSelection.work_family_isBigO
#check @Applications.Selection.CoordinateSelection.observedSelect_valid
#check @Applications.Selection.CoordinateSelection.selectedValue
#check @Applications.Selection.CoordinateSelection.selectedValue_eq_readAll
#check @Applications.Selection.CoordinateSelection.selectedValue_run_iff
#check @Applications.Selection.CoordinateSelection.selectedValue_total
#check @Applications.Selection.CoordinateSelection.selectedValue_correct
#check @Applications.Selection.CoordinateSelection.competitor_query_work_lower_bound
#check @Applications.Selection.CoordinateSelection.exists_uniform_competitor_bound
#check @Applications.Selection.CoordinateSelection.exists_uniform_optimality
#check @Examples.CoordinateSelection.acquired_worker_execution
#check @Examples.CoordinateSelection.empty_run
#check @Examples.CoordinateSelection.empty_every_work
#check @Examples.CoordinateSelection.singleton_run
#check @Examples.CoordinateSelection.singleton_every_work
#check @Examples.CoordinateSelection.concrete_run
#check @Examples.CoordinateSelection.concrete_value_run
#check @Examples.CoordinateSelection.concrete_every_work
#check @Examples.CoordinateSelection.duplicate_run
#check @Examples.CoordinateSelection.duplicate_every_work
#check @Examples.CoordinateSelection.invalid_every_work
#check @Examples.CoordinateSelection.cutoff_twenty_run
#check @Examples.CoordinateSelection.first_recursive_run
#check @Examples.CoordinateSelection.total_correct_value_view
#check @Examples.CoordinateSelection.any_valid_input_contract
#check @Examples.CoordinateSelection.pair_minimum_comparison
