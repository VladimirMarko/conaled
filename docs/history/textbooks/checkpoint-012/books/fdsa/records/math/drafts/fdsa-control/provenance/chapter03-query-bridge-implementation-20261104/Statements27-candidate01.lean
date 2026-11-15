import Examples.CoordinateReadAll

/- Prepared inspection input only. Root must run at the bound candidate. -/
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Applications.Selection.CoordinateQueries.readPlan
#check @Applications.Selection.CoordinateQueries.readPlan_query
#check @Applications.Selection.CoordinateQueries.readPlan_done
#check @Applications.Selection.CoordinateQueries.readPlan_run
#check @Applications.Selection.CoordinateQueries.readPlan_total
#check @Applications.Selection.CoordinateQueries.readPlan_run_iff
#check @Applications.Selection.CoordinateQueries.readPlan_length
#check @Applications.Selection.CoordinateQueries.readPlan_work
#check @Applications.Selection.CoordinateQueries.readAll
#check @Applications.Selection.CoordinateQueries.readAll_run
#check @Applications.Selection.CoordinateQueries.readAll_total
#check @Applications.Selection.CoordinateQueries.readAll_run_iff
#check @Applications.Selection.CoordinateQueries.readAll_coordinates
#check @Applications.Selection.CoordinateQueries.readAll_length
#check @Applications.Selection.CoordinateQueries.readAll_work
#check @Applications.Selection.CoordinateQueries.readAll_correct
#check @Examples.CoordinateReadAll.empty_run
#check @Examples.CoordinateReadAll.empty_every_run
#check @Examples.CoordinateReadAll.full_read_exists
#check @Examples.CoordinateReadAll.full_read_every_run
#check @Examples.CoordinateReadAll.observed_sum
#check @Examples.CoordinateReadAll.concrete_full_read
#check @Examples.CoordinateReadAll.duplicate_full_read
#check @Examples.CoordinateReadAll.duplicate_every_charge
#check @Examples.CoordinateReadAll.repeated_plan_run
#check @Examples.CoordinateReadAll.repeated_plan_every_charge
#check @Examples.CoordinateReadAll.supplied_history_values
