-- Prepared only for the original XT03 source draft; never executed.
-- Any future execution must identify its exact candidate and actual inputs.
import Applications.Resources.TreeFold
import Examples.TreeFold
import Examples.TreeFoldCache
import Examples.TreeFoldObservations

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

-- Applications.Resources.TreeFold
#check @Resources.TreeFold.run
#check @Resources.TreeFold.run_nil
#check @Resources.TreeFold.run_node
#check @Resources.TreeFold.run_node_cost
#check @Resources.TreeFold.run_node_tick
#check @Resources.TreeFold.run_map
#check @Resources.TreeFold.run_value
#check @Resources.TreeFold.run_value_entry
#check @Resources.TreeFold.run_value_of
#check @Resources.TreeFold.reweight_run
#check @Resources.TreeFold.run_cost_entry
#check @Resources.TreeFold.structural_le_cost
#check @Resources.TreeFold.run_cost_const
#check @Resources.TreeFold.run_cost_le

-- Examples.TreeFold
#check @TreeFoldExamples.size_value
#check @TreeFoldExamples.height_value
#check @TreeFoldExamples.size_cost
#check @TreeFoldExamples.height_cost
#check @TreeFoldExamples.empty_run
#check @TreeFoldExamples.empty_primitives
#check @TreeFoldExamples.rightStepRun
#check @TreeFoldExamples.leftStepRun
#check @TreeFoldExamples.single_step_value
#check @TreeFoldExamples.right_step_value
#check @TreeFoldExamples.left_step_value
#check @TreeFoldExamples.single_step_cost
#check @TreeFoldExamples.right_step_cost
#check @TreeFoldExamples.left_step_cost
#check @TreeFoldExamples.single_value
#check @TreeFoldExamples.right_value
#check @TreeFoldExamples.left_value
#check @TreeFoldExamples.single_node_cost
#check @TreeFoldExamples.right_node_cost
#check @TreeFoldExamples.left_node_cost
#check @TreeFoldExamples.nil_work
#check @TreeFoldExamples.singleton_work
#check @TreeFoldExamples.single_sample
#check @TreeFoldExamples.right_sample
#check @TreeFoldExamples.left_sample
#check @TreeFoldExamples.same_inorder_different_work

-- Examples.TreeFoldCache
#check @TreeFoldCacheExamples.annotateRun
#check @TreeFoldCacheExamples.annotate_value
#check @TreeFoldCacheExamples.annotate_valid
#check @TreeFoldCacheExamples.annotate_erases
#check @TreeFoldCacheExamples.annotate_read
#check @TreeFoldCacheExamples.size_cost
#check @TreeFoldCacheExamples.height_cost
#check @TreeFoldCacheExamples.size_cost_one
#check @TreeFoldCacheExamples.height_cost_one
#check @TreeFoldCacheExamples.size_read
#check @TreeFoldCacheExamples.height_read
#check @TreeFoldCacheExamples.size_sample_value
#check @TreeFoldCacheExamples.height_sample_value
#check @TreeFoldCacheExamples.size_sample
#check @TreeFoldCacheExamples.height_sample
#check @TreeFoldCacheExamples.list_value
#check @TreeFoldCacheExamples.list_read
#check @TreeFoldCacheExamples.list_nil_cost
#check @TreeFoldCacheExamples.list_node_cost
#check @TreeFoldCacheExamples.list_sample_work
#check @TreeFoldCacheExamples.list_sample_read
#check @TreeFoldCacheExamples.empty_annotation

-- Examples.TreeFoldObservations
#check @TreeFoldObservationExamples.splitRun
#check @TreeFoldObservationExamples.total
#check @TreeFoldObservationExamples.split_first_run
#check @TreeFoldObservationExamples.split_second_run
#check @TreeFoldObservationExamples.split_total_run
#check @TreeFoldObservationExamples.split_structural
#check @TreeFoldObservationExamples.split_work
#check @TreeFoldObservationExamples.split_total
#check @TreeFoldObservationExamples.append_sample_pair
#check @TreeFoldObservationExamples.cache_sample_pair
#check @TreeFoldObservationExamples.Trace
#check @TreeFoldObservationExamples.traceStep
#check @TreeFoldObservationExamples.words
#check @TreeFoldObservationExamples.trace_value
#check @TreeFoldObservationExamples.trace_node
#check @TreeFoldObservationExamples.trace_sample
#check @TreeFoldObservationExamples.entryToken
#check @TreeFoldObservationExamples.singleton_trace
#check @TreeFoldObservationExamples.collected_trace
#check @TreeFoldObservationExamples.trace_not_collected
#check @TreeFoldObservationExamples.resetStep
#check @TreeFoldObservationExamples.reset_value
#check @TreeFoldObservationExamples.reset_reached_cost
#check @TreeFoldObservationExamples.reset_cost
#check @TreeFoldObservationExamples.reset_unreachable
#check @TreeFoldObservationExamples.reset_not_global

