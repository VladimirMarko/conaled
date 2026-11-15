import Applications.Trees.Shape
import Applications.Trees.ShapeLog
import Examples.TreeShape

set_option autoImplicit false
set_option warningAsError true
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
set_option pp.coercions true
set_option pp.all true

#check @Trees.minHeight
#check @Trees.minHeight_nil
#check @Trees.minHeight_node
#check @Trees.minHeight_map
#check @Trees.minHeight_le_height
#check @Trees.Complete
#check @Trees.complete_nil
#check @Trees.complete_node
#check @Trees.complete_iff_minHeight_eq_height
#check @Trees.complete_map
#check @Trees.AlmostComplete
#check @Trees.almostComplete_nil
#check @Trees.almostComplete_iff_sub
#check @Trees.complete_almostComplete
#check @Trees.almostComplete_children
#check @Trees.almostComplete_map
#check @Trees.pow_minHeight_le_numLeaves
#check @Trees.numLeaves_le_pow_height
#check @Trees.numLeaves_eq_pow_height
#check @Trees.numLeaves_eq_pow_minHeight
#check @Trees.numLeaves_lt_pow_height
#check @Trees.pow_minHeight_lt_numLeaves
#check @Trees.complete_iff_numLeaves_eq_pow_height
#check @Trees.complete_iff_numLeaves_eq_pow_minHeight
#check @Trees.minHeight_le_log_numLeaves
#check @Trees.clog_numLeaves_le_height
#check @Trees.minHeight_eq_log_numLeaves
#check @Trees.height_eq_clog_numLeaves
#check @Trees.height_optimal
#check @Trees.minHeight_le_logb_numLeaves
#check @Trees.logb_numLeaves_le_height
#check @Trees.minHeight_lt_logb_numLeaves
#check @Trees.logb_numLeaves_lt_height
#check @Trees.height_eq_logb_numLeaves
#check @Trees.minHeight_eq_floor_logb_numLeaves
#check @Trees.height_eq_ceil_logb_numLeaves
#check @TreeShapeExamples.single
#check @TreeShapeExamples.single_complete
#check @TreeShapeExamples.single_minHeight
#check @TreeShapeExamples.single_almostComplete
#check @TreeShapeExamples.empty_shapes
#check @TreeShapeExamples.perfectThree
#check @TreeShapeExamples.perfectThree_complete
#check @TreeShapeExamples.perfectThree_leaves
#check @TreeShapeExamples.perfectThree_minHeight
#check @TreeShapeExamples.rightTwo
#check @TreeShapeExamples.rightTwo_incomplete
#check @TreeShapeExamples.rightTwo_almostComplete
#check @TreeShapeExamples.rightTwo_strict_capacity
#check @TreeShapeExamples.rightTwo_children
#check @TreeShapeExamples.rightTwo_sub
#check @TreeShapeExamples.chainThree_power_not_complete
#check @TreeShapeExamples.rightTwo_rounded_equalities
#check @TreeShapeExamples.rightTwo_rounded_strictness_fails
#check @TreeShapeExamples.empty_logarithms
#check @TreeShapeExamples.sample_almostComplete
#check @TreeShapeExamples.sample_minHeight
#check @TreeShapeExamples.sample_leaves
#check @TreeShapeExamples.sample_logarithms
#check @TreeShapeExamples.sample_height_nodes
#check @TreeShapeExamples.sample_wrong_node_offset
#check @TreeShapeExamples.perfectThree_real_height
#check @TreeShapeExamples.rightTwo_strict_real
#check @TreeShapeExamples.sample_real_rounding
#check @TreeShapeExamples.empty_real_height
#check @TreeShapeExamples.mapped_sample
#check @TreeShapeExamples.relabelled_complete
#check @TreeShapeExamples.minHeight_erase
#check @TreeShapeExamples.almostComplete_erase
#check @TreeShapeExamples.pairSample_shape
#check @TreeShapeExamples.corrupt_shape_without_validity
#check @TreeShapeExamples.minStep
#check @TreeShapeExamples.min_reader
#check @TreeShapeExamples.minSample
#check @TreeShapeExamples.minSample_valid
#check @TreeShapeExamples.minSample_erases
#check @TreeShapeExamples.minSample_reads
#check @TreeShapeExamples.heightOptimalCounter
#check @TreeShapeExamples.heightOptimalCounter_numNodes
#check @TreeShapeExamples.heightOptimalCounter_shape
#check @TreeShapeExamples.optimum_across_labels
#check @TreeShapeExamples.counter_not_almostComplete
#check @TreeShapeExamples.counter_rounded_height
#check @TreeShapeExamples.counter_height_optimal
#check @TreeShapeExamples.almostFour
#check @TreeShapeExamples.localBalanceCounter
#check @TreeShapeExamples.localBalanceCounter_balanced
#check @TreeShapeExamples.localBalanceCounter_shape
#check @TreeShapeExamples.localBalanceCounter_not_almostComplete
#check @TreeShapeExamples.chain_rounded_bounds
