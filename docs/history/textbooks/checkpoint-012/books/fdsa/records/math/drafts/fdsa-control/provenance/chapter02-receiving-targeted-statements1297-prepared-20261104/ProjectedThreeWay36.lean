import Applications.Sorting.ThreeWayQuickSort
import Examples.ThreeWayQuickSort
import Applications.Sequences.Partition
import Applications.Resources.Partition
import Examples.ThreeWayPartition
import Applications.Selection.ThreeWay

set_option pp.universes true
set_option pp.explicit true

#check @Applications.Sorting.threeWayQuickSort
#check @Applications.Sorting.threeWayQuickSort_nil
#check @Applications.Sorting.threeWayQuickSort_cons
#check @Applications.Sorting.threeWayQuickSort_singleton
#check @Applications.Sorting.threeWayQuickSort_cons_partition
#check @Applications.Sorting.threeWayQuickSort_perm
#check @Applications.Sorting.threeWayQuickSort_length
#check @Applications.Sorting.mem_threeWayQuickSort
#check @Applications.Sorting.threeWayQuickSort_multiset
#check @Applications.Sorting.threeWayQuickSort_support
#check @Applications.Sorting.threeWayQuickSort_sorted
#check @Applications.Sorting.threeWayQuickSort_correct
#check @Applications.Sorting.threeWayQuickSort_replicate
#check @Examples.ThreeWayQuickSort.empty_input
#check @Examples.ThreeWayQuickSort.singleton_input
#check @Examples.ThreeWayQuickSort.all_equal_buckets
#check @Examples.ThreeWayQuickSort.all_equal_source_equation
#check @Examples.ThreeWayQuickSort.all_equal_input
#check @Examples.ThreeWayQuickSort.all_equal_family
#check @Examples.ThreeWayQuickSort.mixed_buckets
#check @Examples.ThreeWayQuickSort.mixed_source_equation
#check @Examples.ThreeWayQuickSort.mixed_left_child
#check @Examples.ThreeWayQuickSort.mixed_right_child
#check @Examples.ThreeWayQuickSort.mixed_value
#check @Examples.ThreeWayQuickSort.mixed_multiset
#check @Examples.ThreeWayQuickSort.mixed_multiplicities
#check @Examples.ThreeWayQuickSort.mixed_length
#check @Examples.ThreeWayQuickSort.mixed_support_boundary
#check @Examples.ThreeWayQuickSort.absent_pivot_buckets
#check @Examples.ThreeWayQuickSort.absent_pivot_source_equation
#check @Examples.ThreeWayQuickSort.absent_pivot_child_decrease
#check @Examples.ThreeWayQuickSort.absent_pivot_value
#check @Examples.ThreeWayQuickSort.omitted_pivot_boundary
#check @Examples.ThreeWayQuickSort.omitted_equal_block_boundary
#check @Examples.ThreeWayQuickSort.duplicated_pivot_boundary
#check @Examples.ThreeWayQuickSort.misplaced_pivot_boundary
