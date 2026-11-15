import Examples.SelectionCountRank

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.width 120
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Applications.Selection.RankedAt.mem
#check @Applications.Selection.RankedAt.lt_length
#check @Applications.Selection.RankedAt.count_bounds
#check @Applications.Selection.partition_equal_getElem?
#check @Applications.Selection.ordered_getElem?_partition
#check @Applications.Selection.ranked_iff_count_bounds
#check @Applications.Selection.count_bounds_unique
#check @Applications.Selection.filter_le_sublist_filter_lt
#check @Applications.Selection.count_le_add_count_gt
#check @Applications.Selection.ordered_eq_of_pairwise_perm
#check @Applications.Selection.ordered_eq_of_perm
#check @Applications.Selection.ordered_getElem?_perm
#check @Applications.Selection.selectWith_succ_value
#check @Applications.Selection.selectWith_succ_some_iff_count_bounds
#check @Applications.Selection.ordered_getElem?_mem
#check @Applications.Selection.ranked_zero_iff_min
#check @Applications.Selection.ordered_getElem?_zero_iff_min
#check @Applications.Selection.ordered_append
#check @Applications.Selection.ordered_getElem?_append
#check @Applications.Selection.sorted_filter_lt_sublist_take
#check @Applications.Selection.sorted_filter_gt_sublist_drop
#check @Applications.Selection.lowerMedian_value
#check @Applications.Selection.lowerMedian_count_bounds
#check @Applications.Selection.lowerMedian_mem
#check @Examples.SelectionCountRank.duplicate_lower_rank
#check @Examples.SelectionCountRank.duplicate_upper_rank
#check @Examples.SelectionCountRank.duplicate_bounds
#check @Examples.SelectionCountRank.duplicate_public_selection
#check @Examples.SelectionCountRank.weak_upper_count_is_insufficient
#check @Examples.SelectionCountRank.zero_book_rank_is_public_one
#check @Examples.SelectionCountRank.smallest_is_not_largest
#check @Examples.SelectionCountRank.invalid_count_bounds
#check @Examples.SelectionCountRank.outside_pivot_equal_block
#check @Examples.SelectionCountRank.outside_pivot_value
#check @Examples.SelectionCountRank.equal_occurrence_branch
#check @Examples.SelectionCountRank.ordered_blocks
#check @Examples.SelectionCountRank.ordered_blocks_invalid_index
#check @Examples.SelectionCountRank.duplicate_lower_median
#check @Examples.SelectionCountRank.duplicate_median_counts
#check @Examples.SelectionCountRank.monotone_count_transport
