import Examples.MedianOfMedians

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.width 120
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Applications.Selection.lowerMedianValue
#check @Applications.Selection.lowerMedianValue_ranked
#check @Applications.Selection.lowerMedianValue_mem
#check @Applications.Selection.lowerMedianWith_eq_some_value
#check @Applications.Selection.lowerMedianValue_count_bounds
#check @Applications.Selection.chunkMedians
#check @Applications.Selection.length_chunkMedians
#check @Applications.Selection.chunkMedians_eq_nil_iff
#check @Applications.Selection.mem_chunkMedians
#check @Applications.Selection.medianOfMedians
#check @Applications.Selection.medianOfMedians_some_iff_ranked
#check @Applications.Selection.medianOfMedians_none
#check @Applications.Selection.medianOfMedians_mem
#check @Applications.Selection.medianOfMedians_pivot_valid
#check @Applications.Selection.medianOfMedians_median_counts
#check @Applications.Selection.chunkMedianGroups
#check @Applications.Selection.chunkMedianGroups_perm
#check @Applications.Selection.chunkMedianGroups_multiset
#check @Applications.Selection.chunkMedianGroups_lengths
#check @Applications.Selection.chunkMedianGroups_related_length
#check @Applications.Selection.chunk_count_lt_of_median_ge
#check @Applications.Selection.chunk_count_gt_of_median_le
#check @Applications.Selection.medianOfMedians_count_bounds
#check @Applications.Selection.size_five_count_arithmetic
#check @Applications.Selection.medianOfMedians_five_count_bounds
#check @Applications.Selection.ceil_nat_div
#check @Applications.Selection.size_five_ceiling
#check @Applications.Selection.medianOfMedians_five_ceil_bounds
#check @Examples.MedianOfMedians.lower_even_value
#check @Examples.MedianOfMedians.lower_even_adapter
#check @Examples.MedianOfMedians.two_full_chunk_medians
#check @Examples.MedianOfMedians.two_full_chunk_pivot
#check @Examples.MedianOfMedians.two_full_chunk_pivot_mem
#check @Examples.MedianOfMedians.strict_half_is_false
#check @Examples.MedianOfMedians.corrected_non_strict_half
#check @Examples.MedianOfMedians.greater_median_group_is_one
#check @Examples.MedianOfMedians.complementary_group_is_one
#check @Examples.MedianOfMedians.short_final_chunk_medians
#check @Examples.MedianOfMedians.short_final_chunk_pivot
#check @Examples.MedianOfMedians.short_final_chunk_balance
#check @Examples.MedianOfMedians.duplicate_chunk_medians
#check @Examples.MedianOfMedians.duplicate_pivot
#check @Examples.MedianOfMedians.duplicate_strict_sides
#check @Examples.MedianOfMedians.duplicate_groups
#check @Examples.MedianOfMedians.duplicate_groups_multiset
#check @Examples.MedianOfMedians.five_chunk_lower_contribution
#check @Examples.MedianOfMedians.five_chunk_upper_contribution
#check @Examples.MedianOfMedians.five_chunk_total_contribution
#check @Examples.MedianOfMedians.singleton_group_balance
#check @Examples.MedianOfMedians.source_real_ceiling
#check @Examples.MedianOfMedians.source_real_balance
#check @Examples.MedianOfMedians.empty_pivot
#check @Examples.MedianOfMedians.zero_size_pivot
#check @Examples.MedianOfMedians.empty_strict_counts
#check @Examples.MedianOfMedians.mathematical_policy_is_valid
