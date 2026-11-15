-- Prepared for immutable candidate cafc71bef2e2779407944cb04089b9b3b14a13dc.
-- Source-header list only; this program has not been executed by the author.
import Applications.Selection.MedianCounterfamily
import Examples.MedianCounterfamily

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.width 120
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Applications.Selection.MedianCounterfamily.lowBlock
#check @Applications.Selection.MedianCounterfamily.highBlock
#check @Applications.Selection.MedianCounterfamily.fullBlocks
#check @Applications.Selection.MedianCounterfamily.family
#check @Applications.Selection.MedianCounterfamily.fullBlocks_length
#check @Applications.Selection.MedianCounterfamily.mem_fullBlocks_length
#check @Applications.Selection.MedianCounterfamily.flatten_fullBlocks_length
#check @Applications.Selection.MedianCounterfamily.family_length
#check @Applications.Selection.MedianCounterfamily.family_positive
#check @Applications.Selection.MedianCounterfamily.family_ne_nil
#check @Applications.Selection.MedianCounterfamily.family_lengths_strictMono
#check @Applications.Selection.MedianCounterfamily.chop_family
#check @Applications.Selection.MedianCounterfamily.lowBlock_median
#check @Applications.Selection.MedianCounterfamily.highBlock_median
#check @Applications.Selection.MedianCounterfamily.singleton_zero_median
#check @Applications.Selection.MedianCounterfamily.chunkMedians_family
#check @Applications.Selection.MedianCounterfamily.chunkMedians_family_length
#check @Applications.Selection.MedianCounterfamily.chunkMedians_family_count_lt
#check @Applications.Selection.MedianCounterfamily.chunkMedians_family_count_gt
#check @Applications.Selection.MedianCounterfamily.family_pivot
#check @Applications.Selection.MedianCounterfamily.family_count_gt
#check @Applications.Selection.MedianCounterfamily.family_excess
#check @Applications.Selection.MedianCounterfamily.family_strict_seventy
#check @Applications.Selection.MedianCounterfamily.family_pivot_strict_seventy
#check @Applications.Selection.MedianCounterfamily.infinite_family
#check @Examples.MedianCounterfamily.first_input
#check @Examples.MedianCounterfamily.first_chops
#check @Examples.MedianCounterfamily.first_medians
#check @Examples.MedianCounterfamily.first_pivot
#check @Examples.MedianCounterfamily.first_counts
#check @Examples.MedianCounterfamily.first_strict_percentage
#check @Examples.MedianCounterfamily.second_chops
#check @Examples.MedianCounterfamily.second_medians
#check @Examples.MedianCounterfamily.second_pivot
#check @Examples.MedianCounterfamily.second_counts
#check @Examples.MedianCounterfamily.second_has_duplicates
#check @Examples.MedianCounterfamily.third_counts
#check @Examples.MedianCounterfamily.growth_at_every_index
#check @Examples.MedianCounterfamily.positive_denominator_at_every_index
#check @Examples.MedianCounterfamily.book_ceiling_still_bounds
#check @Examples.MedianCounterfamily.dropping_allowance_fails
#check @Examples.MedianCounterfamily.actual_pivot_comparison
