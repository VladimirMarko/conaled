-- Prepared for immutable candidate 9cf01df8f01eb73ec5a2020995d90bb6b6eaba84.
-- Public source-header list; no emitted-type execution by the author.
-- One named private helper remains in the source inventory and full audit scope.
import Examples.GeneralMedianBounds

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.width 120
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Examples.GeneralMedianBounds.partition_bounds
#check @Examples.GeneralMedianBounds.nonempty_input_has_bounded_pivot
#check @Examples.GeneralMedianBounds.three_group_bounds
#check @Examples.GeneralMedianBounds.four_group_bounds
#check @Examples.GeneralMedianBounds.six_group_bounds
#check @Examples.GeneralMedianBounds.constant_input_pivot
#check @Examples.GeneralMedianBounds.constant_input_strict_counts
#check @Examples.GeneralMedianBounds.oddInput
#check @Examples.GeneralMedianBounds.odd_chops
#check @Examples.GeneralMedianBounds.odd_chunk_count
#check @Examples.GeneralMedianBounds.odd_medians
#check @Examples.GeneralMedianBounds.odd_pivot
#check @Examples.GeneralMedianBounds.odd_strict_counts
#check @Examples.GeneralMedianBounds.odd_bound_from_general
#check @Examples.GeneralMedianBounds.odd_partition_values
#check @Examples.GeneralMedianBounds.odd_partition_bounds
#check @Examples.GeneralMedianBounds.evenInput
#check @Examples.GeneralMedianBounds.even_chops
#check @Examples.GeneralMedianBounds.even_chunk_count
#check @Examples.GeneralMedianBounds.even_medians
#check @Examples.GeneralMedianBounds.even_pivot
#check @Examples.GeneralMedianBounds.even_strict_counts
#check @Examples.GeneralMedianBounds.even_bound_from_general
#check @Examples.GeneralMedianBounds.even_partition_values
#check @Examples.GeneralMedianBounds.even_partition_bounds
#check @Examples.GeneralMedianBounds.integer_ties_with_short_chunk
#check @Examples.GeneralMedianBounds.integer_tie_bound
