/- Prepared exhaustive explicit public statements for the four-module chop/map slice.
   UNEXECUTED: root owns all actual compiler and type evidence. -/
import Applications.Resources.Chunks
import Applications.Resources.SelectionMedians
import Examples.ChunkCalls
import Examples.SelectionMedians

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Resources.Chunks.chopRun
#check @Resources.Chunks.chopRun_zero
#check @Resources.Chunks.chopRun_nil
#check @Resources.Chunks.chopRun_eq_cons
#check @Resources.Chunks.chopRun_value
#check @Resources.Chunks.chopRun_cost
#check @Resources.Chunks.chopRun_exact
#check @Resources.Chunks.chopRun_cost_bound
#check @Resources.Chunks.chopRun_one_cost
#check @Resources.Chunks.chopRun_length
#check @Resources.Chunks.chopRun_mem_ne_nil
#check @Resources.Chunks.chopRun_mem_length
#check @Resources.Chunks.chopRun_flatten
#check @Resources.SelectionMedians.slowMedianValueRun
#check @Resources.SelectionMedians.slowMedianValueRun_of_some
#check @Resources.SelectionMedians.slowMedianValueRun_of_run
#check @Resources.SelectionMedians.slowMedianValueRun_some
#check @Resources.SelectionMedians.slowMedianValueRun_cost
#check @Resources.SelectionMedians.slowMedianValueRun_ranked
#check @Resources.SelectionMedians.slowMedianValueRun_mem
#check @Resources.SelectionMedians.slowMedianValueRun_value
#check @Resources.SelectionMedians.slowMedianValueRun_small_bound
#check @Resources.SelectionMedians.mapSlowMedianRun
#check @Resources.SelectionMedians.mapSlowMedianRun_value
#check @Resources.SelectionMedians.mapSlowMedianRun_some_values
#check @Resources.SelectionMedians.mapSlowMedianRun_length
#check @Resources.SelectionMedians.mapSlowMedianRun_cost
#check @Resources.SelectionMedians.mapSlowMedianRun_bound
#check @Resources.SelectionMedians.mapSlowMedianRun_small_bound
#check @Resources.SelectionMedians.mapSlowMedianRun_chop_five_bound
#check @Resources.SelectionMedians.chunkMediansRun
#check @Resources.SelectionMedians.chunkMediansRun_value
#check @Resources.SelectionMedians.chunkMediansRun_some_values
#check @Resources.SelectionMedians.chunkMediansRun_cost_split
#check @Resources.SelectionMedians.chunkMediansRun_cost
#check @Resources.SelectionMedians.chunkMediansRun_cost_positive
#check @Resources.SelectionMedians.chunkMediansRun_length
#check @Resources.SelectionMedians.chunkMediansRun_eq_nil_iff
#check @Resources.SelectionMedians.chunkMediansRun_mem
#check @Resources.SelectionMedians.chunkMediansRun_bound
#check @Resources.SelectionMedians.chunkMediansRun_five_bound
#check @Examples.ChunkCalls.empty_payload
#check @Examples.ChunkCalls.zero_size
#check @Examples.ChunkCalls.singleton_chunks
#check @Examples.ChunkCalls.short_final_chunk
#check @Examples.ChunkCalls.oversized_group
#check @Examples.ChunkCalls.first_recursive_size
#check @Examples.ChunkCalls.both_traversals_are_charged
#check @Examples.ChunkCalls.fused_first_step_is_not_source_count
#check @Examples.ChunkCalls.no_occurrence_is_lost
#check @Examples.ChunkCalls.reached_chunks_are_valid
#check @Examples.ChunkCalls.arbitrary_group_budget
#check @Examples.SelectionMedians.lower_even_payload
#check @Examples.SelectionMedians.duplicate_payload
#check @Examples.SelectionMedians.payload_rank_and_budget
#check @Examples.SelectionMedians.empty_payload_map
#check @Examples.SelectionMedians.two_chunk_map
#check @Examples.SelectionMedians.empty_chunk_preparation
#check @Examples.SelectionMedians.zero_size_preparation
#check @Examples.SelectionMedians.two_full_chunks
#check @Examples.SelectionMedians.short_final_chunk
#check @Examples.SelectionMedians.duplicate_occurrences
#check @Examples.SelectionMedians.first_recursive_size
#check @Examples.SelectionMedians.first_recursive_map_count
#check @Examples.SelectionMedians.prepared_pivot_membership
#check @Examples.SelectionMedians.general_group_preparation
#check @Examples.SelectionMedians.book_map_budget
#check @Examples.SelectionMedians.book_preparation_budget
