/- Prepared complete statement input for auxiliary candidate 8fef3ea5964f058f1c0036f53414d5d06fa56e59.
   This file has not been executed; actual type evidence is root-owned. -/
import Applications.Resources.SelectionAuxiliary
import Examples.SelectionAuxiliary

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Resources.SelectionAuxiliary.slowSelectRun
#check @Resources.SelectionAuxiliary.slowSelectRun_value
#check @Resources.SelectionAuxiliary.slowSelectRun_cost
#check @Resources.SelectionAuxiliary.slowSelectRun_cost_of_lt
#check @Resources.SelectionAuxiliary.slowSelectRun_some_iff
#check @Resources.SelectionAuxiliary.slowSelectRun_none
#check @Resources.SelectionAuxiliary.slowSelectRun_public
#check @Resources.SelectionAuxiliary.slowSelectRun_cost_bound
#check @Resources.SelectionAuxiliary.slowSelectRun_cost_of_pairwise
#check @Resources.SelectionAuxiliary.slowSelectRun_cost_reverse_range
#check @Resources.SelectionAuxiliary.slowSelectRun_entry_bound
#check @Resources.SelectionAuxiliary.slowSelectRun_cutoff_bound
#check @Resources.SelectionAuxiliary.slowMedianRun
#check @Resources.SelectionAuxiliary.slowMedianRun_value
#check @Resources.SelectionAuxiliary.slowMedianRun_cost
#check @Resources.SelectionAuxiliary.slowMedianRun_some_iff
#check @Resources.SelectionAuxiliary.slowMedianRun_none
#check @Resources.SelectionAuxiliary.slowMedianRun_mem
#check @Resources.SelectionAuxiliary.slowMedianRun_cost_bound
#check @Resources.SelectionAuxiliary.slowMedianRun_small_bound
#check @Examples.SelectionAuxiliary.empty_payload_selection
#check @Examples.SelectionAuxiliary.singleton_selection
#check @Examples.SelectionAuxiliary.singleton_invalid
#check @Examples.SelectionAuxiliary.public_rank_bridge
#check @Examples.SelectionAuxiliary.duplicate_occurrence_rank
#check @Examples.SelectionAuxiliary.collapsed_occurrence_rank
#check @Examples.SelectionAuxiliary.valid_selection_budget
#check @Examples.SelectionAuxiliary.empty_payload_median
#check @Examples.SelectionAuxiliary.singleton_median
#check @Examples.SelectionAuxiliary.lower_even_median
#check @Examples.SelectionAuxiliary.repeated_central_values
#check @Examples.SelectionAuxiliary.ascending_five_median
#check @Examples.SelectionAuxiliary.descending_five_median
#check @Examples.SelectionAuxiliary.same_median_different_work
#check @Examples.SelectionAuxiliary.arbitrary_short_chunk
#check @Examples.SelectionAuxiliary.singleton_short_chunk
#check @Examples.SelectionAuxiliary.median_value_and_budget
#check @Examples.SelectionAuxiliary.cutoff_sorted_last
#check @Examples.SelectionAuxiliary.cutoff_descending_last
#check @Examples.SelectionAuxiliary.cutoff_uniform_budget
