import Examples.RandomSelectionTrace
import Examples.RandomSelection
import Examples.RandomSelectionMean
import Examples.RandomSelectionDrift
import Examples.RandomSelectionTail
import Examples.RandomSelectionEqual
import Examples.RandomSelectionEndpoints

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000





#check @Resources.RandomSelection.prepend_injective
#check @Resources.RandomSelection.map_prepend_apply
#check @Resources.RandomSelection.run_child_atom
#check @Resources.RandomSelection.run_trace_injective
#check @Resources.RandomSelection.traceLaw
#check @Resources.RandomSelection.traceLaw_support
#check @Resources.RandomSelection.traceLaw_atom
#check @Resources.RandomSelection.traceLaw_nil
#check @Resources.RandomSelection.run_singleton_atom
#check @Examples.RandomSelectionTrace.singleton_trace_atom
#check @Examples.RandomSelectionTrace.middle_child_atom
#check @Examples.RandomSelectionTrace.middle_path_atom
#check @Examples.RandomSelectionTrace.middle_path_trace
#check @Examples.RandomSelectionTrace.middle_path_observations
#check @Examples.RandomSelectionTrace.negative_path_atom
#check @Examples.RandomSelectionTrace.negative_path_trace
#check @Examples.RandomSelectionTrace.duplicate_trace_atom
#check @Examples.RandomSelectionTrace.empty_trace_atom
#check @Examples.RandomSelectionTrace.invalid_singleton_trace_atom
#check @Examples.RandomSelectionTrace.different_initial_rank_boundary
#check @Examples.RandomSelectionTrace.unsupported_empty_trace_boundary
#check @Examples.RandomSelectionTrace.arbitrary_supported_trace

#check @Examples.RandomSelectionTrace.middle_path_supported
