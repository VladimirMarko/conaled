import Applications.Resources.RandomSelectionWorst
import Examples.RandomSelectionWorst

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

#check @Resources.RandomSelection.EndpointTrace
#check @Resources.RandomSelection.endpointTrace_nil
#check @Resources.RandomSelection.endpointTrace_empty_input
#check @Resources.RandomSelection.endpointTrace_singleton
#check @Resources.RandomSelection.endpointTrace_child
#check @Resources.RandomSelection.endpointTrace_target
#check @Resources.RandomSelection.endpointTrace_valid
#check @Resources.RandomSelection.exists_endpoint_worst
#check @Resources.RandomSelection.range_endpoint_worst
#check @Resources.RandomSelection.unbounded_endpoint_source_family
#check @Examples.RandomSelectionWorst.singleton_endpoint
#check @Examples.RandomSelectionWorst.middle_endpoint_trace
#check @Examples.RandomSelectionWorst.middle_endpoint_probability
#check @Examples.RandomSelectionWorst.signed_endpoint_trace
#check @Examples.RandomSelectionWorst.signed_endpoint_probability
#check @Examples.RandomSelectionWorst.distinct_scan_maximum
#check @Examples.RandomSelectionWorst.unsorted_endpoint_ranks
#check @Examples.RandomSelectionWorst.range_four_exact
#check @Examples.RandomSelectionWorst.range_four_bounds
#check @Examples.RandomSelectionWorst.large_family_every_rank
#check @Examples.RandomSelectionWorst.empty_endpoint_boundary
#check @Examples.RandomSelectionWorst.invalid_endpoint_boundary
#check @Examples.RandomSelectionWorst.invalid_singleton_endpoint_boundary
#check @Examples.RandomSelectionWorst.equal_block_endpoint_boundary
#check @Examples.RandomSelectionWorst.mixed_duplicate_endpoint_boundary
