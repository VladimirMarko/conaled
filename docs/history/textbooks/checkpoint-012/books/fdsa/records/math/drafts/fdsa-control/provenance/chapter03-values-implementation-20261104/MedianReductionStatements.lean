-- Prepared, unexecuted input for immutable candidate 24b74c65e2b907f1a4cd8b8c72e22bba8f315eea.
-- All 65 new public names; see median-reduction-inventory.json for source identities.
import Applications.Selection.MedianReduction
import Applications.Resources.MedianReduction
import Examples.MedianReduction

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.width 120
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Applications.Selection.MedianReduction.padExtrema
#check @Applications.Selection.MedianReduction.padExtrema_length
#check @Applications.Selection.MedianReduction.padding_length_identity
#check @Applications.Selection.MedianReduction.padding_total_le
#check @Applications.Selection.MedianReduction.extrema
#check @Applications.Selection.MedianReduction.extrema_spec
#check @Applications.Selection.MedianReduction.extrema_eq_of_bounds
#check @Applications.Selection.MedianReduction.ranked_padExtrema
#check @Applications.Selection.MedianReduction.reduceToMedian
#check @Applications.Selection.MedianReduction.reduceToMedian_nil
#check @Applications.Selection.MedianReduction.reduceToMedian_length
#check @Applications.Selection.MedianReduction.reduceToMedian_nonempty
#check @Applications.Selection.MedianReduction.reduceToMedian_length_eq
#check @Applications.Selection.MedianReduction.reduceToMedian_center
#check @Applications.Selection.MedianReduction.reduceToMedian_odd
#check @Applications.Selection.MedianReduction.reduceToMedian_length_le
#check @Applications.Selection.MedianReduction.reduceToMedian_rank_shift
#check @Applications.Selection.MedianReduction.reduceToMedian_ranked
#check @Applications.Selection.MedianReduction.reduceToMedian_value
#check @Applications.Selection.MedianReduction.reduceToMedian_payload_value
#check @Applications.Selection.MedianReduction.reduceToMedian_spec
#check @Resources.MedianReduction.replicateRun
#check @Resources.MedianReduction.replicateRun_exact
#check @Resources.MedianReduction.padExtremaRun
#check @Resources.MedianReduction.padExtremaRun_value
#check @Resources.MedianReduction.padExtremaRun_cost
#check @Resources.MedianReduction.padExtremaRun_exact
#check @Resources.MedianReduction.extremaRun
#check @Resources.MedianReduction.extremaRun_value
#check @Resources.MedianReduction.extremaRun_cost
#check @Resources.MedianReduction.extremaRun_exact
#check @Resources.MedianReduction.reduceToMedianRun
#check @Resources.MedianReduction.reduceToMedianRun_nil
#check @Resources.MedianReduction.reduceToMedianRun_value
#check @Resources.MedianReduction.reduceToMedianRun_cons_cost
#check @Resources.MedianReduction.reduceToMedianRun_cost
#check @Resources.MedianReduction.reduceToMedianRun_cost_le
#check @Resources.MedianReduction.reduceToMedianRun_uniform_bound
#check @Examples.MedianReduction.extrema_mixed
#check @Examples.MedianReduction.extrema_tied
#check @Examples.MedianReduction.extrema_integer
#check @Examples.MedianReduction.extrema_execution
#check @Examples.MedianReduction.replication_execution
#check @Examples.MedianReduction.tied_padding_rank
#check @Examples.MedianReduction.first_padding
#check @Examples.MedianReduction.last_padding
#check @Examples.MedianReduction.lower_middle_padding
#check @Examples.MedianReduction.upper_middle_padding
#check @Examples.MedianReduction.already_central
#check @Examples.MedianReduction.singleton_unchanged
#check @Examples.MedianReduction.empty_median_failure
#check @Examples.MedianReduction.lower_middle_median
#check @Examples.MedianReduction.upper_middle_payload
#check @Examples.MedianReduction.reduction_shape
#check @Examples.MedianReduction.padding_execution
#check @Examples.MedianReduction.first_execution
#check @Examples.MedianReduction.last_execution
#check @Examples.MedianReduction.central_execution
#check @Examples.MedianReduction.singleton_execution
#check @Examples.MedianReduction.empty_execution
#check @Examples.MedianReduction.first_rank_attains_bound
#check @Examples.MedianReduction.measured_reduction_contract
#check @Examples.MedianReduction.invalid_rank_values
#check @Examples.MedianReduction.invalid_rank_cost_exceeds_valid_bound
#check @Examples.MedianReduction.uniform_reduction_constants
