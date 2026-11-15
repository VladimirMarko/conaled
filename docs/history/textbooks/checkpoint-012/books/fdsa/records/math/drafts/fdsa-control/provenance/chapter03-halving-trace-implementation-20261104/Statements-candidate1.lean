-- Prepared only; no actual-type credit from this input.
-- Candidate: 45d120ce0f5bacbaac76cbceeca13ee3ff494dff
import Applications.Resources.HalvingTrace
import Examples.HalvingTrace

set_option autoImplicit false
set_option warningAsError true
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000

#check @Resources.HalvingTrace.Halves
#check @Resources.HalvingTrace.Halves.stop
#check @Resources.HalvingTrace.Halves.step
#check @Resources.HalvingTrace.positive
#check @Resources.HalvingTrace.nonempty
#check @Resources.HalvingTrace.head_eq
#check @Resources.HalvingTrace.length_pos
#check @Resources.HalvingTrace.all_positive
#check @Resources.HalvingTrace.next_halved
#check @Resources.HalvingTrace.step_of_le_half
#check @Resources.HalvingTrace.length_le_sum
#check @Resources.HalvingTrace.member_le_sum
#check @Resources.HalvingTrace.initial_le_sum
#check @Resources.HalvingTrace.sum_le_twice
#check @Resources.HalvingTrace.pow_edges_le
#check @Resources.HalvingTrace.edges_le_log
#check @Resources.HalvingTrace.edges_le_clog
#check @Resources.HalvingTrace.singleton_at_one
#check @Resources.HalvingTrace.zero_impossible
#check @Resources.HalvingTrace.affine_charges_sum_le
#check @Resources.HalvingTrace.tariff_sum_le
#check @Resources.HalvingTrace.sum_le_charges
#check @Resources.HalvingTrace.initial_le_charges
#check @Examples.HalvingTrace.power_two_trace
#check @Examples.HalvingTrace.power_two_values
#check @Examples.HalvingTrace.power_two_bounds
#check @Examples.HalvingTrace.odd_trace
#check @Examples.HalvingTrace.odd_values
#check @Examples.HalvingTrace.odd_bounds
#check @Examples.HalvingTrace.singleton_trace
#check @Examples.HalvingTrace.singleton_values
#check @Examples.HalvingTrace.singleton_forced
#check @Examples.HalvingTrace.early_stop
#check @Examples.HalvingTrace.early_stop_bounds
#check @Examples.HalvingTrace.zero_rejected
#check @Examples.HalvingTrace.insufficient_halving
#check @Examples.HalvingTrace.fixed_tariff_alignment
#check @Examples.HalvingTrace.fixed_tariff_value
#check @Examples.HalvingTrace.fixed_tariff_bounds

-- Generated eliminators, separately counted; full generated audit still required.
#check @Resources.HalvingTrace.Halves.rec
#check @Resources.HalvingTrace.Halves.recOn
#check @Resources.HalvingTrace.Halves.casesOn
