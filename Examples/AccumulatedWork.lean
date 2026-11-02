import Applications.Probability.AccumulatedWork
import Applications.Resources.Workload
import Examples.AccumulatedWorkBoundary
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic

/-!
# Dependent stages with an actual accumulated observation

One uniformly chosen environment determines all four stage decisions. An
active stage prepends its index to the returned list and charges one unit;
an inactive stage preserves the state and charges zero. The existing measured
executor sequences these operations. Its cost is connected to the ordinary
sum consumed by the shared accumulated-work theorems.

The independently calculated means are `1, 1/2, 1/4, 1/8`, with total `15/8`.
The threshold-three event has mass `1/4`. These stages are dependent: the
intersection of the first two nonconstant events has mass `1/4`, whereas the
product of their marginal masses is `1/8`.

This is an explicit observation model. Condition tests and the selection of
the environment are not charged by this example; no runtime interpretation
or randomized sorting/selection correspondence is inferred from it.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.AccumulatedWork

open MeasureTheory ProbabilityTheory Resources
open scoped ENNReal BigOperators

private theorem uniformFin_integral (n : Nat) (f : Fin n → ℝ≥0∞) :
    (∫⁻ ω, f ω ∂uniformOn (Set.univ : Set (Fin n))) =
      ∑ ω : Fin n, f ω * (1 / n) := by
  rw [lintegral_fintype]
  apply Finset.sum_congr rfl
  intro ω _
  rw [uniformOn_univ]
  simp

private theorem uniformFin_event (n : Nat) (p : Fin n → Prop) [DecidablePred p] :
    uniformOn (Set.univ : Set (Fin n)) {ω | p ω} =
      ((Finset.univ.filter p).card : ℝ≥0∞) / n := by
  have he : {ω : Fin n | p ω} = (↑(Finset.univ.filter p) : Set (Fin n)) := by
    ext ω
    simp
  rw [he]
  simpa using
    (uniformOn_apply_finset (s := Finset.univ) (t := Finset.univ.filter p))

noncomputable def law : Measure (Fin 8) := uniformOn Set.univ

instance : IsProbabilityMeasure law := by
  unfold law
  infer_instance

/-- The work charged by an individual stage under the shared environment. -/
def charge : Nat → Fin 8 → Nat
  | 0, _ => 1
  | 1, ω => if ω.val < 4 then 1 else 0
  | 2, ω => if ω.val < 2 then 1 else 0
  | 3, ω => if ω.val < 1 then 1 else 0
  | _, _ => 0

theorem charge_le_one (t : Nat) (ω : Fin 8) : charge t ω ≤ 1 := by
  rcases t with _ | _ | _ | _ | t <;>
    simp only [charge] <;> split_ifs <;> omega

theorem charge_late (t : Nat) (ω : Fin 8) (ht : 4 ≤ t) : charge t ω = 0 := by
  have he : t = (t - 4) + 4 := by omega
  rw [he]
  rfl

/-- A successful stage records its index; an inactive stage retains the state. -/
def step (ω : Fin 8) (t : Nat) (seen : List Nat) : Measured (List Nat) Nat :=
  if charge t ω = 1 then (t :: seen, 1) else pure seen

theorem step_cost (ω : Fin 8) (t : Nat) (seen : List Nat) :
    (step ω t seen).2 = charge t ω := by
  unfold step
  split_ifs with h
  · exact h.symm
  · have hz : charge t ω = 0 := by have := charge_le_one t ω; omega
    simp [pure, hz]

def program (ω : Fin 8) : Measured (List Nat) Nat :=
  run (step ω) [0, 1, 2, 3] []

/-- Full ordered values are retained, independently of the resource bound. -/
theorem program_value (ω : Fin 8) :
    (program ω).1 =
      if ω.val < 1 then [3, 2, 1, 0]
      else if ω.val < 2 then [2, 1, 0]
      else if ω.val < 4 then [1, 0]
      else [0] := by
  fin_cases ω <;> decide

theorem program_cost (ω : Fin 8) :
    (program ω).2 = 1 + (if ω.val < 4 then 1 else 0) +
      (if ω.val < 2 then 1 else 0) + (if ω.val < 1 then 1 else 0) := by
  fin_cases ω <;> decide

def observation (t : Nat) (ω : Fin 8) : ℝ≥0∞ := charge t ω

theorem observation_measurable (t : Nat) : AEMeasurable (observation t) law :=
  (measurable_of_countable _).aemeasurable

theorem observation_le_one (t : Nat) :
    observation t ≤ᵐ[law] (fun _ => 1) := by
  apply Filter.Eventually.of_forall
  intro ω
  change (charge t ω : ℝ≥0∞) ≤ 1
  exact_mod_cast charge_le_one t ω

/-- The infinite sum is the cost of the finite measured run, padded by zeros. -/
theorem accumulated_eq_cost (ω : Fin 8) :
    (∑' t : Nat, observation t ω) = ((program ω).2 : ℝ≥0∞) := by
  calc
    (∑' t : Nat, observation t ω) = ∑ t ∈ Finset.range 4, observation t ω := by
      apply tsum_eq_sum
      intro t ht
      have hlate : 4 ≤ t := by simpa only [Finset.mem_range, not_lt] using ht
      simp [observation, charge_late t ω hlate]
    _ = ((program ω).2 : ℝ≥0∞) := by
      fin_cases ω <;>
        norm_num [Finset.sum_range_succ, observation, charge, program, run, step, bind, pure]

theorem stage_means (t : Nat) : (∫⁻ ω, observation t ω ∂law) =
    match t with
    | 0 => 1
    | 1 => 1 / 2
    | 2 => 1 / 4
    | 3 => 1 / 8
    | _ => 0 := by
  unfold law
  rw [uniformFin_integral]
  rcases t with _ | _ | _ | _ | t <;>
    norm_num [Fin.sum_univ_succ, observation, charge,
      ← ENNReal.coe_div, ← ENNReal.coe_add, ← ENNReal.coe_mul]

theorem initial_mean : (∫⁻ ω, observation 0 ω ∂law) ≤ 1 := by
  exact (stage_means 0).le

theorem integrated_drift (t : Nat) :
    (∫⁻ ω, observation (t + 1) ω ∂law) ≤
      (1 / 2 : ℝ≥0∞) * (∫⁻ ω, observation t ω ∂law) := by
  simp only [stage_means]
  rcases t with _ | _ | _ | _ | t <;>
    norm_num [← ENNReal.coe_div, ← ENNReal.coe_mul]

/-- Exact arithmetic is calculated from the actual cost of each finite run. -/
theorem expected_cost_exact :
    (∫⁻ ω, ((program ω).2 : ℝ≥0∞) ∂law) = 15 / 8 := by
  unfold law
  rw [uniformFin_integral]
  norm_num [Fin.sum_univ_succ, program_cost,
    ← ENNReal.coe_div, ← ENNReal.coe_add, ← ENNReal.coe_mul]

/-- The same actual cost obtains its upper bound through the general theorem. -/
theorem expected_cost_le :
    (∫⁻ ω, ((program ω).2 : ℝ≥0∞) ∂law) ≤ 2 := by
  have h := Applications.Probability.AccumulatedWork.lintegral_tsum_le law observation
    observation_measurable initial_mean integrated_drift
  simpa [accumulated_eq_cost, one_div, ENNReal.one_sub_inv_two] using h

theorem expected_cost_finite :
    (∫⁻ ω, ((program ω).2 : ℝ≥0∞) ∂law) < ∞ := by
  have h := Applications.Probability.AccumulatedWork.lintegral_tsum_lt_top law observation
    observation_measurable initial_mean integrated_drift
    (by simpa only [one_div] using ENNReal.one_half_lt_one) (by simp)
  simpa only [accumulated_eq_cost] using h

theorem remaining_eq_cost (ω : Fin 8) :
    (∑' j : Nat, observation (1 + j) ω) = (((program ω).2 - 1 : Nat) : ℝ≥0∞) := by
  calc
    (∑' j : Nat, observation (1 + j) ω) =
        ∑ j ∈ Finset.range 3, observation (1 + j) ω := by
      apply tsum_eq_sum
      intro j hj
      have hlate : 4 ≤ 1 + j := by
        simp only [Finset.mem_range] at hj
        omega
      simp [observation, charge_late (1 + j) ω hlate]
    _ = (((program ω).2 - 1 : Nat) : ℝ≥0∞) := by
      fin_cases ω <;> norm_num [Finset.sum_range_succ, observation, charge, program_cost]

theorem expected_remaining_exact :
    (∫⁻ ω, (∑' j : Nat, observation (1 + j) ω) ∂law) = 7 / 8 := by
  simp_rw [remaining_eq_cost]
  unfold law
  rw [uniformFin_integral]
  norm_num [Fin.sum_univ_succ, program_cost,
    ← ENNReal.coe_div, ← ENNReal.coe_add, ← ENNReal.coe_mul]

/-- A positive shift exercises the general remaining-work theorem directly. -/
theorem expected_remaining_le :
    (∫⁻ ω, (∑' j : Nat, observation (1 + j) ω) ∂law) ≤ 1 := by
  have h := Applications.Probability.AccumulatedWork.lintegral_tsum_shift_le law observation
    observation_measurable initial_mean integrated_drift 1
  have hconst : (1 / 2 : ℝ≥0∞) ^ 1 * 1 / (1 - 1 / 2) = 1 := by
    simp only [pow_one, mul_one, one_div, ENNReal.one_sub_inv_two]
    exact ENNReal.div_self (by simp) (by simp)
  rw [hconst] at h
  exact h

theorem tail_event : {ω : Fin 8 | (3 : ℝ≥0∞) ≤ (program ω).2} =
    {ω : Fin 8 | ω.val < 2} := by
  ext ω
  fin_cases ω <;> norm_num [program_cost]

theorem tail_mass : law {ω | (3 : ℝ≥0∞) ≤ (program ω).2} = 1 / 4 := by
  rw [tail_event]
  unfold law
  rw [uniformFin_event]
  have hcard : (Finset.univ.filter (fun ω : Fin 8 => ω.val < 2)).card = 2 := by decide
  rw [hcard]
  norm_num [← ENNReal.coe_div]

/-- The nonempty tail event is bounded through prefix accounting and Markov. -/
theorem tail_le : law {ω | (3 : ℝ≥0∞) ≤ (program ω).2} ≤ 1 / 2 := by
  have h := Applications.Probability.AccumulatedWork.measure_tsum_ge_le_of_stage_le
    law observation observation_measurable initial_mean integrated_drift 1
    (by simpa only [one_div] using ENNReal.one_half_lt_one)
    (by simp) (by simp) observation_le_one
  norm_num [accumulated_eq_cost, one_div, ENNReal.one_sub_inv_two] at h ⊢
  exact h

theorem shared_stage_masses :
    law {ω | ω.val < 4} = 1 / 2 ∧ law {ω | ω.val < 2} = 1 / 4 ∧
    law ({ω | ω.val < 4} ∩ {ω | ω.val < 2}) = 1 / 4 := by
  have hfour : law {ω | ω.val < 4} = 1 / 2 := by
    unfold law
    rw [uniformFin_event]
    have hc : (Finset.univ.filter (fun ω : Fin 8 => ω.val < 4)).card = 4 := by decide
    rw [hc]
    norm_num [← ENNReal.coe_div]
  have htwo : law {ω | ω.val < 2} = 1 / 4 := by simpa only [tail_event] using tail_mass
  refine ⟨hfour, htwo, ?_⟩
  have he : ({ω : Fin 8 | ω.val < 4} ∩ {ω | ω.val < 2}) = {ω | ω.val < 2} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    omega
  rwa [he]

/-- Shared stages have different joint mass from the product of their marginals. -/
theorem shared_stages_not_independent :
    law ({ω | ω.val < 4} ∩ {ω | ω.val < 2}) ≠
      law {ω | ω.val < 4} * law {ω | ω.val < 2} := by
  rw [shared_stage_masses.1, shared_stage_masses.2.1, shared_stage_masses.2.2]
  norm_num [← ENNReal.coe_div, ← ENNReal.coe_mul]

/-- Reweight the completed observation, then sequence an explicit final charge. -/
def affineProgram (ω : Fin 8) : Measured (List Nat) Nat :=
  bind (reweight (fun c : Nat => 2 * c) (program ω)) (fun seen => (seen, 3))

theorem affineProgram_value (ω : Fin 8) : (affineProgram ω).1 = (program ω).1 := rfl

theorem affineProgram_cost (ω : Fin 8) :
    (affineProgram ω).2 = 2 * (program ω).2 + 3 := rfl

theorem affine_expected_exact :
    (∫⁻ ω, ((affineProgram ω).2 : ℝ≥0∞) ∂law) = 27 / 4 := by
  unfold law
  rw [uniformFin_integral]
  norm_num [Fin.sum_univ_succ, affineProgram_cost, program_cost,
    ← ENNReal.coe_div, ← ENNReal.coe_add, ← ENNReal.coe_mul]

/-- The composed cost is still below the generic affine bound. -/
theorem affine_expected_le :
    (∫⁻ ω, ((affineProgram ω).2 : ℝ≥0∞) ∂law) ≤ 7 := by
  have hpoint : (fun ω : Fin 8 => ((affineProgram ω).2 : ℝ≥0∞)) =
      fun ω => 2 * ((program ω).2 : ℝ≥0∞) + 3 := by
    funext ω
    simp [affineProgram_cost]
  rw [hpoint, lintegral_add_right _ measurable_const,
    lintegral_const_mul _ (measurable_of_countable _)]
  simp only [lintegral_const, measure_univ, mul_one]
  calc
    2 * (∫⁻ ω, ((program ω).2 : ℝ≥0∞) ∂law) + 3 ≤ 2 * 2 + 3 :=
      add_le_add_right (mul_le_mul_left' expected_cost_le 2) 3
    _ = 7 := by norm_num

theorem affine_tail_event : {ω : Fin 8 | (9 : ℝ≥0∞) ≤ (affineProgram ω).2} =
    {ω : Fin 8 | (3 : ℝ≥0∞) ≤ (program ω).2} := by
  ext ω
  fin_cases ω <;> norm_num [affineProgram_cost, program_cost]

theorem affine_tail_mass : law {ω | (9 : ℝ≥0∞) ≤ (affineProgram ω).2} = 1 / 4 := by
  rw [affine_tail_event]
  exact tail_mass

theorem affine_tail_le : law {ω | (9 : ℝ≥0∞) ≤ (affineProgram ω).2} ≤ 1 / 2 := by
  rw [affine_tail_event]
  exact tail_le

end Examples.AccumulatedWork
