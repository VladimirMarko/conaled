import Applications.Probability.PermutationPlacement
import Examples.PermutationExpectation
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic

/-!
# Actual placement, internal-order weights and both conditioning directions

The existing Fin3 subset `{0,1}` supplies its actual preceding count and
finite-image first position. The order observation below uses that same sampled
permutation. Its four joint cells come from the invariant-event fiber law;
the new generic independence theorem is specialized with `HasLaw.id`.

The order-dependent weights 2 and 5 have mean `7/2`, count-weight mean `7/6`,
and actual ordinal-weight mean `14/3`. Signed real and positive ENNReal uses
exercise the two weighted interfaces with genuine real integrability.

Conditioning on a supported internal order preserves the count law. Conditioning
on count 1 preserves the uniform internal order and changes the count mean to 1.
Both measures still describe the original sample. Null events yield the zero
conditional measure. The last example shows why an arbitrary placement-dependent
weight cannot replace a function of the internal order.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PermutationPlacement

open MeasureTheory ProbabilityTheory
open Applications.Probability.PermutationExpectation
open Applications.Probability.PermutationOrder
open Applications.Probability.PermutationPlacement
open Examples.PermutationExpectation
  (selected rank3 law3 count_le_one count_mean_real count_mean_ennreal
    firstPosition3 first_position_bridge)
open scoped ENNReal ProbabilityTheory

local instance : MeasurableSpace (Equiv.Perm (Fin 3)) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin 3)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List (Fin 3)) := ⊤
local instance : MeasurableSingletonClass (List (Fin 3)) := ⟨fun _ => trivial⟩

local instance law3_isProbabilityMeasure : IsProbabilityMeasure law3 := by
  dsimp [law3]
  infer_instance

def positions : List (Fin 3) := [0, 1, 2]

private theorem positions_nodup : positions.Nodup := by decide

private theorem positions_complete (a : Fin 3) : a ∈ positions := by
  fin_cases a <;> decide

/-- Inverse-label order of the same selected keys whose placement is counted. -/
def order (π : Equiv.Perm (Fin 3)) : List (Fin 3) :=
  restrictedOrder positions selected π

def countEvent (n : ℕ) : Set (Equiv.Perm (Fin 3)) :=
  {π | beforeCount rank3 selected π = n}

def orderEvent (xs : List (Fin 3)) : Set (Equiv.Perm (Fin 3)) :=
  {π | order π = xs}

private theorem order01_supported :
    ([0, 1] : List (Fin 3)) ∈ orders positions selected := by decide

private theorem order10_supported :
    ([1, 0] : List (Fin 3)) ∈ orders positions selected := by decide

private theorem count_cases (π : Equiv.Perm (Fin 3)) :
    beforeCount rank3 selected π = 0 ∨ beforeCount rank3 selected π = 1 := by
  have h := count_le_one π
  omega

private theorem count_eq_indicator (π : Equiv.Perm (Fin 3)) :
    (beforeCount rank3 selected π : ℝ≥0∞) = (countEvent 1).indicator 1 π := by
  rcases count_cases π with h | h <;> simp [countEvent, h]

/-- The actual count is a 0/1 indicator, so its old mean identifies this mass. -/
theorem count_one_mass : law3 (countEvent 1) = 1 / 3 := by
  calc
    _ = ∫⁻ π, (countEvent 1).indicator 1 π ∂law3 :=
      (lintegral_indicator_one (by trivial)).symm
    _ = ∫⁻ π, (beforeCount rank3 selected π : ℝ≥0∞) ∂law3 := by
      apply lintegral_congr
      intro π
      exact (count_eq_indicator π).symm
    _ = 1 / 3 := count_mean_ennreal

private theorem count_zero_eq_compl : countEvent 0 = (countEvent 1)ᶜ := by
  ext π
  change beforeCount rank3 selected π = 0 ↔ ¬ beforeCount rank3 selected π = 1
  have h := count_le_one π
  omega

theorem count_zero_mass : law3 (countEvent 0) = 2 / 3 := by
  rw [count_zero_eq_compl, prob_compl_eq_one_sub (by trivial), count_one_mass]
  norm_num [← ENNReal.coe_div, ← ENNReal.coe_sub]

theorem order01_mass : law3 (orderEvent [0, 1]) = 1 / 2 := by
  calc
    _ = if ([0, 1] : List (Fin 3)) ∈ orders positions selected
        then (Nat.factorial selected.card : ℝ≥0∞)⁻¹ else 0 :=
      uniformOn_restrictedOrder_eq positions positions_nodup positions_complete
        selected [0, 1]
    _ = 1 / 2 := by
      rw [if_pos order01_supported]
      norm_num [selected, one_div]

theorem order10_mass : law3 (orderEvent [1, 0]) = 1 / 2 := by
  calc
    _ = if ([1, 0] : List (Fin 3)) ∈ orders positions selected
        then (Nat.factorial selected.card : ℝ≥0∞)⁻¹ else 0 :=
      uniformOn_restrictedOrder_eq positions positions_nodup positions_complete
        selected [1, 0]
    _ = 1 / 2 := by
      rw [if_pos order10_supported]
      norm_num [selected, one_div]

private theorem count_event_invariant (n : ℕ) :
    ∀ (σ : Equiv.Perm (Fin 3)), (∀ a, σ a ∈ selected ↔ a ∈ selected) →
      ∀ π, (π * σ.symm ∈ countEvent n ↔ π ∈ countEvent n) := by
  intro σ hA π
  change beforeCount rank3 selected (π * σ.symm) = n ↔
    beforeCount rank3 selected π = n
  rw [beforeCount_relabel rank3 selected π σ hA]

private theorem count_order_slice (n : ℕ) (xs : List (Fin 3)) :
    law3 (countEvent n ∩ orderEvent xs) =
      if xs ∈ orders positions selected then law3 (countEvent n) / 2 else 0 := by
  have h := uniformOn_inter_restrictedOrder_eq positions positions_nodup positions_complete
    selected (countEvent n) (count_event_invariant n) xs
  simpa [law3, orderEvent, order, selected] using h

/-- All four cells use the new event law and the retained actual count masses. -/
theorem count_zero_order01_mass :
    law3 (countEvent 0 ∩ orderEvent [0, 1]) = 1 / 3 := by
  rw [count_order_slice, if_pos order01_supported, count_zero_mass]
  norm_num [← ENNReal.coe_div]

theorem count_zero_order10_mass :
    law3 (countEvent 0 ∩ orderEvent [1, 0]) = 1 / 3 := by
  rw [count_order_slice, if_pos order10_supported, count_zero_mass]
  norm_num [← ENNReal.coe_div]

theorem count_one_order01_mass :
    law3 (countEvent 1 ∩ orderEvent [0, 1]) = 1 / 6 := by
  rw [count_order_slice, if_pos order01_supported, count_one_mass]
  norm_num [← ENNReal.coe_div]

theorem count_one_order10_mass :
    law3 (countEvent 1 ∩ orderEvent [1, 0]) = 1 / 6 := by
  rw [count_order_slice, if_pos order10_supported, count_one_mass]
  norm_num [← ENNReal.coe_div]

/-- The generic current-law theorem specializes to these actual observations. -/
theorem count_order_independent :
    IndepFun (fun π => beforeCount rank3 selected π) order law3 := by
  exact indepFun_beforeCount_restrictedOrder positions positions_nodup positions_complete
    rank3 selected (HasLaw.id (μ := law3))

private theorem independent_cell (n : ℕ) (xs : List (Fin 3)) :
    law3 (countEvent n ∩ orderEvent xs) =
      law3 (countEvent n) * law3 (orderEvent xs) := by
  have h := count_order_independent.measure_inter_preimage_eq_mul
    ({n} : Set ℕ) ({xs} : Set (List (Fin 3)))
    (measurableSet_singleton n) (measurableSet_singleton xs)
  simpa [countEvent, orderEvent] using h

/-! ## Actual order weights and the finite-image ordinal -/

noncomputable def weight (xs : List (Fin 3)) : ℝ :=
  if xs = [0, 1] then 2 else 5

theorem weight_nonneg (xs : List (Fin 3)) : 0 ≤ weight xs := by
  unfold weight
  split_ifs <;> norm_num

theorem weight_integrable : Integrable (fun π => weight (order π)) law3 :=
  Integrable.of_finite

theorem weighted_count_integrable :
    Integrable (fun π => (beforeCount rank3 selected π : ℝ) * weight (order π)) law3 :=
  Integrable.of_finite

private theorem weight_eq_indicator (π : Equiv.Perm (Fin 3)) :
    weight (order π) = 5 - 3 * (orderEvent [0, 1]).indicator 1 π := by
  by_cases h : order π = [0, 1] <;> norm_num [weight, orderEvent, h]

theorem weight_mean : (∫ π, weight (order π) ∂law3) = 7 / 2 := by
  have hconstant : Integrable (fun _π : Equiv.Perm (Fin 3) => (5 : ℝ)) law3 :=
    Integrable.of_finite
  have hindicator :
      Integrable ((orderEvent [0, 1]).indicator (1 : Equiv.Perm (Fin 3) → ℝ)) law3 :=
    Integrable.of_finite
  calc
    _ = ∫ π, 5 - 3 * (orderEvent [0, 1]).indicator 1 π ∂law3 :=
      integral_congr_ae (Filter.Eventually.of_forall weight_eq_indicator)
    _ = (∫ _π : Equiv.Perm (Fin 3), (5 : ℝ) ∂law3) -
        3 * ∫ π, (orderEvent [0, 1]).indicator 1 π ∂law3 := by
      rw [integral_sub hconstant (hindicator.const_mul 3), integral_const_mul]
    _ = 5 - 3 * (law3 (orderEvent [0, 1])).toReal := by
      rw [integral_const, integral_indicator_one (by trivial)]
      simp [measureReal_def]
    _ = 7 / 2 := by
      rw [order01_mass]
      norm_num [ENNReal.toReal_div]

theorem weighted_count_factor :
    (∫ π, (beforeCount rank3 selected π : ℝ) * weight (order π) ∂law3) =
      (1 / 3 : ℝ) * ∫ π, weight (order π) ∂law3 := by
  have h := integral_beforeCount_mul_order positions positions_nodup positions_complete
    rank3 rank3.injective selected weight (HasLaw.id (μ := law3))
  simpa [order, selected, Nat.card_eq_fintype_card] using h

theorem weighted_count_mean :
    (∫ π, (beforeCount rank3 selected π : ℝ) * weight (order π) ∂law3) = 7 / 6 := by
  rw [weighted_count_factor, weight_mean]
  norm_num

/-- Increasing the coefficient from 1/3 to 1/2 uses a nonnegative actual weight. -/
theorem weighted_count_bound :
    (∫ π, (beforeCount rank3 selected π : ℝ) * weight (order π) ∂law3) ≤ 7 / 4 := by
  have hweight : 0 ≤ ∫ π, weight (order π) ∂law3 :=
    integral_nonneg (fun π => weight_nonneg (order π))
  calc
    _ = (1 / 3 : ℝ) * ∫ π, weight (order π) ∂law3 := weighted_count_factor
    _ ≤ (1 / 2 : ℝ) * ∫ π, weight (order π) ∂law3 :=
      mul_le_mul_of_nonneg_right (by norm_num) hweight
    _ = 7 / 4 := by rw [weight_mean] <;> norm_num

theorem weighted_ordinal_integrable :
    Integrable (fun π => (firstPosition3 π : ℝ) * weight (order π)) law3 :=
  Integrable.of_finite

/-- The original finite-image minimum is connected before integrating its product. -/
theorem weighted_ordinal_mean :
    (∫ π, (firstPosition3 π : ℝ) * weight (order π) ∂law3) = 14 / 3 := by
  calc
    _ = ∫ π, (beforeCount rank3 selected π : ℝ) * weight (order π) +
        weight (order π) ∂law3 := by
      apply integral_congr_ae
      filter_upwards [] with π
      rw [first_position_bridge]
      push_cast
      ring
    _ = (∫ π, (beforeCount rank3 selected π : ℝ) * weight (order π) ∂law3) +
        ∫ π, weight (order π) ∂law3 :=
      integral_add weighted_count_integrable weight_integrable
    _ = 14 / 3 := by rw [weighted_count_mean, weight_mean] <;> norm_num

noncomputable def signedWeight (xs : List (Fin 3)) : ℝ := -weight xs

theorem signed_weight_integrable : Integrable (fun π => signedWeight (order π)) law3 :=
  Integrable.of_finite

theorem signed_product_integrable :
    Integrable (fun π => (beforeCount rank3 selected π : ℝ) * signedWeight (order π))
      law3 := Integrable.of_finite

theorem signed_weight_mean : (∫ π, signedWeight (order π) ∂law3) = -(7 / 2 : ℝ) := by
  change (∫ π, -weight (order π) ∂law3) = -(7 / 2 : ℝ)
  rw [integral_neg, weight_mean]

/-- The new real equality is used directly with negative order-dependent weights. -/
theorem signed_product_mean :
    (∫ π, (beforeCount rank3 selected π : ℝ) * signedWeight (order π) ∂law3) =
      -(7 / 6 : ℝ) := by
  have h := integral_beforeCount_mul_order positions positions_nodup positions_complete
    rank3 rank3.injective selected signedWeight (HasLaw.id (μ := law3))
  have hfactor :
      (∫ π, (beforeCount rank3 selected π : ℝ) * signedWeight (order π) ∂law3) =
        (1 / 3 : ℝ) * ∫ π, signedWeight (order π) ∂law3 := by
    simpa [order, selected, Nat.card_eq_fintype_card] using h
  rw [hfactor, signed_weight_mean]
  norm_num

/-- The same positive values, viewed in ENNReal after proving real nonnegativity. -/
noncomputable def weightENN (xs : List (Fin 3)) : ℝ≥0∞ := ENNReal.ofReal (weight xs)

theorem weight_ennreal_mean : (∫⁻ π, weightENN (order π) ∂law3) = 7 / 2 := by
  have hnonneg : 0 ≤ᵐ[law3] (fun π => weight (order π)) :=
    Filter.Eventually.of_forall fun π => weight_nonneg (order π)
  calc
    _ = ENNReal.ofReal (∫ π, weight (order π) ∂law3) :=
      (ofReal_integral_eq_lintegral_ofReal weight_integrable hnonneg).symm
    _ = 7 / 2 := by rw [weight_mean] <;> norm_num

/-- This product is evaluated through the new lower-integral theorem. -/
theorem weighted_count_ennreal_mean :
    (∫⁻ π, (beforeCount rank3 selected π : ℝ≥0∞) * weightENN (order π) ∂law3) =
      7 / 6 := by
  have h := lintegral_beforeCount_mul_order positions positions_nodup positions_complete
    rank3 rank3.injective selected weightENN (HasLaw.id (μ := law3))
  have hfactor :
      (∫⁻ π, (beforeCount rank3 selected π : ℝ≥0∞) * weightENN (order π) ∂law3) =
        (1 / 3 : ℝ≥0∞) * ∫⁻ π, weightENN (order π) ∂law3 := by
    simpa [order, selected, Nat.card_eq_fintype_card] using h
  rw [hfactor, weight_ennreal_mean]
  norm_num [← ENNReal.coe_div, ← ENNReal.coe_mul]

/-! ## Conditioning on internal order preserves the count law -/

noncomputable def afterOrder01 : Measure (Equiv.Perm (Fin 3)) :=
  law3[|orderEvent [0, 1]]

local instance afterOrder01_isProbabilityMeasure : IsProbabilityMeasure afterOrder01 := by
  apply cond_isProbabilityMeasure (μ := law3) (s := orderEvent [0, 1])
  rw [order01_mass]
  norm_num

private theorem after_order_count_mass (n : ℕ) :
    afterOrder01 (countEvent n) = law3 (countEvent n) := by
  have hpos : law3 (orderEvent [0, 1]) ≠ 0 := by rw [order01_mass] <;> norm_num
  calc
    _ = (law3 (orderEvent [0, 1]))⁻¹ *
        law3 (orderEvent [0, 1] ∩ countEvent n) :=
      cond_apply (by trivial) law3 (countEvent n)
    _ = (law3 (orderEvent [0, 1]))⁻¹ *
        (law3 (countEvent n) * law3 (orderEvent [0, 1])) := by
      rw [Set.inter_comm, independent_cell]
    _ = law3 (countEvent n) := by
      rw [mul_left_comm, ENNReal.inv_mul_cancel hpos (measure_ne_top _ _), mul_one]

theorem after_order_count_zero_mass : afterOrder01 (countEvent 0) = 2 / 3 := by
  rw [after_order_count_mass, count_zero_mass]

theorem after_order_count_one_mass : afterOrder01 (countEvent 1) = 1 / 3 := by
  rw [after_order_count_mass, count_one_mass]

theorem after_order_environment_changed : afterOrder01 ≠ law3 := by
  have h : afterOrder01 (orderEvent [0, 1]) = 1 := by
    exact cond_apply_self (by rw [order01_mass] <;> norm_num) (measure_ne_top _ _)
  intro heq
  rw [heq, order01_mass] at h
  norm_num [← ENNReal.coe_div] at h

/-! ## Conditioning on placement preserves the internal order -/

noncomputable def afterOne : Measure (Equiv.Perm (Fin 3)) := law3[|countEvent 1]

local instance afterOne_isProbabilityMeasure : IsProbabilityMeasure afterOne := by
  apply cond_isProbabilityMeasure (μ := law3) (s := countEvent 1)
  rw [count_one_mass]
  norm_num

theorem after_one_order01_mass : afterOne (orderEvent [0, 1]) = 1 / 2 := by
  change law3[orderEvent [0, 1] | countEvent 1] = 1 / 2
  rw [cond_apply (by trivial), count_one_mass, count_one_order01_mass]
  norm_num [← ENNReal.coe_div, ← ENNReal.coe_mul]

theorem after_one_order10_mass : afterOne (orderEvent [1, 0]) = 1 / 2 := by
  change law3[orderEvent [1, 0] | countEvent 1] = 1 / 2
  rw [cond_apply (by trivial), count_one_mass, count_one_order10_mass]
  norm_num [← ENNReal.coe_div, ← ENNReal.coe_mul]

theorem after_one_count_ae :
    ∀ᵐ π ∂afterOne, beforeCount rank3 selected π = 1 :=
  ae_cond_of_forall_mem (μ := law3) (s := countEvent 1) (by trivial) (fun _ h => h)

/-- The changed count mean has genuine finite integrability under its own measure. -/
theorem after_one_count_moment :
    Integrable (fun π => (beforeCount rank3 selected π : ℝ)) afterOne ∧
      (∫ π, (beforeCount rank3 selected π : ℝ) ∂afterOne) = 1 := by
  refine ⟨Integrable.of_finite, ?_⟩
  calc
    _ = ∫ _π : Equiv.Perm (Fin 3), (1 : ℝ) ∂afterOne := by
      apply integral_congr_ae
      filter_upwards [after_one_count_ae] with π hπ
      simp only [hπ, Nat.cast_one]
    _ = 1 := by simp

theorem after_one_environment_changed : afterOne ≠ law3 := by
  have h : afterOne (countEvent 1) = 1 := by
    exact cond_apply_self (by rw [count_one_mass] <;> norm_num) (measure_ne_top _ _)
  intro heq
  rw [heq, count_one_mass] at h
  norm_num [← ENNReal.coe_div] at h

/-! ## Zero events and unsupported orders are retained before normalization -/

theorem empty_event_slice (xs : List (Fin 3)) :
    law3 ((∅ : Set (Equiv.Perm (Fin 3))) ∩ orderEvent xs) = 0 := by
  have hInvariant :
      ∀ (σ : Equiv.Perm (Fin 3)), (∀ a, σ a ∈ selected ↔ a ∈ selected) →
        ∀ π, (π * σ.symm ∈ (∅ : Set (Equiv.Perm (Fin 3))) ↔ π ∈ ∅) := by
    intro _ _ _
    simp
  have h := uniformOn_inter_restrictedOrder_eq positions positions_nodup positions_complete
    selected ∅ hInvariant xs
  simpa [law3, orderEvent, order] using h

theorem count_two_event_empty : countEvent 2 = ∅ := by
  ext π
  change beforeCount rank3 selected π = 2 ↔ False
  have h := count_le_one π
  omega

theorem count_two_mass : law3 (countEvent 2) = 0 := by
  rw [count_two_event_empty, measure_empty]

theorem count_two_slice (xs : List (Fin 3)) : law3 (countEvent 2 ∩ orderEvent xs) = 0 := by
  rw [count_order_slice, count_two_mass]
  split_ifs <;> simp

theorem unsupported_order_slice (n : ℕ) :
    law3 (countEvent n ∩ orderEvent [0, 0]) = 0 := by
  rw [count_order_slice, if_neg (by decide)]

theorem unsupported_order_mass : law3 (orderEvent [0, 0]) = 0 := by
  have hInvariant :
      ∀ (σ : Equiv.Perm (Fin 3)), (∀ a, σ a ∈ selected ↔ a ∈ selected) →
        ∀ π, (π * σ.symm ∈ (Set.univ : Set (Equiv.Perm (Fin 3))) ↔ π ∈ Set.univ) := by
    intro _ _ _
    simp
  have hnot : ([0, 0] : List (Fin 3)) ∉ orders positions selected := by decide
  have h := uniformOn_inter_restrictedOrder_eq positions positions_nodup positions_complete
    selected Set.univ hInvariant [0, 0]
  simpa [law3, orderEvent, order, hnot] using h

theorem cond_empty_eq_zero : law3[|(∅ : Set (Equiv.Perm (Fin 3)))] = 0 := by simp

theorem cond_count_two_eq_zero : law3[|countEvent 2] = 0 :=
  cond_eq_zero_of_meas_eq_zero count_two_mass

theorem cond_unsupported_order_eq_zero : law3[|orderEvent [0, 0]] = 0 :=
  cond_eq_zero_of_meas_eq_zero unsupported_order_mass

/-! ## An actual placement-dependent weight does not factor -/

noncomputable def placementWeight (π : Equiv.Perm (Fin 3)) : ℝ :=
  beforeCount rank3 selected π

theorem placement_weight_mean : (∫ π, placementWeight π ∂law3) = 1 / 3 :=
  count_mean_real

theorem placement_product_integrable :
    Integrable (fun π => (beforeCount rank3 selected π : ℝ) * placementWeight π) law3 :=
  Integrable.of_finite

theorem placement_product_mean :
    (∫ π, (beforeCount rank3 selected π : ℝ) * placementWeight π ∂law3) = 1 / 3 := by
  calc
    _ = ∫ π, (beforeCount rank3 selected π : ℝ) ∂law3 := by
      apply integral_congr_ae
      filter_upwards [] with π
      rcases count_cases π with h | h <;> simp [placementWeight, h]
    _ = 1 / 3 := count_mean_real

theorem placement_marginal_product :
    (∫ π, (beforeCount rank3 selected π : ℝ) ∂law3) *
      (∫ π, placementWeight π ∂law3) = 1 / 9 := by
  rw [count_mean_real, placement_weight_mean]
  norm_num

/-- Knowing only a random weight's own mean does not justify the order-weight rule. -/
theorem placement_factorization_fails :
    (∫ π, (beforeCount rank3 selected π : ℝ) * placementWeight π ∂law3) ≠
      (∫ π, (beforeCount rank3 selected π : ℝ) ∂law3) *
        ∫ π, placementWeight π ∂law3 := by
  rw [placement_product_mean, placement_marginal_product]
  norm_num

end Examples.PermutationPlacement
