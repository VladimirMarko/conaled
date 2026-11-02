import Applications.Probability.PermutationTail
import Examples.PermutationOrder
import Examples.PermutationJointBoundary
import Mathlib.Probability.HasLaw
import Mathlib.Tactic

/-!
# Joint observations under one permutation and its conditional tail

The two Fin4 restrictions below are read from the same global permutation.
The new joint theorem gives mass `1/4`, while the old marginal theorems give
`1/2` each. Their actual map laws then establish Mathlib's existing IndepFun
predicate. Unsupported outputs in either coordinate retain mass zero.

The Fin5 example conditions the actual full order to start with key `2`.
The old conditional-tail HasLaw is the premise of the new pair-filter law.
The paired tail filters and the original projections coincide on that event,
so both actual observations have the product law under the changed measure.
No independent sample or uniformity of that whole environment is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PermutationJoint

open MeasureTheory ProbabilityTheory
open Applications.Probability.PermutationOrder
open Applications.Probability.PermutationTail
open Examples.PermutationOrder (positions positions_nodup positions_complete law)
open Examples.PermutationJointBoundary
  (positions5 positions5_nodup positions5_complete law5)
open scoped ENNReal ProbabilityTheory

local instance : MeasurableSpace (Equiv.Perm (Fin 4)) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin 4)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List (Fin 4)) := ⊤
local instance : MeasurableSingletonClass (List (Fin 4)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Equiv.Perm (Fin 5)) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin 5)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List (Fin 5)) := ⊤
local instance : MeasurableSingletonClass (List (Fin 5)) := ⟨fun _ => trivial⟩

local instance law_isProbabilityMeasure : IsProbabilityMeasure law := by
  unfold law
  infer_instance

local instance law5_isProbabilityMeasure : IsProbabilityMeasure law5 := by
  unfold law5
  infer_instance

def leftKeys : Finset (Fin 4) := {0, 2}
def rightKeys : Finset (Fin 4) := {1, 3}

theorem subsets_disjoint : Disjoint leftKeys rightKeys := by decide

/-- The actual pair fiber is connected directly to the new universal formula. -/
theorem joint_mass :
    law {π | (restrictedOrder positions leftKeys π,
      restrictedOrder positions rightKeys π) = ([0, 2], [1, 3])} = 1 / 4 := by
  have hsupport : ([0, 2] : List (Fin 4)) ∈ orders positions leftKeys ∧
      ([1, 3] : List (Fin 4)) ∈ orders positions rightKeys := by decide
  unfold law
  rw [uniformOn_restrictedOrder_pair_eq positions positions_nodup positions_complete
    leftKeys rightKeys subsets_disjoint [0, 2] [1, 3], if_pos hsupport]
  norm_num [leftKeys, rightKeys, one_div]

theorem left_mass :
    law {π | restrictedOrder positions leftKeys π = [0, 2]} = 1 / 2 := by
  have hmem : ([0, 2] : List (Fin 4)) ∈ orders positions leftKeys := by decide
  unfold law
  rw [uniformOn_restrictedOrder_eq positions positions_nodup positions_complete
    leftKeys [0, 2], if_pos hmem]
  norm_num [leftKeys, one_div]

theorem right_mass :
    law {π | restrictedOrder positions rightKeys π = [1, 3]} = 1 / 2 := by
  have hmem : ([1, 3] : List (Fin 4)) ∈ orders positions rightKeys := by decide
  unfold law
  rw [uniformOn_restrictedOrder_eq positions positions_nodup positions_complete
    rightKeys [1, 3], if_pos hmem]
  norm_num [rightKeys, one_div]

theorem unsupported_left_mass :
    law {π | (restrictedOrder positions leftKeys π,
      restrictedOrder positions rightKeys π) = ([0, 0], [1, 3])} = 0 := by
  have hbad : ¬ (([0, 0] : List (Fin 4)) ∈ orders positions leftKeys ∧
      ([1, 3] : List (Fin 4)) ∈ orders positions rightKeys) := by decide
  unfold law
  rw [uniformOn_restrictedOrder_pair_eq positions positions_nodup positions_complete
    leftKeys rightKeys subsets_disjoint [0, 0] [1, 3], if_neg hbad]

theorem unsupported_right_mass :
    law {π | (restrictedOrder positions leftKeys π,
      restrictedOrder positions rightKeys π) = ([0, 2], [1, 1])} = 0 := by
  have hbad : ¬ (([0, 2] : List (Fin 4)) ∈ orders positions leftKeys ∧
      ([1, 1] : List (Fin 4)) ∈ orders positions rightKeys) := by decide
  unfold law
  rw [uniformOn_restrictedOrder_pair_eq positions positions_nodup positions_complete
    leftKeys rightKeys subsets_disjoint [0, 2] [1, 1], if_neg hbad]

/-- This map law concerns the actual pair, not merely its two marginals. -/
theorem joint_map :
    law.map (fun π => (restrictedOrder positions leftKeys π,
      restrictedOrder positions rightKeys π)) =
      (uniformOn (orders positions leftKeys : Set (List (Fin 4)))).prod
        (uniformOn (orders positions rightKeys : Set (List (Fin 4)))) :=
  map_restrictedOrder_pair_uniformOn positions positions_nodup positions_complete
    leftKeys rightKeys subsets_disjoint

theorem left_hasLaw :
    HasLaw (restrictedOrder positions leftKeys)
      (uniformOn (orders positions leftKeys : Set (List (Fin 4)))) law where
  aemeasurable := (measurable_of_finite _).aemeasurable
  map_eq := map_restrictedOrder_uniformOn positions positions_nodup positions_complete leftKeys

theorem right_hasLaw :
    HasLaw (restrictedOrder positions rightKeys)
      (uniformOn (orders positions rightKeys : Set (List (Fin 4)))) law where
  aemeasurable := (measurable_of_finite _).aemeasurable
  map_eq := map_restrictedOrder_uniformOn positions positions_nodup positions_complete rightKeys

theorem joint_hasLaw :
    HasLaw (fun π => (restrictedOrder positions leftKeys π,
      restrictedOrder positions rightKeys π))
      ((uniformOn (orders positions leftKeys : Set (List (Fin 4)))).prod
        (uniformOn (orders positions rightKeys : Set (List (Fin 4))))) law where
  aemeasurable := (measurable_of_finite _).aemeasurable
  map_eq := joint_map

/-- The existing independence predicate follows from the new actual joint law. -/
theorem orders_independent :
    IndepFun (restrictedOrder positions leftKeys) (restrictedOrder positions rightKeys) law :=
  (indepFun_iff_hasLaw_prodMk_prod left_hasLaw right_hasLaw).mpr joint_hasLaw

/-! ## Reuse under the actual first-key-2 conditioning on Fin5 -/

def globalOrder5 (π : Equiv.Perm (Fin 5)) : List (Fin 5) :=
  restrictedOrder positions5 Finset.univ π

def firstTwo : Set (Equiv.Perm (Fin 5)) := firstEvent globalOrder5 2

noncomputable def afterTwo : Measure (Equiv.Perm (Fin 5)) := law5[|firstTwo]

def remaining5 : Finset (Fin 5) := Finset.univ.erase 2
def left5 : Finset (Fin 5) := {0, 1}
def right5 : Finset (Fin 5) := {3, 4}

def tail5 (π : Equiv.Perm (Fin 5)) : List (Fin 5) := (globalOrder5 π).tail

def leftTail (π : Equiv.Perm (Fin 5)) : List (Fin 5) :=
  (tail5 π).filter (fun a => decide (a ∈ left5))

def rightTail (π : Equiv.Perm (Fin 5)) : List (Fin 5) :=
  (tail5 π).filter (fun a => decide (a ∈ right5))

def projectionPair5 (π : Equiv.Perm (Fin 5)) : List (Fin 5) × List (Fin 5) :=
  (restrictedOrder positions5 left5 π, restrictedOrder positions5 right5 π)

theorem global_hasLaw :
    HasLaw globalOrder5
      (uniformOn (orders positions5 Finset.univ : Set (List (Fin 5)))) law5 where
  aemeasurable := (measurable_of_finite _).aemeasurable
  map_eq := map_restrictedOrder_uniformOn positions5 positions5_nodup positions5_complete
    Finset.univ

theorem first_two_mass : law5 firstTwo = 1 / 5 := by
  calc
    _ = ((Finset.univ : Finset (Fin 5)).card : ℝ≥0∞)⁻¹ :=
      head_mass_of_hasLaw positions5 positions5_nodup positions5_complete
        Finset.univ 2 (Finset.mem_univ 2) global_hasLaw
    _ = 1 / 5 := by norm_num [one_div]

local instance afterTwo_isProbabilityMeasure : IsProbabilityMeasure afterTwo := by
  apply cond_isProbabilityMeasure (μ := law5) (s := firstTwo)
  rw [first_two_mass]
  norm_num

/-- This is the actual remaining order under the changed source measure. -/
theorem tail_hasLaw :
    HasLaw tail5 (uniformOn (orders positions5 remaining5 : Set (List (Fin 5))))
      afterTwo :=
  hasLaw_tail_cond_first positions5 positions5_nodup positions5_complete
    Finset.univ 2 (Finset.mem_univ 2) global_hasLaw

/-- The new generic law consumes the old conditional-tail law directly. -/
theorem conditional_pair_hasLaw :
    HasLaw (fun π => (leftTail π, rightTail π))
      ((uniformOn (orders positions5 left5 : Set (List (Fin 5)))).prod
        (uniformOn (orders positions5 right5 : Set (List (Fin 5))))) afterTwo :=
  hasLaw_filter_pair positions5 positions5_nodup positions5_complete remaining5
    tail_hasLaw left5 right5 (by decide) (by decide) (by decide)

theorem conditional_left_hasLaw :
    HasLaw leftTail (uniformOn (orders positions5 left5 : Set (List (Fin 5))))
      afterTwo :=
  hasLaw_filter_tail_cond_first positions5 positions5_nodup positions5_complete
    Finset.univ 2 (Finset.mem_univ 2) global_hasLaw left5 (by decide)

theorem conditional_right_hasLaw :
    HasLaw rightTail (uniformOn (orders positions5 right5 : Set (List (Fin 5))))
      afterTwo :=
  hasLaw_filter_tail_cond_first positions5 positions5_nodup positions5_complete
    Finset.univ 2 (Finset.mem_univ 2) global_hasLaw right5 (by decide)

theorem conditional_tail_orders_independent : IndepFun leftTail rightTail afterTwo :=
  (indepFun_iff_hasLaw_prodMk_prod conditional_left_hasLaw conditional_right_hasLaw).mpr
    conditional_pair_hasLaw

/-- Both components retain the original sample, and equality is on the reveal event. -/
theorem tail_pair_eq_projection_on_event (π : Equiv.Perm (Fin 5))
    (hπ : π ∈ firstTwo) : (leftTail π, rightTail π) = projectionPair5 π := by
  apply Prod.ext
  · exact filter_tail_restrictedOrder_eq positions5 positions5_nodup
      Finset.univ 2 π hπ left5 (by decide)
  · exact filter_tail_restrictedOrder_eq positions5 positions5_nodup
      Finset.univ 2 π hπ right5 (by decide)

/-- The same product law also describes the original two projections under ν. -/
theorem conditional_projection_hasLaw :
    HasLaw projectionPair5
      ((uniformOn (orders positions5 left5 : Set (List (Fin 5)))).prod
        (uniformOn (orders positions5 right5 : Set (List (Fin 5))))) afterTwo := by
  apply conditional_pair_hasLaw.congr
  exact ae_cond_of_forall_mem (μ := law5) (s := firstTwo) (by trivial)
    (fun π hπ => (tail_pair_eq_projection_on_event π hπ).symm)

private theorem order_mass5 (S : Finset (Fin 5)) (xs : List (Fin 5))
    (hxs : xs ∈ orders positions5 S) :
    uniformOn (orders positions5 S : Set (List (Fin 5))) {xs} =
      (Nat.factorial S.card : ℝ≥0∞)⁻¹ := by
  calc
    _ = (((orders positions5 S) ∩ {xs}).card : ℝ≥0∞) /
        ((orders positions5 S).card : ℝ≥0∞) := by
      simpa only [Finset.coe_singleton] using
        (uniformOn_apply_finset (s := orders positions5 S) (t := {xs}))
    _ = (Nat.factorial S.card : ℝ≥0∞)⁻¹ := by
      simp [Finset.inter_singleton_of_mem hxs,
        orders_card positions5 positions5_nodup positions5_complete S, one_div]

private theorem product_output_mass :
    ((uniformOn (orders positions5 left5 : Set (List (Fin 5)))).prod
      (uniformOn (orders positions5 right5 : Set (List (Fin 5)))))
        {([0, 1], [3, 4])} = 1 / 4 := by
  letI : IsProbabilityMeasure
      (uniformOn (orders positions5 left5 : Set (List (Fin 5)))) :=
    isProbabilityMeasure_uniformOn (orders positions5 left5).finite_toSet
      (orders_nonempty positions5 left5)
  letI : IsProbabilityMeasure
      (uniformOn (orders positions5 right5 : Set (List (Fin 5)))) :=
    isProbabilityMeasure_uniformOn (orders positions5 right5).finite_toSet
      (orders_nonempty positions5 right5)
  rw [← Set.singleton_prod_singleton, Measure.prod_prod,
    order_mass5 left5 [0, 1] (by decide), order_mass5 right5 [3, 4] (by decide)]
  norm_num [left5, right5, one_div]

/-- A probability derived from the new law of the actual conditioned tail filters. -/
theorem conditional_tail_pair_mass :
    afterTwo {π | (leftTail π, rightTail π) = ([0, 1], [3, 4])} = 1 / 4 := by
  calc
    _ = ((uniformOn (orders positions5 left5 : Set (List (Fin 5)))).prod
          (uniformOn (orders positions5 right5 : Set (List (Fin 5)))))
            {([0, 1], [3, 4])} :=
      conditional_pair_hasLaw.measure_eq (measurableSet_singleton _)
    _ = 1 / 4 := product_output_mass

/-- The on-event value bridge connects that law to the original paired projections. -/
theorem conditional_projection_pair_mass :
    afterTwo {π | projectionPair5 π = ([0, 1], [3, 4])} = 1 / 4 := by
  calc
    _ = ((uniformOn (orders positions5 left5 : Set (List (Fin 5)))).prod
          (uniformOn (orders positions5 right5 : Set (List (Fin 5)))))
            {([0, 1], [3, 4])} :=
      conditional_projection_hasLaw.measure_eq (measurableSet_singleton _)
    _ = 1 / 4 := product_output_mass

theorem afterTwo_first_event_mass : afterTwo firstTwo = 1 := by
  apply cond_apply_self
  · rw [first_two_mass]
    norm_num
  · rw [first_two_mass]
    norm_num

theorem environment_changed : afterTwo ≠ law5 := by
  intro h
  have hmass := congrArg (fun μ : Measure (Equiv.Perm (Fin 5)) => μ firstTwo) h
  rw [afterTwo_first_event_mass, first_two_mass] at hmass
  norm_num at hmass

end Examples.PermutationJoint
