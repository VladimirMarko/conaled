import Applications.Probability.PermutationPlacement
import Examples.PermutationExpectation
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Tactic

/-!
# Boundaries of fixed placement and internal-order independence

The new independence theorem applies to the existing empty, full, singleton,
tied-priority and empty-index observations. Its bare `LT` hypothesis also
permits an always-true relation: the actual full-set count is then two, not
an outside-key count. A lawful full set instead has zero count, including
when its order weight is infinite.

The current-law example keeps an arbitrary environment and transports genuine
product integrability from the finite permutation target. The final two-atom
measure has the same nonconstant uniform order marginal as the original law,
but its actual count and order are dependent. Existing global-head and adaptive
mean counterexamples retain their narrower meanings.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PermutationPlacementBoundary

open MeasureTheory ProbabilityTheory
open Applications.Probability.PermutationExpectation
open Applications.Probability.PermutationOrder
open Applications.Probability.PermutationPlacement
open Examples.PermutationExpectation (selected selected_nonempty rank3 law3)
open scoped ENNReal ProbabilityTheory

universe w

local instance : MeasurableSpace (Equiv.Perm (Fin 2)) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin 2)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Equiv.Perm (Fin 3)) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin 3)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Equiv.Perm Empty) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm Empty) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List (Fin 2)) := ⊤
local instance : MeasurableSingletonClass (List (Fin 2)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List (Fin 3)) := ⊤
local instance : MeasurableSingletonClass (List (Fin 3)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List Empty) := ⊤
local instance : MeasurableSingletonClass (List Empty) := ⟨fun _ => trivial⟩

def positions3 : List (Fin 3) := [0, 1, 2]

theorem positions3_nodup : positions3.Nodup := by decide

theorem positions3_complete (a : Fin 3) : a ∈ positions3 := by
  fin_cases a <;> decide

def positions2 : List (Fin 2) := [0, 1]

theorem positions2_nodup : positions2.Nodup := by decide

theorem positions2_complete (a : Fin 2) : a ∈ positions2 := by
  fin_cases a <;> decide

noncomputable def law2 : Measure (Equiv.Perm (Fin 2)) := uniformOn Set.univ

noncomputable def emptyLaw : Measure (Equiv.Perm Empty) := uniformOn Set.univ

local instance law3_isProbabilityMeasure : IsProbabilityMeasure law3 := by
  dsimp [law3]
  infer_instance

/-- The actual empty observation is included in the new independence law. -/
theorem empty_subset_independent :
    IndepFun (fun π => beforeCount rank3 ∅ π)
      (restrictedOrder positions3 ∅) law3 := by
  exact indepFun_beforeCount_restrictedOrder positions3 positions3_nodup
    positions3_complete rank3 (∅ : Finset (Fin 3))
    (HasLaw.id : HasLaw id law3 law3)

theorem empty_subset_observations (π : Equiv.Perm (Fin 3)) :
    beforeCount rank3 ∅ π = 3 ∧ restrictedOrder positions3 ∅ π = [] := by
  refine ⟨PermutationExpectationBoundary.empty_subset_count π, ?_⟩
  simp [restrictedOrder]

/-- The lawful full subset has the old zero count and a possibly varying order. -/
theorem full_subset_independent :
    IndepFun (fun π => beforeCount rank3 Finset.univ π)
      (restrictedOrder positions3 Finset.univ) law3 := by
  exact indepFun_beforeCount_restrictedOrder positions3 positions3_nodup
    positions3_complete rank3 (Finset.univ : Finset (Fin 3))
    (HasLaw.id : HasLaw id law3 law3)

theorem singleton_independent :
    IndepFun (fun π => beforeCount rank3 PermutationExpectationBoundary.singleton π)
      (restrictedOrder positions3 PermutationExpectationBoundary.singleton) law3 := by
  exact indepFun_beforeCount_restrictedOrder positions3 positions3_nodup
    positions3_complete rank3 PermutationExpectationBoundary.singleton
    (HasLaw.id : HasLaw id law3 law3)

/-- A constant singleton order does not make its assigned rank constant. -/
theorem singleton_observations (π : Equiv.Perm (Fin 3)) :
    beforeCount rank3 PermutationExpectationBoundary.singleton π = (π 1).val ∧
      restrictedOrder positions3 PermutationExpectationBoundary.singleton π = [1] := by
  refine ⟨PermutationExpectationBoundary.singleton_count_eq π, ?_⟩
  simpa [positions3, PermutationExpectationBoundary.singletonOrder,
    PermutationExpectationBoundary.positions] using
    PermutationExpectationBoundary.singleton_order_value π

/-- Tied priorities need no injected-priority premise for independence. -/
theorem tied_priorities_independent :
    IndepFun
      (fun π => beforeCount PermutationExpectationBoundary.tiedPriority
        PermutationExpectationBoundary.tiedSubset π)
      (restrictedOrder positions2 PermutationExpectationBoundary.tiedSubset) law2 := by
  exact indepFun_beforeCount_restrictedOrder positions2 positions2_nodup
    positions2_complete PermutationExpectationBoundary.tiedPriority
    PermutationExpectationBoundary.tiedSubset
    (HasLaw.id : HasLaw id law2 law2)

/-- The old zero count and failed mean substitution coexist with independence. -/
theorem tied_mean_boundary :
    (∀ π : Equiv.Perm (Fin 2),
      beforeCount PermutationExpectationBoundary.tiedPriority
        PermutationExpectationBoundary.tiedSubset π = 0) ∧
    (∫ π, (beforeCount PermutationExpectationBoundary.tiedPriority
      PermutationExpectationBoundary.tiedSubset π : ℝ) ∂law2) ≠
      ((Nat.card (Fin 2) - PermutationExpectationBoundary.tiedSubset.card : ℕ) : ℝ) /
        ((PermutationExpectationBoundary.tiedSubset.card + 1 : ℕ) : ℝ) := by
  exact ⟨PermutationExpectationBoundary.tied_count,
    PermutationExpectationBoundary.tied_mean_ne_formula⟩

theorem empty_indices_independent :
    IndepFun
      (fun π => beforeCount PermutationExpectationBoundary.emptyPriority ∅ π)
      (restrictedOrder ([] : List Empty) ∅) emptyLaw := by
  exact indepFun_beforeCount_restrictedOrder ([] : List Empty) (by simp)
    (fun a => nomatch a) PermutationExpectationBoundary.emptyPriority ∅
    (HasLaw.id : HasLaw id emptyLaw emptyLaw)

/-- The permutation sample is normalized even though there is no index. -/
theorem empty_indices_observations :
    emptyLaw Set.univ = 1 ∧
      ∀ π : Equiv.Perm Empty,
        beforeCount PermutationExpectationBoundary.emptyPriority ∅ π = 0 ∧
          restrictedOrder ([] : List Empty) ∅ π = [] := by
  refine ⟨PermutationExpectationBoundary.empty_indices_normalized, ?_⟩
  intro π
  exact ⟨PermutationExpectationBoundary.empty_indices_count π, rfl⟩

section BareLT

local instance alwaysTrueLT : LT Unit := ⟨fun _ _ => True⟩

def alwaysPriority (_ : Fin 2) : Unit := ()

/-- A bare comparison relation need not exclude the selected keys themselves. -/
theorem always_true_full_count (π : Equiv.Perm (Fin 2)) :
    beforeCount alwaysPriority Finset.univ π = 2 := by
  have hset : {b : Fin 2 | ∀ a ∈ (Finset.univ : Finset (Fin 2)),
      alwaysPriority (π b) < alwaysPriority (π a)} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro _ _ _
    trivial
  rw [beforeCount, hset]
  simp

/-- The new theorem really accepts only LT, including this non-irreflexive relation. -/
theorem always_true_full_independent :
    IndepFun (fun π => beforeCount alwaysPriority Finset.univ π)
      (restrictedOrder positions2 Finset.univ) law2 := by
  exact indepFun_beforeCount_restrictedOrder positions2 positions2_nodup
    positions2_complete alwaysPriority (Finset.univ : Finset (Fin 2))
    (HasLaw.id : HasLaw id law2 law2)

end BareLT

theorem full_infinite_product_value (π : Equiv.Perm (Fin 3)) :
    (beforeCount rank3 Finset.univ π : ℝ≥0∞) * ∞ = 0 := by
  rw [PermutationExpectationBoundary.full_subset_count]
  simp

/-- The new lower-integral law retains the actual zero product with infinite weight. -/
theorem full_infinite_weight_mean :
    (∫⁻ π, (beforeCount rank3 Finset.univ π : ℝ≥0∞) *
      (fun _ : List (Fin 3) => ∞) (restrictedOrder positions3 Finset.univ π)
      ∂law3) = 0 := by
  simpa [Nat.card_eq_fintype_card] using
    (lintegral_beforeCount_mul_order positions3 positions3_nodup positions3_complete
      rank3 rank3.injective (Finset.univ : Finset (Fin 3))
      (fun _ : List (Fin 3) => ∞) (HasLaw.id : HasLaw id law3 law3))

theorem full_weight_itself_infinite :
    (∫⁻ π : Equiv.Perm (Fin 3),
      (fun _ : List (Fin 3) => (∞ : ℝ≥0∞))
        (restrictedOrder positions3 Finset.univ π) ∂law3) = ∞ := by
  simp

/-- The environment is arbitrary. Product integrability comes from the finite
permutation target through its actual HasLaw, not from finiteness of Ω. -/
theorem actual_environment_case {Ω : Type w} [MeasurableSpace Ω]
    {μ : Measure Ω} {Π : Ω → Equiv.Perm (Fin 3)}
    (hΠ : HasLaw Π law3 μ) (g : List (Fin 3) → ℝ) :
    IndepFun (fun ω => beforeCount rank3 selected (Π ω))
      (fun ω => restrictedOrder positions3 selected (Π ω)) μ ∧
    Integrable (fun ω => (beforeCount rank3 selected (Π ω) : ℝ) *
      g (restrictedOrder positions3 selected (Π ω))) μ ∧
    (∫ ω, (beforeCount rank3 selected (Π ω) : ℝ) *
      g (restrictedOrder positions3 selected (Π ω)) ∂μ) =
      (1 / 3 : ℝ) * ∫ ω, g (restrictedOrder positions3 selected (Π ω)) ∂μ := by
  have htarget : Integrable (fun π : Equiv.Perm (Fin 3) =>
      (beforeCount rank3 selected π : ℝ) *
        g (restrictedOrder positions3 selected π)) law3 := Integrable.of_finite
  have hproduct : Integrable (fun ω => (beforeCount rank3 selected (Π ω) : ℝ) *
      g (restrictedOrder positions3 selected (Π ω))) μ := by
    simpa only [Function.comp_def] using hΠ.integrable_comp htarget
  refine ⟨indepFun_beforeCount_restrictedOrder positions3 positions3_nodup
    positions3_complete rank3 selected hΠ, hproduct, ?_⟩
  simpa [selected, Nat.card_eq_fintype_card] using
    (integral_beforeCount_mul_order positions3 positions3_nodup positions3_complete
      rank3 rank3.injective selected g hΠ)

/-! ## A uniform nonconstant order marginal without placement independence -/

def flipped : Equiv.Perm (Fin 3) := Equiv.swap 0 2

def selectedOrder (π : Equiv.Perm (Fin 3)) : List (Fin 3) :=
  restrictedOrder positions3 selected π

noncomputable def twoAtomLaw : Measure (Equiv.Perm (Fin 3)) :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac (Equiv.refl (Fin 3)) +
    (1 / 2 : ℝ≥0∞) • Measure.dirac flipped

theorem identity_observations :
    beforeCount rank3 selected (Equiv.refl (Fin 3)) = 0 ∧
      selectedOrder (Equiv.refl (Fin 3)) = [0, 1] := by
  constructor
  · calc
      _ = ((selected.image (fun a => rank3 ((Equiv.refl (Fin 3)) a))).min'
          (selected_nonempty.image (fun a => rank3 ((Equiv.refl (Fin 3)) a)))).val :=
        beforeCount_rank_eq rank3 selected selected_nonempty (Equiv.refl (Fin 3))
      _ = 0 := by decide
  · decide

theorem flipped_observations :
    beforeCount rank3 selected flipped = 1 ∧ selectedOrder flipped = [1, 0] := by
  constructor
  · calc
      _ = ((selected.image (fun a => rank3 (flipped a))).min'
          (selected_nonempty.image (fun a => rank3 (flipped a)))).val :=
        beforeCount_rank_eq rank3 selected selected_nonempty flipped
      _ = 1 := by decide
  · decide

theorem twoAtomLaw_apply (E : Set (Equiv.Perm (Fin 3))) :
    twoAtomLaw E =
      (1 / 2 : ℝ≥0∞) * E.indicator 1 (Equiv.refl (Fin 3)) +
        (1 / 2 : ℝ≥0∞) * E.indicator 1 flipped := by
  simp [twoAtomLaw, Measure.dirac_apply, smul_eq_mul]

theorem two_atom_normalized : twoAtomLaw Set.univ = 1 := by
  rw [twoAtomLaw_apply]
  norm_num [Set.indicator]

local instance twoAtomLaw_isProbabilityMeasure : IsProbabilityMeasure twoAtomLaw :=
  ⟨two_atom_normalized⟩

private theorem selected_orders :
    orders positions3 selected = {([0, 1] : List (Fin 3)), [1, 0]} := by decide

/-- XU02 supplies the original law of this same actual list observation. -/
theorem selected_order_original_hasLaw :
    HasLaw selectedOrder
      (uniformOn (orders positions3 selected : Set (List (Fin 3)))) law3 where
  aemeasurable := (measurable_of_finite _).aemeasurable
  map_eq := map_restrictedOrder_uniformOn positions3 positions3_nodup
    positions3_complete selected

/-- The two-atom measure has exactly the old uniform whole-order marginal. -/
theorem selected_order_two_atom_hasLaw :
    HasLaw selectedOrder
      (uniformOn (orders positions3 selected : Set (List (Fin 3)))) twoAtomLaw where
  aemeasurable := (measurable_of_finite _).aemeasurable
  map_eq := by
    apply Measure.ext_of_singleton
    intro xs
    rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton xs)]
    change twoAtomLaw {π | selectedOrder π = xs} =
      uniformOn (orders positions3 selected : Set (List (Fin 3))) {xs}
    have htarget : uniformOn (orders positions3 selected : Set (List (Fin 3))) {xs} =
        (((orders positions3 selected) ∩ {xs}).card : ℝ≥0∞) /
          ((orders positions3 selected).card : ℝ≥0∞) := by
      simpa only [Finset.coe_singleton] using
        (uniformOn_apply_finset (s := orders positions3 selected)
          (t := ({xs} : Finset (List (Fin 3)))))
    rw [twoAtomLaw_apply, htarget, selected_orders]
    simp only [Set.indicator, Set.mem_setOf_eq, identity_observations.2,
      flipped_observations.2, Pi.one_apply]
    by_cases h01 : xs = [0, 1]
    · subst xs
      norm_num
    · by_cases h10 : xs = [1, 0]
      · subst xs
        norm_num
      · simp [h01, h10, Ne.symm h01, Ne.symm h10]

theorem two_atom_count_one_mass :
    twoAtomLaw {π | beforeCount rank3 selected π = 1} = 1 / 2 := by
  rw [twoAtomLaw_apply]
  simp [Set.indicator, identity_observations.1, flipped_observations.1]

theorem two_atom_reverse_order_mass :
    twoAtomLaw {π | selectedOrder π = [1, 0]} = 1 / 2 := by
  rw [twoAtomLaw_apply]
  norm_num [Set.indicator, identity_observations.2, flipped_observations.2]

theorem two_atom_joint_mass :
    twoAtomLaw ({π | beforeCount rank3 selected π = 1} ∩
      {π | selectedOrder π = [1, 0]}) = 1 / 2 := by
  rw [twoAtomLaw_apply]
  simp [Set.indicator, identity_observations.1, flipped_observations.1,
    identity_observations.2, flipped_observations.2]

theorem two_atom_marginal_product :
    twoAtomLaw {π | beforeCount rank3 selected π = 1} *
      twoAtomLaw {π | selectedOrder π = [1, 0]} = 1 / 4 := by
  rw [two_atom_count_one_mass, two_atom_reverse_order_mass]
  norm_num

theorem two_atom_joint_ne_product :
    twoAtomLaw ({π | beforeCount rank3 selected π = 1} ∩
      {π | selectedOrder π = [1, 0]}) ≠
      twoAtomLaw {π | beforeCount rank3 selected π = 1} *
        twoAtomLaw {π | selectedOrder π = [1, 0]} := by
  rw [two_atom_joint_mass, two_atom_marginal_product]
  norm_num

/-- A uniform nonconstant order marginal does not imply the new independence. -/
theorem two_atom_not_independent :
    ¬ IndepFun (fun π => beforeCount rank3 selected π) selectedOrder twoAtomLaw := by
  intro h
  have hprod := h.measure_inter_preimage_eq_mul ({1} : Set ℕ)
    {([1, 0] : List (Fin 3))} (measurableSet_singleton 1)
    (measurableSet_singleton ([1, 0] : List (Fin 3)))
  change twoAtomLaw ({π | beforeCount rank3 selected π = 1} ∩
      {π | selectedOrder π = [1, 0]}) =
      twoAtomLaw {π | beforeCount rank3 selected π = 1} *
        twoAtomLaw {π | selectedOrder π = [1, 0]} at hprod
  exact two_atom_joint_ne_product hprod

/-- The actual full-global HasLaw premise cannot be supplied for this measure. -/
theorem two_atom_not_global_uniform :
    ¬ HasLaw (id : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3)) law3 twoAtomLaw := by
  intro hΠ
  exact two_atom_not_independent
    (indepFun_beforeCount_restrictedOrder positions3 positions3_nodup
      positions3_complete rank3 selected hΠ)

/-! ## Existing conditioning/adaptivity limits and the aggregate symmetry -/

/-- The original and conditioned singleton orders have the same law, while
their count means are the existing 1 and 3/2. This is a mean-transfer boundary,
not a failure of independence from a constant singleton observation. -/
theorem retained_global_head_boundary :
    HasLaw PermutationExpectationBoundary.singletonOrder
      (uniformOn (orders PermutationExpectationBoundary.positions
        PermutationExpectationBoundary.singleton : Set (List (Fin 3))))
      PermutationExpectationBoundary.original ∧
    HasLaw PermutationExpectationBoundary.singletonOrder
      (uniformOn (orders PermutationExpectationBoundary.positions
        PermutationExpectationBoundary.singleton : Set (List (Fin 3))))
      PermutationExpectationBoundary.afterZero ∧
    (∫ π, (beforeCount rank3 PermutationExpectationBoundary.singleton π : ℝ)
      ∂PermutationExpectationBoundary.afterZero) ≠
      ∫ π, (beforeCount rank3 PermutationExpectationBoundary.singleton π : ℝ)
        ∂PermutationExpectationBoundary.original := by
  exact ⟨PermutationExpectationBoundary.singleton_order_original_hasLaw,
    PermutationExpectationBoundary.singleton_order_conditional_hasLaw,
    PermutationExpectationBoundary.placement_means_differ⟩

/-- The existing adaptive minimum selects one key but changes the count mean.
Its count is constant zero, so it is not itself an independence counterexample. -/
theorem retained_adaptive_boundary :
    (∀ π : Equiv.Perm (Fin 3),
      beforeCount rank3 (PermutationExpectationBoundary.adaptiveSubset π) π = 0) ∧
    (∫ π, (beforeCount rank3 (PermutationExpectationBoundary.adaptiveSubset π) π : ℝ)
      ∂law3) ≠
      ∫ π, (beforeCount rank3 PermutationExpectationBoundary.singleton π : ℝ)
        ∂law3 := by
  exact ⟨PermutationExpectationBoundary.adaptive_count,
    PermutationExpectationBoundary.adaptive_mean_ne_fixed_singleton⟩

/-- Setwise preservation may permute named outsiders; it is not pointwise fixing. -/
theorem preserving_can_move_outsider :
    (∀ a : Fin 4, Equiv.swap 2 3 a ∈ ({0, 1} : Finset (Fin 4)) ↔
      a ∈ ({0, 1} : Finset (Fin 4))) ∧ Equiv.swap (2 : Fin 4) 3 2 ≠ 2 := by
  decide

theorem outsider_swap_count_preserved (π : Equiv.Perm (Fin 4)) :
    beforeCount (fun a : Fin 4 => a) ({0, 1} : Finset (Fin 4))
        (π * (Equiv.swap 2 3).symm) =
      beforeCount (fun a : Fin 4 => a) ({0, 1} : Finset (Fin 4)) π :=
  beforeCount_relabel (fun a : Fin 4 => a) ({0, 1} : Finset (Fin 4)) π
    (Equiv.swap 2 3) preserving_can_move_outsider.1

end Examples.PermutationPlacementBoundary
