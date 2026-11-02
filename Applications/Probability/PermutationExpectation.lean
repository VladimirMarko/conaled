import Applications.Probability.PermutationMinimum
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import Mathlib.Basic.ENNReal.Inv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Order.Interval.Finset.Fin

/-!
# Preceding counts and ordinal first positions

The observation counts labels whose assigned priorities precede every member
of a fixed subset. Its definition uses the ordinary `Set.ncard` convention:
an infinite set has natural cardinality zero. The finite-population laws
therefore state their finiteness assumption explicitly.

Under one uniform global permutation and injective priorities, each outside
label precedes the subset exactly when it is the minimum after inserting
that label. The existing minimum-event law and finite indicator integration
give the count's mean, including the empty subset and empty index type.
The real mean is transported with genuine finite-sample integrability.

A rank equivalence identifies the count with the actual finite-image
minimum's zero-based position. Adding one gives the one-based ordinal
expectation on a proved nonempty subset. This is not a raw numeric-priority
expectation. Neither a relative-order law alone nor a subset chosen after
sampling supplies the global-uniform, fixed-subset premise used here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Applications.Probability.PermutationExpectation

open MeasureTheory ProbabilityTheory PermutationMinimum
open scoped ENNReal BigOperators

universe u v

variable {I : Type u} {P : Type v}

/-- Count labels strictly before every member of the supplied subset.
As for `Set.ncard`, an infinite counted set gives zero. -/
noncomputable def beforeCount [LT P] (priority : I → P) (S : Finset I)
    (π : Equiv.Perm I) : ℕ :=
  Set.ncard {b | ∀ a ∈ S, priority (π b) < priority (π a)}

/-- At an empty subset every label satisfies the vacuous comparison. -/
@[simp] theorem beforeCount_empty [LT P] (priority : I → P) (π : Equiv.Perm I) :
    beforeCount priority ∅ π = Nat.card I := by
  simp [beforeCount]

/-- No member of the subset precedes itself. This bound does not require
injective priorities or a probability law. -/
theorem beforeCount_le [Finite I] [Preorder P]
    (priority : I → P) (S : Finset I) (π : Equiv.Perm I) :
    beforeCount priority S π ≤ Nat.card I - S.card := by
  have hsub : {b | ∀ a ∈ S, priority (π b) < priority (π a)} ⊆
      (S : Set I)ᶜ := by
    intro b hb hbS
    exact lt_irrefl _ (hb b hbS)
  calc
    beforeCount priority S π ≤ ((S : Set I)ᶜ).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card I - (S : Set I).ncard :=
      Set.ncard_compl (S : Set I) S.finite_toSet
    _ = Nat.card I - S.card := by rw [Set.ncard_coe_finset]

private theorem beforeEvent_eq_minimumEvent [LinearOrder P] [DecidableEq I]
    (priority : I → P) (hinj : Function.Injective priority)
    (S : Finset I) (b : I) (hb : b ∉ S) :
    {π : Equiv.Perm I | ∀ a ∈ S, priority (π b) < priority (π a)} =
      minimumEvent priority (insert b S) b := by
  apply Set.ext
  intro π
  constructor
  · intro h
    refine ⟨Finset.mem_insert_self b S, ?_⟩
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact le_rfl
    · exact (h a ha).le
  · intro h a ha
    rcases lt_or_eq_of_le (h.2 a (Finset.mem_insert_of_mem ha)) with hlt | heq
    · exact hlt
    · have hba : b = a := π.injective (hinj heq)
      exact False.elim (hb (hba.symm ▸ ha))

private theorem cast_beforeCount_eq_sum [Fintype I] [DecidableEq I] [Preorder P]
    (priority : I → P) (S : Finset I) (π : Equiv.Perm I) :
    (beforeCount priority S π : ℝ≥0∞) =
      ∑ b ∈ Finset.univ \ S,
        ({ρ : Equiv.Perm I | ∀ a ∈ S, priority (ρ b) < priority (ρ a)}).indicator
          (1 : Equiv.Perm I → ℝ≥0∞) π := by
  classical
  have hset : {b | ∀ a ∈ S, priority (π b) < priority (π a)} =
      (((Finset.univ \ S).filter
        (fun b => ∀ a ∈ S, priority (π b) < priority (π a))) : Set I) := by
    apply Set.ext
    intro b
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro hb
      exact ⟨fun hbS => lt_irrefl _ (hb b hbS), hb⟩
    · exact fun hb => hb.2
  rw [beforeCount, hset, Set.ncard_coe_finset]
  have hsum := Finset.sum_indicator_eq_sum_filter (Finset.univ \ S)
    (fun _ : I => (1 : Equiv.Perm I → ℝ≥0∞))
    (fun b => {ρ : Equiv.Perm I | ∀ a ∈ S, priority (ρ b) < priority (ρ a)})
    (fun _ : I => π)
  simpa only [Set.mem_setOf_eq, Pi.one_apply, Finset.sum_const, nsmul_eq_mul,
    mul_one] using hsum.symm

/-- Mean of the actual finite preceding count under the original uniform
global permutation. The subset is fixed and may be empty. -/
theorem lintegral_beforeCount_uniformOn [Finite I] [LinearOrder P]
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    (priority : I → P) (hinj : Function.Injective priority) (S : Finset I) :
    (∫⁻ π, (beforeCount priority S π : ℝ≥0∞)
        ∂uniformOn (Set.univ : Set (Equiv.Perm I))) =
      ((Nat.card I - S.card : ℕ) : ℝ≥0∞) / ((S.card + 1 : ℕ) : ℝ≥0∞) := by
  classical
  letI := Fintype.ofFinite I
  let μ₀ : Measure (Equiv.Perm I) := uniformOn Set.univ
  let D : Finset I := Finset.univ \ S
  let E : I → Set (Equiv.Perm I) :=
    fun b => {π | ∀ a ∈ S, priority (π b) < priority (π a)}
  have hcard : D.card = Nat.card I - S.card := by
    simp only [D, Finset.card_univ_sdiff, Nat.card_eq_fintype_card]
  calc
    (∫⁻ π, (beforeCount priority S π : ℝ≥0∞) ∂μ₀) =
        ∫⁻ π, ∑ b ∈ D, (E b).indicator (1 : Equiv.Perm I → ℝ≥0∞) π ∂μ₀ :=
      lintegral_congr (cast_beforeCount_eq_sum priority S)
    _ = ∑ b ∈ D, ∫⁻ π, (E b).indicator (1 : Equiv.Perm I → ℝ≥0∞) π ∂μ₀ :=
      lintegral_finsetSum D (fun _b _ => measurable_of_finite _)
    _ = ∑ b ∈ D, μ₀ (E b) := by
      apply Finset.sum_congr rfl
      intro b _hb
      exact lintegral_indicator_one ((Set.toFinite (E b)).measurableSet)
    _ = ∑ _b ∈ D, (((S.card + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hbS : b ∉ S := (Finset.mem_sdiff.mp hb).2
      change uniformOn Set.univ
          {π : Equiv.Perm I | ∀ a ∈ S, priority (π b) < priority (π a)} = _
      rw [beforeEvent_eq_minimumEvent priority hinj S b hbS,
        uniformOn_minimumEvent priority hinj (insert b S) b (Finset.mem_insert_self b S),
        Finset.card_insert_of_notMem hbS]
    _ = ((Nat.card I - S.card : ℕ) : ℝ≥0∞) /
        ((S.card + 1 : ℕ) : ℝ≥0∞) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard, div_eq_mul_inv]

/-- The real mean is the finite nonnegative mean transported through
`ENNReal.ofReal`; finite-sample integrability is proved explicitly. -/
theorem integral_beforeCount_uniformOn [Finite I] [LinearOrder P]
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    (priority : I → P) (hinj : Function.Injective priority) (S : Finset I) :
    (∫ π, (beforeCount priority S π : ℝ)
        ∂uniformOn (Set.univ : Set (Equiv.Perm I))) =
      ((Nat.card I - S.card : ℕ) : ℝ) / ((S.card + 1 : ℕ) : ℝ) := by
  classical
  letI := Fintype.ofFinite I
  let μ₀ : Measure (Equiv.Perm I) := uniformOn Set.univ
  have hfi : Integrable (fun π => (beforeCount priority S π : ℝ)) μ₀ :=
    Integrable.of_finite
  have hnn : 0 ≤ᵐ[μ₀] (fun π => (beforeCount priority S π : ℝ)) :=
    Filter.Eventually.of_forall fun _π => Nat.cast_nonneg _
  have hmean : ENNReal.ofReal (∫ π, (beforeCount priority S π : ℝ) ∂μ₀) =
      ((Nat.card I - S.card : ℕ) : ℝ≥0∞) / ((S.card + 1 : ℕ) : ℝ≥0∞) := by
    calc
      _ = ∫⁻ π, ENNReal.ofReal (beforeCount priority S π : ℝ) ∂μ₀ :=
        ofReal_integral_eq_lintegral_ofReal hfi hnn
      _ = ∫⁻ π, (beforeCount priority S π : ℝ≥0∞) ∂μ₀ := by
        simp only [ENNReal.ofReal_natCast]
      _ = _ := lintegral_beforeCount_uniformOn priority hinj S
  have hfinite : ((Nat.card I - S.card : ℕ) : ℝ≥0∞) /
      ((S.card + 1 : ℕ) : ℝ≥0∞) ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero S.card))
  have hnonneg : 0 ≤ ∫ π, (beforeCount priority S π : ℝ) ∂μ₀ :=
    integral_nonneg (fun _π => Nat.cast_nonneg _)
  have htransport := (ENNReal.toReal_eq_toReal_iff'
    (by simp : ENNReal.ofReal (∫ π, (beforeCount priority S π : ℝ) ∂μ₀) ≠ ∞)
    hfinite).mpr hmean
  simpa only [ENNReal.toReal_ofReal hnonneg, ENNReal.toReal_div,
    ENNReal.toReal_natCast] using htransport

/-- Under an actual rank equivalence, preceding labels correspond exactly
to the finite initial segment below the minimum assigned rank. -/
theorem beforeCount_rank_eq {U : ℕ} (rank : I ≃ Fin U)
    (S : Finset I) (hS : S.Nonempty) (π : Equiv.Perm I) :
    beforeCount rank S π =
      ((S.image (fun a => rank (π a))).min'
        (hS.image (fun a => rank (π a)))).val := by
  classical
  let e : I ≃ Fin U := π.trans rank
  let R : Finset (Fin U) := S.image e
  have hR : R.Nonempty := hS.image e
  have hset : {b | ∀ a ∈ S, rank (π b) < rank (π a)} =
      e ⁻¹' Set.Iio (R.min' hR) := by
    apply Set.ext
    intro b
    change (∀ a ∈ S, e b < e a) ↔ e b < R.min' hR
    rw [Finset.lt_min'_iff]
    constructor
    · intro hb y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      exact hb a ha
    · intro hb a ha
      exact hb (e a) (Finset.mem_image_of_mem e ha)
  calc
    beforeCount rank S π = (e ⁻¹' Set.Iio (R.min' hR)).ncard :=
      congrArg Set.ncard hset
    _ = (Set.Iio (R.min' hR)).ncard :=
      Set.ncard_preimage_of_injective_subset_range e.injective
        (fun y _hy => e.surjective y)
    _ = (Finset.Iio (R.min' hR)).card := by
      rw [← Finset.coe_Iio, Set.ncard_coe_finset]
    _ = (R.min' hR).val := Fin.card_Iio _
    _ = ((S.image (fun a => rank (π a))).min'
        (hS.image (fun a => rank (π a)))).val := rfl

/-- Expected one-based position of the actual finite-image minimum.
Nonemptiness is required only for this minimum/ordinal interpretation. -/
theorem integral_firstPosition_uniformOn {U : ℕ}
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    (rank : I ≃ Fin U) (S : Finset I) (hS : S.Nonempty) :
    (∫ π,
        ((((S.image (fun a => rank (π a))).min'
          (hS.image (fun a => rank (π a)))).val + 1 : ℕ) : ℝ)
        ∂uniformOn (Set.univ : Set (Equiv.Perm I))) =
      ((U + 1 : ℕ) : ℝ) / ((S.card + 1 : ℕ) : ℝ) := by
  classical
  letI : Finite I := Finite.of_injective rank rank.injective
  letI := Fintype.ofFinite I
  let μ₀ : Measure (Equiv.Perm I) := uniformOn Set.univ
  have hcard : Nat.card I = U := Nat.card_eq_of_equiv_fin rank
  have hle : S.card ≤ U := by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact Finset.card_le_univ S
  have hfi : Integrable (fun π => (beforeCount rank S π : ℝ)) μ₀ :=
    Integrable.of_finite
  have hvalue : ∀ π : Equiv.Perm I,
      ((((S.image (fun a => rank (π a))).min'
        (hS.image (fun a => rank (π a)))).val + 1 : ℕ) : ℝ) =
        (beforeCount rank S π : ℝ) + 1 := by
    intro π
    rw [← beforeCount_rank_eq rank S hS π, Nat.cast_add, Nat.cast_one]
  calc
    (∫ π,
        ((((S.image (fun a => rank (π a))).min'
          (hS.image (fun a => rank (π a)))).val + 1 : ℕ) : ℝ) ∂μ₀) =
        ∫ π, (beforeCount rank S π : ℝ) + 1 ∂μ₀ :=
      integral_congr_ae (Filter.Eventually.of_forall hvalue)
    _ = (∫ π, (beforeCount rank S π : ℝ) ∂μ₀) + 1 := by
      rw [integral_add hfi (integrable_const (1 : ℝ))]
      simp
    _ = ((U - S.card : ℕ) : ℝ) / ((S.card + 1 : ℕ) : ℝ) + 1 := by
      rw [integral_beforeCount_uniformOn rank rank.injective S, hcard]
    _ = ((U + 1 : ℕ) : ℝ) / ((S.card + 1 : ℕ) : ℝ) := by
      have hden : (S.card : ℝ) + 1 ≠ 0 :=
        ne_of_gt (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one)
      simp only [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
      calc
        ((U : ℝ) - S.card) / (S.card + 1) + 1 =
            ((U : ℝ) - S.card) / (S.card + 1) + (S.card + 1) / (S.card + 1) := by
          rw [div_self hden]
        _ = (((U : ℝ) - S.card) + (S.card + 1)) / (S.card + 1) :=
          (add_div _ _ _).symm
        _ = ((U : ℝ) + 1) / (S.card + 1) := by
          rw [← add_assoc, sub_add_cancel]

end Applications.Probability.PermutationExpectation
