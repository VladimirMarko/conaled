import Applications.Probability.PermutationExpectation
import Applications.Probability.PermutationOrder
import Mathlib.Probability.Independence.Integration

/-!
# Fixed-subset placement and internal order

The existing aggregate preceding count is invariant under relabeling the
members of a fixed subset. The existing internal-order observation changes
transitively under those same relabelings. The actual invariant-event fibers
therefore establish independence, rather than merely two marginal laws.

The public independence theorem observes a supplied global permutation under
its current environment through `HasLaw`. The environment need not be finite;
the premise concerns the whole global permutation, not its selected order.
Independence needs only the priority comparison relation. With an arbitrary
`LT`, the counted set can include selected identifiers themselves.

Injective linear priorities additionally give the existing explicit count
mean. Combining it with independence yields order-weighted real and extended
nonnegative moments. Real integrability is established on the finite target
and transported to the actual environment, including for signed weights.
Infinite ENNReal weights follow the existing multiplication convention.

No arbitrary-history, adaptive-subset, numeric-minimum or algorithm-work
correspondence is asserted by these fixed-observation results.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Applications.Probability.PermutationPlacement

open MeasureTheory ProbabilityTheory PermutationExpectation PermutationOrder
open scoped ENNReal BigOperators

universe u v w

variable {I : Type u} [DecidableEq I] {P : Type v}

private theorem indepFun_beforeCount_restrictedOrder_uniformOn [LT P]
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    [MeasurableSpace (List I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ a, a ∈ positions)
    (priority : I → P) (A : Finset I) :
    IndepFun (beforeCount priority A) (restrictedOrder positions A)
      (uniformOn (Set.univ : Set (Equiv.Perm I))) := by
  classical
  letI := Fintype.ofList positions hcomplete
  let μ0 : Measure (Equiv.Perm I) := uniformOn Set.univ
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _hs _ht
  let E : Set (Equiv.Perm I) := (beforeCount priority A) ⁻¹' s
  let Q := (orders positions A).filter (fun xs => xs ∈ t)
  have hpre : (restrictedOrder positions A) ⁻¹' (Q : Set (List I)) =
      (restrictedOrder positions A) ⁻¹' t := by
    apply Set.ext
    intro π
    simp only [Set.mem_preimage, Finset.mem_coe, Q, Finset.mem_filter]
    exact and_iff_right (restrictedOrder_mem_orders positions hnd hcomplete A π)
  have hInvariant : ∀ (σ : Equiv.Perm I), (∀ a, σ a ∈ A ↔ a ∈ A) →
      ∀ π, (π * σ.symm ∈ E ↔ π ∈ E) := by
    intro σ hA π
    change beforeCount priority A (π * σ.symm) ∈ s ↔ beforeCount priority A π ∈ s
    rw [beforeCount_relabel priority A π σ hA]
  have hpartition (ν : Measure (Equiv.Perm I)) :
      (∑ xs ∈ Q, ν {π | restrictedOrder positions A π = xs}) =
        ν ((restrictedOrder positions A) ⁻¹' t) := by
    have h := sum_measure_preimage_singleton (μ := ν)
      (f := restrictedOrder positions A) Q (fun _xs _ => (Set.toFinite _).measurableSet)
    rw [hpre] at h
    exact h
  have hslice (xs : List I) (hxs : xs ∈ Q) :
      μ0 (E ∩ {π | restrictedOrder positions A π = xs}) =
        μ0 E * μ0 {π | restrictedOrder positions A π = xs} := by
    have hsupport : xs ∈ orders positions A := (Finset.mem_filter.mp hxs).1
    change uniformOn Set.univ (E ∩ {π | restrictedOrder positions A π = xs}) =
      uniformOn Set.univ E * uniformOn Set.univ {π | restrictedOrder positions A π = xs}
    rw [uniformOn_inter_restrictedOrder_eq positions hnd hcomplete A E hInvariant xs,
      uniformOn_restrictedOrder_eq positions hnd hcomplete A xs]
    simp only [if_pos hsupport, div_eq_mul_inv]
  change μ0 (E ∩ (restrictedOrder positions A) ⁻¹' t) =
    μ0 E * μ0 ((restrictedOrder positions A) ⁻¹' t)
  calc
    _ = (μ0.restrict E) ((restrictedOrder positions A) ⁻¹' t) := by
      rw [Measure.restrict_apply ((Set.toFinite _).measurableSet), Set.inter_comm]
    _ = ∑ xs ∈ Q, (μ0.restrict E) {π | restrictedOrder positions A π = xs} :=
      (hpartition (μ0.restrict E)).symm
    _ = ∑ xs ∈ Q, μ0 (E ∩ {π | restrictedOrder positions A π = xs}) := by
      apply Finset.sum_congr rfl
      intro xs _hxs
      rw [Measure.restrict_apply ((Set.toFinite _).measurableSet), Set.inter_comm]
    _ = ∑ xs ∈ Q, μ0 E * μ0 {π | restrictedOrder positions A π = xs} :=
      Finset.sum_congr rfl hslice
    _ = μ0 E * ∑ xs ∈ Q, μ0 {π | restrictedOrder positions A π = xs} := by
      rw [Finset.mul_sum]
    _ = μ0 E * μ0 ((restrictedOrder positions A) ⁻¹' t) := by
      rw [hpartition μ0]

/-- The actual aggregate count and selected order are independent whenever
the observed whole permutation has the uniform global law. Only the count's
comparison relation is needed; no finiteness assumption on the environment
or stronger measurability assumption on its observation is imposed. -/
theorem indepFun_beforeCount_restrictedOrder [LT P]
    {Ω : Type w} [MeasurableSpace Ω]
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    [MeasurableSpace (List I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ a, a ∈ positions)
    (priority : I → P) (A : Finset I) {μ : Measure Ω} {Π : Ω → Equiv.Perm I}
    (hΠ : HasLaw Π (uniformOn (Set.univ : Set (Equiv.Perm I))) μ) :
    IndepFun (fun ω => beforeCount priority A (Π ω))
      (fun ω => restrictedOrder positions A (Π ω)) μ := by
  classical
  letI := Fintype.ofList positions hcomplete
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hcanonical := (indepFun_beforeCount_restrictedOrder_uniformOn
    positions hnd hcomplete priority A).measure_inter_preimage_eq_mul s t hs ht
  calc
    μ ((fun ω => beforeCount priority A (Π ω)) ⁻¹' s ∩
        (fun ω => restrictedOrder positions A (Π ω)) ⁻¹' t) =
        uniformOn Set.univ ((beforeCount priority A) ⁻¹' s ∩
          (restrictedOrder positions A) ⁻¹' t) :=
      hΠ.measure_eq ((Set.toFinite _).measurableSet)
    _ = uniformOn Set.univ ((beforeCount priority A) ⁻¹' s) *
        uniformOn Set.univ ((restrictedOrder positions A) ⁻¹' t) := hcanonical
    _ = μ ((fun ω => beforeCount priority A (Π ω)) ⁻¹' s) *
        μ ((fun ω => restrictedOrder positions A (Π ω)) ⁻¹' t) := by
      rw [hΠ.measure_eq (p := fun π => beforeCount priority A π ∈ s)
          ((Set.toFinite _).measurableSet),
        hΠ.measure_eq (p := fun π => restrictedOrder positions A π ∈ t)
          ((Set.toFinite _).measurableSet)]

/-- Exact lower-integral weighted count mean under the actual global law.
The fixed order weight may take infinity; no measurable list structure is
part of this scalar statement. Natural subtraction precedes the cast. -/
theorem lintegral_beforeCount_mul_order [LinearOrder P]
    {Ω : Type w} [MeasurableSpace Ω]
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ a, a ∈ positions)
    (priority : I → P) (hinj : Function.Injective priority) (A : Finset I)
    (g : List I → ℝ≥0∞) {μ : Measure Ω} {Π : Ω → Equiv.Perm I}
    (hΠ : HasLaw Π (uniformOn (Set.univ : Set (Equiv.Perm I))) μ) :
    (∫⁻ ω, (beforeCount priority A (Π ω) : ℝ≥0∞) *
        g (restrictedOrder positions A (Π ω)) ∂μ) =
      (((Nat.card I - A.card : ℕ) : ℝ≥0∞) / ((A.card + 1 : ℕ) : ℝ≥0∞)) *
        ∫⁻ ω, g (restrictedOrder positions A (Π ω)) ∂μ := by
  classical
  letI := Fintype.ofList positions hcomplete
  letI : MeasurableSpace (List I) := ⊤
  letI : MeasurableSingletonClass (List I) := ⟨fun _ => trivial⟩
  let μ0 : Measure (Equiv.Perm I) := uniformOn Set.univ
  have hweight : AEMeasurable (fun π => g (restrictedOrder positions A π)) μ0 :=
    (measurable_of_finite _).aemeasurable
  have hindependent : IndepFun
      (fun π => (beforeCount priority A π : ℝ≥0∞))
      (fun π => g (restrictedOrder positions A π)) μ0 := by
    have h := (indepFun_beforeCount_restrictedOrder
      positions hnd hcomplete priority A (HasLaw.id (μ := μ0))).comp
        (φ := fun n : ℕ => (n : ℝ≥0∞)) (ψ := g)
        (measurable_of_countable _) (measurable_of_countable _)
    simpa only [Function.comp_def, id_eq] using h
  have hcanonical :
      (∫⁻ π, (beforeCount priority A π : ℝ≥0∞) *
          g (restrictedOrder positions A π) ∂μ0) =
        (((Nat.card I - A.card : ℕ) : ℝ≥0∞) / ((A.card + 1 : ℕ) : ℝ≥0∞)) *
          ∫⁻ π, g (restrictedOrder positions A π) ∂μ0 := by
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
      (measurable_of_finite _).aemeasurable
      (measurable_of_finite _).aemeasurable hindependent,
      lintegral_beforeCount_uniformOn priority hinj A]
  calc
    _ = ∫⁻ π, (beforeCount priority A π : ℝ≥0∞) *
        g (restrictedOrder positions A π) ∂μ0 :=
      hΠ.lintegral_comp (measurable_of_finite _).aemeasurable
    _ = (((Nat.card I - A.card : ℕ) : ℝ≥0∞) / ((A.card + 1 : ℕ) : ℝ≥0∞)) *
        ∫⁻ π, g (restrictedOrder positions A π) ∂μ0 := hcanonical
    _ = (((Nat.card I - A.card : ℕ) : ℝ≥0∞) / ((A.card + 1 : ℕ) : ℝ≥0∞)) *
        ∫⁻ ω, g (restrictedOrder positions A (Π ω)) ∂μ := by
      congr 1
      exact (hΠ.lintegral_comp hweight).symm

private theorem real_weighted_moment [LinearOrder P]
    {Ω : Type w} [MeasurableSpace Ω]
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ a, a ∈ positions)
    (priority : I → P) (hinj : Function.Injective priority) (A : Finset I)
    (g : List I → ℝ) {μ : Measure Ω} {Π : Ω → Equiv.Perm I}
    (hΠ : HasLaw Π (uniformOn (Set.univ : Set (Equiv.Perm I))) μ) :
    Integrable (fun ω => (beforeCount priority A (Π ω) : ℝ)) μ ∧
      Integrable (fun ω => g (restrictedOrder positions A (Π ω))) μ ∧
      Integrable (fun ω => (beforeCount priority A (Π ω) : ℝ) *
        g (restrictedOrder positions A (Π ω))) μ ∧
      (∫ ω, (beforeCount priority A (Π ω) : ℝ) *
          g (restrictedOrder positions A (Π ω)) ∂μ) =
        (((Nat.card I - A.card : ℕ) : ℝ) / ((A.card + 1 : ℕ) : ℝ)) *
          ∫ ω, g (restrictedOrder positions A (Π ω)) ∂μ := by
  classical
  letI := Fintype.ofList positions hcomplete
  letI : MeasurableSpace (List I) := ⊤
  letI : MeasurableSingletonClass (List I) := ⟨fun _ => trivial⟩
  let μ0 : Measure (Equiv.Perm I) := uniformOn Set.univ
  have hcount : Integrable (fun π => (beforeCount priority A π : ℝ)) μ0 :=
    Integrable.of_finite
  have hweight : Integrable (fun π => g (restrictedOrder positions A π)) μ0 :=
    Integrable.of_finite
  have hproduct : Integrable (fun π => (beforeCount priority A π : ℝ) *
      g (restrictedOrder positions A π)) μ0 := Integrable.of_finite
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Function.comp_def] using hΠ.integrable_comp hcount
  · simpa only [Function.comp_def] using hΠ.integrable_comp hweight
  · simpa only [Function.comp_def] using hΠ.integrable_comp hproduct
  · have hindependent : IndepFun
        (fun π => (beforeCount priority A π : ℝ))
        (fun π => g (restrictedOrder positions A π)) μ0 := by
      have h := (indepFun_beforeCount_restrictedOrder
        positions hnd hcomplete priority A (HasLaw.id (μ := μ0))).comp
          (φ := fun n : ℕ => (n : ℝ)) (ψ := g)
          (measurable_of_countable _) (measurable_of_countable _)
      simpa only [Function.comp_def, id_eq] using h
    have hcanonical :
        (∫ π, (beforeCount priority A π : ℝ) *
            g (restrictedOrder positions A π) ∂μ0) =
          (((Nat.card I - A.card : ℕ) : ℝ) / ((A.card + 1 : ℕ) : ℝ)) *
            ∫ π, g (restrictedOrder positions A π) ∂μ0 := by
      rw [hindependent.integral_fun_mul_eq_mul_integral
        hcount.aestronglyMeasurable hweight.aestronglyMeasurable,
        integral_beforeCount_uniformOn priority hinj A]
    calc
      _ = ∫ π, (beforeCount priority A π : ℝ) *
          g (restrictedOrder positions A π) ∂μ0 := by
        simpa only [Function.comp_def] using
          hΠ.integral_comp hproduct.aestronglyMeasurable
      _ = (((Nat.card I - A.card : ℕ) : ℝ) / ((A.card + 1 : ℕ) : ℝ)) *
          ∫ π, g (restrictedOrder positions A π) ∂μ0 := hcanonical
      _ = (((Nat.card I - A.card : ℕ) : ℝ) / ((A.card + 1 : ℕ) : ℝ)) *
          ∫ ω, g (restrictedOrder positions A (Π ω)) ∂μ := by
        congr 1
        simpa only [Function.comp_def] using
          (hΠ.integral_comp hweight.aestronglyMeasurable).symm

/-- Exact real weighted count mean for a fixed function of the selected order.
Signed weights are allowed. The finite canonical count, weight and product
are integrable, and their integrability is transported to the actual
environment before extracting this identity. -/
theorem integral_beforeCount_mul_order [LinearOrder P]
    {Ω : Type w} [MeasurableSpace Ω]
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ a, a ∈ positions)
    (priority : I → P) (hinj : Function.Injective priority) (A : Finset I)
    (g : List I → ℝ) {μ : Measure Ω} {Π : Ω → Equiv.Perm I}
    (hΠ : HasLaw Π (uniformOn (Set.univ : Set (Equiv.Perm I))) μ) :
    (∫ ω, (beforeCount priority A (Π ω) : ℝ) *
        g (restrictedOrder positions A (Π ω)) ∂μ) =
      (((Nat.card I - A.card : ℕ) : ℝ) / ((A.card + 1 : ℕ) : ℝ)) *
        ∫ ω, g (restrictedOrder positions A (Π ω)) ∂μ :=
  (real_weighted_moment positions hnd hcomplete priority hinj A g hΠ).2.2.2

end Applications.Probability.PermutationPlacement
