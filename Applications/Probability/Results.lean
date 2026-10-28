import Applications.Probability.Execution

/-!
# Operational result subprobabilities

Restrict the original execution law to finite termination, then push forward
the unique value and exact transition count. Missing mass is therefore actual
divergence mass. Explicit failure remains an ordinary returned sum value.
-/
namespace ProbabilityProgress
open MeasureTheory
open scoped ENNReal
variable {Ω S A : Type} [MeasurableSpace Ω]

/-- Total mathematical observation: the left unit tag denotes an infinite execution.
This uses classical choice of an existing finite derivation, not fuel search. -/
noncomputable def outcome (step : Execution Ω S A) (s : S) (ω : Ω) : Sum Unit (A × Nat) := by
  classical
  exact if h : ∃ r : A × Nat, Progress.Evaluates (step ω) s r.1 r.2
  then .inr (Classical.choose h) else .inl ()

theorem outcome_some_iff (step : Execution Ω S A) (s : S) (ω : Ω) (a : A) (k : Nat) :
    outcome step s ω = Sum.inr (a,k) ↔ Progress.Evaluates (step ω) s a k := by
  classical
  unfold outcome
  split
  · rename_i h
    have hc := Classical.choose_spec h
    constructor
    · intro eq
      have he := Sum.inr.inj eq
      simpa only [he] using hc
    · intro he
      obtain ⟨ha,hk⟩ := hc.unique he
      exact congrArg Sum.inr (Prod.ext ha hk)
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    intro he; exact h ⟨(a,k),he⟩

theorem outcome_none_iff (step : Execution Ω S A) (s : S) (ω : Ω) :
    outcome step s ω = Sum.inl () ↔ ω ∉ termination step s := by
  classical
  simp only [outcome, termination, Progress.Terminates, Set.mem_ofPred_eq]
  split
  · rename_i h
    obtain ⟨⟨a,k⟩,he⟩ := h
    simp only [reduceCtorEq, false_iff, not_not]
    exact ⟨a,k,he⟩
  · rename_i h
    simp only [true_iff]
    rintro ⟨a,k,he⟩; exact h ⟨(a,k),he⟩

theorem measurable_outcome [Countable S] [Countable A] [MeasurableSpace A]
    (step : Execution Ω S A) (hm : MeasurableSteps step) (s : S) :
    Measurable (outcome step s) := by
  apply measurable_to_countable'
  intro r
  cases r with
  | inl u =>
    cases u
    convert (measurable_termination step hm s).compl using 1
    ext ω; exact outcome_none_iff step s ω
  | inr r =>
    convert measurable_evaluates step hm s r.1 r.2 using 1
    ext ω; exact outcome_some_iff step s ω r.1 r.2

/-- Subprobability of finite returned values and costs; the left unit tag has zero mass.
Retaining the sum carrier avoids any inhabitedness assumption on outputs. -/
noncomputable def results [MeasurableSpace A] (μ : Measure Ω)
    (step : Execution Ω S A) (s : S) : Measure (Sum Unit (A × Nat)) :=
  (μ.restrict (termination step s)).map (outcome step s)

theorem results_mass [Countable S] [Countable A] [MeasurableSpace A]
    (μ : Measure Ω) (step : Execution Ω S A) (hm : MeasurableSteps step) (s : S) :
    results μ step s Set.univ = μ (termination step s) := by
  rw [results, Measure.map_apply (measurable_outcome step hm s) MeasurableSet.univ]
  simp

theorem results_mass_le_one [Countable S] [Countable A] [MeasurableSpace A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (step : Execution Ω S A)
    (hm : MeasurableSteps step) (s : S) : results μ step s Set.univ ≤ 1 := by
  rw [results_mass μ step hm s]
  exact prob_le_one

theorem divergence_mass [Countable S] [Countable A] [MeasurableSpace A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (step : Execution Ω S A)
    (hm : MeasurableSteps step) (s : S) :
    μ (termination step s)ᶜ = 1 - results μ step s Set.univ := by
  rw [results_mass μ step hm s]
  exact prob_compl_eq_one_sub (measurable_termination step hm s)

theorem results_none [Countable S] [Countable A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure Ω) (step : Execution Ω S A)
    (hm : MeasurableSteps step) (s : S) : results μ step s {Sum.inl ()} = 0 := by
  have hs : MeasurableSet ({Sum.inl ()} : Set (Sum Unit (A × Nat))) := by
    simpa only [Set.image_singleton] using (measurableSet_singleton ()).inl_image
  rw [results, Measure.map_apply (measurable_outcome step hm s) hs,
    Measure.restrict_apply ((measurable_outcome step hm s) hs)]
  have he : outcome step s ⁻¹' {Sum.inl ()} ∩ termination step s = ∅ := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      outcome_none_iff, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun h => h
  rw [he, measure_empty]

/-- Every returned value/cost atom has exactly the probability of its finite
operational derivation. This includes explicit failure outputs. -/
theorem results_some [Countable S] [Countable A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure Ω) (step : Execution Ω S A)
    (hm : MeasurableSteps step) (s : S) (a : A) (k : Nat) :
    results μ step s {Sum.inr (a,k)} = μ {ω | Progress.Evaluates (step ω) s a k} := by
  have hs : MeasurableSet ({Sum.inr (a,k)} : Set (Sum Unit (A × Nat))) := by
    simpa only [Set.image_singleton] using (measurableSet_singleton (a,k)).inr_image
  rw [results, Measure.map_apply (measurable_outcome step hm s) hs,
    Measure.restrict_apply ((measurable_outcome step hm s) hs)]
  congr 1
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    outcome_some_iff, Set.mem_ofPred_eq]
  exact ⟨And.left, fun h => ⟨h, a,k,h⟩⟩

end ProbabilityProgress
