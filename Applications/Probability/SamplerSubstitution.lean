import Applications.Probability.RandomFunction

/-! Law substitution through represented randomized continuations.
The generated sigma algebra of a QBS product is retained throughout. -/
open MeasureTheory
open scoped ENNReal
namespace Applications.Probability.QuasiBorel

/-- Supply explicit fresh noise to an admitted continuation. -/
def seeded {S T : Type} [MeasurableSpace S] [MeasurableSpace T] {X Y : Space}
    (a : Hom (ofMeasurable S) X) (k : Hom (prod X (ofMeasurable T)) Y) :
    Hom (ofMeasurable (S × T)) Y :=
  k.comp (pair (a.comp (measurableHom Prod.fst measurable_fst))
    (measurableHom Prod.snd measurable_snd))

/-- Keep the semantic input, without adding its chosen seed to the observation. -/
def retain {T : Type} [MeasurableSpace T] {X Y : Space}
    (k : Hom (prod X (ofMeasurable T)) Y) : Hom (prod X (ofMeasurable T)) (prod X Y) :=
  pair (fst X _) k

/-- A random curve is itself an admitted real-parameter family. -/
def randomFamily {X : Space} (a : ℝ → X) (ha : X.random a) :
    Hom (ofMeasurable ℝ) X := ⟨a, fun hr => X.reparam ha hr⟩

/-- Integrating a measurable event over fresh noise is measurable on the
actual generated sigma algebra of X. This proves, rather than assumes, the
parameterized measurability needed for substitution. -/
theorem event_measurable {T : Type} [MeasurableSpace T] [StandardBorelSpace T]
    {X Y : Space} (ν : Measure T) [SFinite ν]
    (k : Hom (prod X (ofMeasurable T)) Y) (E : Set Y)
    (hE : @MeasurableSet Y (sigma Y) E) :
    @Measurable X ℝ≥0∞ (sigma X) inferInstance (fun x => ν {t | k (x,t) ∈ E}) := by
  let q : Hom X (ofMeasurable ℝ≥0∞) := {
    toFun := fun x => ν {t | k (x,t) ∈ E}
    preserves := by
      intro a ha
      have h := (seeded (randomFamily a ha) k).measurable_source hE
      exact measurable_measure_prodMk_left h }
  exact q.measurable_observer

/-- The law of the seed is used only through its pushforward to semantic values. -/
theorem seeded_apply {S T : Type} [MeasurableSpace S] [StandardBorelSpace S]
    [MeasurableSpace T] [StandardBorelSpace T] {X Y : Space}
    (μ : Measure S) (ν : Measure T) [SFinite ν]
    (a : Hom (ofMeasurable S) X) (k : Hom (prod X (ofMeasurable T)) Y)
    (E : Set Y) (hE : @MeasurableSet Y (sigma Y) E) :
    law (μ.prod ν) (seeded a k) E =
      @lintegral X (sigma X) (law μ a) (fun x => ν {t | k (x,t) ∈ E}) := by
  let : MeasurableSpace X := sigma X
  let : MeasurableSpace Y := sigma Y
  rw [law, Measure.map_apply (seeded a k).measurable_source hE,
    Measure.prod_apply ((seeded a k).measurable_source hE)]
  exact (lintegral_map (event_measurable ν k E hE) a.measurable_source).symm

/-- Equal input laws may use different standard Borel seed spaces. -/
theorem law_substitution {S S' T : Type} [MeasurableSpace S] [StandardBorelSpace S]
    [MeasurableSpace S'] [StandardBorelSpace S']
    [MeasurableSpace T] [StandardBorelSpace T] {X Y : Space}
    (μ : Measure S) (μ' : Measure S') (ν : Measure T) [SFinite ν]
    (a : Hom (ofMeasurable S) X) (a' : Hom (ofMeasurable S') X)
    (k : Hom (prod X (ofMeasurable T)) Y) (h : law μ a = law μ' a') :
    law (μ.prod ν) (seeded a k) = law (μ'.prod ν) (seeded a' k) := by
  let : MeasurableSpace Y := sigma Y
  apply Measure.ext
  intro E hE
  rw [seeded_apply μ ν a k E hE, seeded_apply μ' ν a' k E hE, h]

theorem retained_law_substitution {S S' T : Type}
    [MeasurableSpace S] [StandardBorelSpace S] [MeasurableSpace S'] [StandardBorelSpace S']
    [MeasurableSpace T] [StandardBorelSpace T] {X Y : Space}
    (μ : Measure S) (μ' : Measure S') (ν : Measure T) [SFinite ν]
    (a : Hom (ofMeasurable S) X) (a' : Hom (ofMeasurable S') X)
    (k : Hom (prod X (ofMeasurable T)) Y) (h : law μ a = law μ' a') :
    law (μ.prod ν) (seeded a (retain k)) =
      law (μ'.prod ν) (seeded a' (retain k)) :=
  law_substitution μ μ' ν a a' (retain k) h

/-- Two fresh stages retain the input and both intermediate semantic values. -/
def retainedTwo {S T U : Type} [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableSpace U] {X Y Z : Space} (a : Hom (ofMeasurable S) X)
    (k : Hom (prod X (ofMeasurable T)) Y)
    (l : Hom (prod (prod X Y) (ofMeasurable U)) Z) :
    Hom (ofMeasurable ((S × T) × U)) (prod (prod X Y) Z) :=
  seeded (seeded a (retain k)) (retain l)

theorem two_stage_substitution {S S' T U : Type}
    [MeasurableSpace S] [StandardBorelSpace S] [MeasurableSpace S'] [StandardBorelSpace S']
    [MeasurableSpace T] [StandardBorelSpace T] [MeasurableSpace U] [StandardBorelSpace U]
    {X Y Z : Space} (μ : Measure S) (μ' : Measure S') (ν : Measure T) (ξ : Measure U)
    [SFinite ν] [SFinite ξ]
    (a : Hom (ofMeasurable S) X) (a' : Hom (ofMeasurable S') X)
    (k : Hom (prod X (ofMeasurable T)) Y)
    (l : Hom (prod (prod X Y) (ofMeasurable U)) Z) (h : law μ a = law μ' a') :
    law ((μ.prod ν).prod ξ) (retainedTwo a k l) =
      law ((μ'.prod ν).prod ξ) (retainedTwo a' k l) :=
  retained_law_substitution (μ.prod ν) (μ'.prod ν) ξ _ _ l
    (retained_law_substitution μ μ' ν a a' k h)

/-- Ignoring the fresh noise recovers deterministic pushforward. -/
theorem seeded_deterministic {S T : Type} [MeasurableSpace S] [StandardBorelSpace S]
    [MeasurableSpace T] [StandardBorelSpace T] {X Y : Space}
    (μ : Measure S) (ν : Measure T) [IsProbabilityMeasure ν]
    (a : Hom (ofMeasurable S) X) (g : Hom X Y) :
    law (μ.prod ν) (seeded a (g.comp (fst X (ofMeasurable T)))) =
      law μ (g.comp a) := by
  let : MeasurableSpace Y := sigma Y
  change (μ.prod ν).map ((g.comp a) ∘ Prod.fst) = μ.map (g.comp a)
  rw [← Measure.map_map (g.comp a).measurable_source measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul]

end Applications.Probability.QuasiBorel
