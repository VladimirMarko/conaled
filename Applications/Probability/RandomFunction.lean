import Applications.Probability.QuasiBorel
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # Random functions and polynomial realization

An experimental, recursion-free sampling fragment. Values use the constructed
QBS exponential. Laws are actual measures on its random-element sigma algebra.
Sampling is from standard Borel spaces; independent sequencing uses their
product measure. No higher-order probability object or general bind is claimed.
-/

open MeasureTheory
open scoped ENNReal

namespace Applications.Probability.QuasiBorel

noncomputable def law {S : Type} [MeasurableSpace S] {X : Space}
    (μ : Measure S) (f : Hom (ofMeasurable S) X) : @Measure X (sigma X) :=
  @Measure.map S X _ (sigma X) f μ

theorem law_probability {S : Type} [MeasurableSpace S] [StandardBorelSpace S]
    {X : Space} (μ : Measure S) [IsProbabilityMeasure μ] (f : Hom (ofMeasurable S) X) :
    IsProbabilityMeasure (law μ f) := by
  let : MeasurableSpace X := sigma X
  exact (Measure.isProbabilityMeasure_map_iff f.measurable_source.aemeasurable).2 inferInstance

theorem law_map {S : Type} [MeasurableSpace S] [StandardBorelSpace S]
    {X Y : Space} (μ : Measure S) (f : Hom (ofMeasurable S) X) (g : Hom X Y) :
    @Measure.map X Y (sigma X) (sigma Y) g (law μ f) = law μ (g.comp f) := by
  let : MeasurableSpace X := sigma X
  let : MeasurableSpace Y := sigma Y
  exact Measure.map_map g.measurable f.measurable_source

/-- Full output measures, rather than just equality of finitely many moments. -/
theorem law_observe {S A : Type} [MeasurableSpace S] [StandardBorelSpace S]
    [MeasurableSpace A] {X : Space} (μ : Measure S)
    (f : Hom (ofMeasurable S) X) (g : Hom X (ofMeasurable A)) :
    @Measure.map X A (sigma X) _ g (law μ f) = μ.map (fun s => g (f s)) := by
  let : MeasurableSpace X := sigma X
  exact Measure.map_map g.measurable_observer f.measurable_source

theorem law_dirac {S : Type} [MeasurableSpace S] [StandardBorelSpace S]
    {X : Space} (s : S) (f : Hom (ofMeasurable S) X) :
    law (Measure.dirac s) f = @Measure.dirac X (sigma X) (f s) := by
  let : MeasurableSpace X := sigma X
  exact Measure.map_dirac' f.measurable_source s

/-- Deterministic bind is the only dependent sequencing operation used here. -/
theorem deterministic_bind {S : Type} [MeasurableSpace S] [StandardBorelSpace S]
    {X : Space} (μ : Measure S) (f : Hom (ofMeasurable S) X) :
    @Measure.bind S X _ (sigma X) μ (fun s => @Measure.dirac X (sigma X) (f s)) =
      law μ f := by
  let : MeasurableSpace X := sigma X
  exact Measure.bind_dirac_eq_map μ f.measurable_source

/-- Independent source draws preserve the full product law under separate observations. -/
theorem independent_observations {S T A B : Type} [MeasurableSpace S]
    [MeasurableSpace T] [StandardBorelSpace S] [StandardBorelSpace T]
    [MeasurableSpace A] [MeasurableSpace B] {X Y : Space}
    (μ : Measure S) (ν : Measure T) [SFinite ν]
    (f : Hom (ofMeasurable S) X) (g : Hom (ofMeasurable T) Y)
    (u : Hom X (ofMeasurable A)) (v : Hom Y (ofMeasurable B)) :
    (μ.prod ν).map (fun st => (u (f st.1), v (g st.2))) =
      (μ.map (fun s => u (f s))).prod (ν.map (fun t => v (g t))) := by
  exact (Measure.map_prod_map μ ν
    (u.measurable_observer.comp f.measurable_source)
    (v.measurable_observer.comp g.measurable_source)).symm

abbrev realSpace := ofMeasurable ℝ
abbrev functionSpace := exp realSpace realSpace
abbrev coefficients := ofMeasurable (ℝ × ℝ)
abbrev quadraticCoefficients := ofMeasurable (ℝ × ℝ × ℝ)

def affineEval : Hom (prod coefficients realSpace) realSpace where
  toFun p := p.1.1 * p.2 + p.1.2
  preserves h := ((measurable_fst.comp h.1).mul h.2).add (measurable_snd.comp h.1)

def affine : Hom coefficients functionSpace := curry affineEval

def squareReal : Hom realSpace realSpace := measurableHom (fun x => x ^ 2) (by fun_prop)
def squareFunction : Hom functionSpace functionSpace := curry (squareReal.comp (eval _ _))

def polynomialEval : Hom (prod quadraticCoefficients realSpace) realSpace where
  toFun p := p.1.1 * p.2 ^ 2 + p.1.2.1 * p.2 + p.1.2.2
  preserves h := by
    exact (((measurable_fst.comp h.1).mul (h.2.pow_const 2)).add
      ((measurable_fst.comp (measurable_snd.comp h.1)).mul h.2)).add
      (measurable_snd.comp (measurable_snd.comp h.1))

def polynomial : Hom quadraticCoefficients functionSpace := curry polynomialEval

def repair : Hom coefficients quadraticCoefficients :=
  measurableHom (fun e => (e.1 ^ 2, 2 * e.1 * e.2, e.2 ^ 2)) (by fun_prop)

def embedAffine : Hom coefficients quadraticCoefficients :=
  measurableHom (fun e => (0, e.1, e.2)) (by fun_prop)

/-- Arbitrary inputs can be chosen after receiving the function. -/
def observe (x y : ℝ) : Hom functionSpace (ofMeasurable (ℝ × ℝ)) where
  toFun f := (f x, f y)
  preserves h := (h id measurable_id _ measurable_const).prodMk
    (h id measurable_id _ measurable_const)

def observeThree (x y z : ℝ) : Hom functionSpace (ofMeasurable (ℝ × ℝ × ℝ)) where
  toFun f := (f x, f y, f z)
  preserves h := (h id measurable_id _ measurable_const).prodMk
    ((h id measurable_id _ measurable_const).prodMk (h id measurable_id _ measurable_const))

@[simp] theorem affine_apply (e : ℝ × ℝ) (x : ℝ) : affine e x = e.1 * x + e.2 := rfl
@[simp] theorem squareFunction_apply (f : functionSpace) (x : ℝ) :
    squareFunction f x = (f x) ^ 2 := rfl
@[simp] theorem polynomial_apply (e : ℝ × ℝ × ℝ) (x : ℝ) :
    polynomial e x = e.1 * x ^ 2 + e.2.1 * x + e.2.2 := rfl

theorem affine_continuous (e : ℝ × ℝ) : Continuous (affine e) := by
  change Continuous (fun x => e.1 * x + e.2)
  fun_prop

theorem square_affine_continuous (e : ℝ × ℝ) : Continuous (squareFunction (affine e)) :=
  (affine_continuous e).pow 2

theorem repair_meaning : polynomial.comp repair = squareFunction.comp affine := by
  ext e x
  change e.1 ^ 2 * x ^ 2 + 2 * e.1 * e.2 * x + e.2 ^ 2 = (e.1 * x + e.2) ^ 2
  ring

theorem embedAffine_meaning : polynomial.comp embedAffine = affine := by
  ext e x
  change 0 * x ^ 2 + e.1 * x + e.2 = e.1 * x + e.2
  ring

theorem shared_law (μ : Measure (ℝ × ℝ)) (x y : ℝ) :
    @Measure.map functionSpace (ℝ × ℝ) (sigma functionSpace) _ (observe x y)
      (law μ affine) = μ.map (fun e => (e.1 * x + e.2, e.1 * y + e.2)) :=
  law_observe μ affine (observe x y)

theorem nonlinear_law (μ : Measure (ℝ × ℝ)) (x y z : ℝ) :
    @Measure.map functionSpace (ℝ × ℝ × ℝ) (sigma functionSpace) _ (observeThree x y z)
      (law μ (squareFunction.comp affine)) =
      μ.map (fun e => ((e.1 * x + e.2)^2, (e.1 * y + e.2)^2, (e.1 * z + e.2)^2)) :=
  law_observe μ (squareFunction.comp affine) (observeThree x y z)

/-- The repaired coefficients carry the pushforward of the original joint law. -/
theorem repaired_law (μ : Measure (ℝ × ℝ)) :
    law (μ.map repair) polynomial = law μ (squareFunction.comp affine) := by
  let : MeasurableSpace functionSpace := sigma functionSpace
  change (μ.map repair).map polynomial = _
  rw [Measure.map_map polynomial.measurable_source (by change Measurable repair.toFun; fun_prop)]
  change law μ (polynomial.comp repair) = _
  rw [repair_meaning]

/-- Two separately sampled values are paired before observation. -/
def independentFamily : Hom (ofMeasurable ((ℝ × ℝ) × (ℝ × ℝ)))
    (prod functionSpace functionSpace) :=
  pair (affine.comp (measurableHom Prod.fst measurable_fst))
    (affine.comp (measurableHom Prod.snd measurable_snd))

def observeIndependent (x y : ℝ) : Hom (prod functionSpace functionSpace)
    (ofMeasurable (ℝ × ℝ)) where
  toFun p := (p.1 x, p.2 y)
  preserves h := (h.1 id measurable_id _ measurable_const).prodMk
    (h.2 id measurable_id _ measurable_const)

theorem independent_law (μ : Measure (ℝ × ℝ)) (x y : ℝ) :
    @Measure.map (prod functionSpace functionSpace) (ℝ × ℝ)
      (sigma (prod functionSpace functionSpace)) _ (observeIndependent x y)
      (law (μ.prod μ) independentFamily) =
    (μ.prod μ).map (fun e => (e.1.1 * x + e.1.2, e.2.1 * y + e.2.2)) :=
  law_observe (μ.prod μ) independentFamily (observeIndependent x y)

noncomputable def uniform01 : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure uniform01 where
  measure_univ := by norm_num [uniform01, Measure.restrict_apply, Real.volume_Icc]

noncomputable def coefficientLaw : Measure (ℝ × ℝ) := uniform01.prod uniform01
instance : IsProbabilityMeasure coefficientLaw := inferInstanceAs
  (IsProbabilityMeasure (uniform01.prod uniform01))

end Applications.Probability.QuasiBorel
