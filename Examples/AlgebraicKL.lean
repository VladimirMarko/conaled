import SquareKit.AlgebraicDerivative
import Examples.AlgebraicScalar
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Experimental KL consumers: squaring, dual-stage observation, and the
external analytic derivative of the corresponding integer polynomial.
-/
noncomputable section
namespace Examples.AlgebraicKL
open CategoryTheory Opposite
open SquareKit.AlgebraicStage SquareKit.AlgebraicKL SquareKit.AlgebraicDerivative
open SquareKit.SheafRelation SquareKit.SheafFunction

def square : scalar ⟶ scalar := lift (𝟙 _) (𝟙 _) ≫ SquareKit.AlgebraicStage.mul

def twice : scalar ⟶ scalar := lift (𝟙 _) (𝟙 _) ≫ SquareKit.AlgebraicStage.add

/-- The expected coefficient is proved unique by the constructed KL inverse. -/
theorem derivative_square : derivative square = twice := by
  apply derivative_unique
  intro A x d
  change (x+d.val)*(x+d.val) = x*x + (x+x)*d.val
  rw [AlgebraicScalar.square_expansion A x d.val d.property]
  ring

theorem derivative_square_apply (A : Stage) (x : Carrier A) :
    (derivative square).hom.app (atStage A) x = 2*x := by
  rw [derivative_square]
  change x+x = 2*x
  ring

abbrev dualIntegers := AlgebraicScalar.dualIntegers

/-- Nonzero universal epsilon is consumed by the synthetic Taylor theorem. -/
theorem square_at_epsilon (x : Carrier dualIntegers) :
    square.hom.app (atStage dualIntegers) (x+(eps .integers).val) =
      x*x + (2*x)*(eps .integers).val := by
  have h := taylor square dualIntegers x (eps .integers)
  rw [derivative_square_apply] at h
  exact h

/-- Reverse the genuine infinitesimal direction while fixing integer constants. -/
abbrev flip : dualIntegers ⟶ dualIntegers :=
  dualLift .integers dualIntegers
    (ringMap (inl .integers), ⟨-(eps .integers).val, by rw [neg_mul_neg]; exact (eps .integers).property⟩)

theorem flip_epsilon : ringMap flip DualNumber.eps = -(DualNumber.eps : Carrier dualIntegers) :=
  dualLift_eps _ _ _ _

theorem flip_not_identity : flip ≠ 𝟙 dualIntegers := by
  intro h
  have he := flip_epsilon
  rw [h] at he
  have hs := congrArg TrivSqZeroExt.snd he
  change (1 : ℤ) = -1 at hs
  norm_num at hs

/-- Derivative preservation along a proved nonidentity algebra map. -/
theorem derivative_flip (x : Carrier dualIntegers) :
    (derivative square).hom.app (atStage dualIntegers) (ringMap flip x) =
      ringMap flip ((derivative square).hom.app (atStage dualIntegers) x) :=
  congrArg (fun k : scalar.obj.obj (atStage dualIntegers) ⟶ scalar.obj.obj (atStage dualIntegers) => k x)
    ((derivative square).hom.naturality (stageMap flip))

theorem integers_infinitesimal_zero (d : infinitesimal.obj.obj (atStage .integers)) : d.val = 0 := by
  have h : (show ℤ from d.val) * (show ℤ from d.val) = 0 := d.property
  have hh : (show ℤ from d.val) = 0 := mul_self_eq_zero.mp h
  exact hh

/-- Fixed-stage evaluation sees no slope over the integers. -/
theorem same_integer_evaluation (d : infinitesimal.obj.obj (atStage .integers)) :
    (evaluation infinitesimal scalar).hom.app (atStage .integers)
      (d, affine.hom.app (atStage .integers) (0, 0)) =
    (evaluation infinitesimal scalar).hom.app (atStage .integers)
      (d, affine.hom.app (atStage .integers) (0, 1)) := by
  rw [affine_evaluation, affine_evaluation, integers_infinitesimal_zero d]
  simp

/-- Different internal slopes are distinguished by the actual inverse. -/
theorem internal_slopes_distinct :
    affine.hom.app (atStage .integers) (0, 0) ≠ affine.hom.app (atStage .integers) (0, 1) := by
  intro h
  have he := congrArg (extract.hom.app (atStage .integers)) h
  have hi (p : (product scalar scalar).obj.obj (atStage .integers)) :=
    congrArg (fun k : product scalar scalar ⟶ product scalar scalar =>
      k.hom.app (atStage .integers) p) affine_extract
  have h01 := (hi (0, 0)).symm.trans (he.trans (hi (0, 1)))
  exact Int.zero_ne_one (congrArg Prod.snd h01)

abbrev observeSlope (b : ℤ) : Carrier dualIntegers :=
  (evaluation infinitesimal scalar).hom.app (atStage dualIntegers)
    (eps .integers, functions.obj.map (stageMap (inl .integers))
      (affine.hom.app (atStage .integers) (0, b)))

/-- A slope hidden at integer points is visible after restriction to dual integers. -/
theorem slope_observed_at_dual (b : ℤ) :
    observeSlope b =
      (⟨0, b⟩ : DualNumber ℤ) := by
  have hn := congrArg (fun k : (product scalar scalar).obj.obj (atStage .integers) ⟶
    functions.obj.obj (atStage dualIntegers) => k (0, b))
    (affine.hom.naturality (stageMap (inl .integers)))
  change affine.hom.app (atStage dualIntegers)
    (ringMap (inl .integers) 0, ringMap (inl .integers) b) =
      functions.obj.map (stageMap (inl .integers))
        (affine.hom.app (atStage .integers) (0, b)) at hn
  unfold observeSlope
  erw [← hn]
  exact AlgebraicScalar.affine_at_epsilon 0 b

theorem slope_observations_distinct : observeSlope 0 ≠ observeSlope 1 := by
  rw [slope_observed_at_dual, slope_observed_at_dual]
  intro h
  exact AlgebraicScalar.epsilon_nonzero h.symm

/-- Integer polynomial corresponding to the natural squaring map. -/
def polynomial : Polynomial ℤ := Polynomial.X ^ 2

theorem square_polynomial (A : Stage) (x : Carrier A) :
    square.hom.app (atStage A) x = polynomial.eval₂ (Int.castRingHom (Carrier A)) x := by
  change x*x = _
  simp [polynomial, pow_two]

theorem coefficient_polynomial (A : Stage) (x : Carrier A) :
    (derivative square).hom.app (atStage A) x =
      polynomial.derivative.eval₂ (Int.castRingHom (Carrier A)) x := by
  rw [derivative_square_apply]
  simp [polynomial]

/-- Observe the model-derived slope at the universal polynomial variable. -/
def modelSlope : Polynomial ℤ :=
  (derivative square).hom.app (atStage (.polynomial .integers)) Polynomial.X

theorem modelSlope_eq : modelSlope = polynomial.derivative := by
  have h : (2 : Polynomial ℤ) * (Polynomial.X : Polynomial ℤ) = polynomial.derivative := by
    simp [polynomial]
  exact (derivative_square_apply (.polynomial .integers)
    (show Carrier (.polynomial .integers) from (Polynomial.X : Polynomial ℤ))).trans h

/-- Real numbers are external evaluation targets, not objects of this site.
The analytic derivative coefficient is the polynomial obtained from KL. -/
theorem analytic_square (x : ℝ) :
    HasDerivAt (fun y : ℝ => (polynomial.map (Int.castRingHom ℝ)).eval y)
      ((modelSlope.map (Int.castRingHom ℝ)).eval x) x := by
  rw [modelSlope_eq]
  simpa only [Polynomial.derivative_map] using
    (polynomial.map (Int.castRingHom ℝ)).hasDerivAt x

end Examples.AlgebraicKL
