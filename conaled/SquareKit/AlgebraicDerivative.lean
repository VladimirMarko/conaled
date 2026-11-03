import SquareKit.AlgebraicKL

/-! Experimental synthetic derivatives defined by the constructed KL inverse.
Every equation concerns natural scalar morphisms, with all stage parameters.
-/
noncomputable section
namespace SquareKit.AlgebraicDerivative
open CategoryTheory
open AlgebraicStage AlgebraicKL SheafRelation SheafFunction

/-- Add the infinitesimal to the parameter. -/
def translate : product infinitesimal scalar ⟶ scalar :=
  lift (snd _ _) (fst _ _ ≫ inclusion) ≫ AlgebraicStage.add

def increment (f : scalar ⟶ scalar) : product infinitesimal scalar ⟶ scalar := translate ≫ f

/-- Extract the slope through the actual inverse of the affine map. -/
def derivative (f : scalar ⟶ scalar) : scalar ⟶ scalar := curry (increment f) ≫ kl.inv ≫ snd _ _

theorem derivative_coefficients (f : scalar ⟶ scalar) :
    derivative f = coefficients (increment f) ≫ snd _ _ := by
  unfold derivative
  rw [← Category.assoc]
  change (curry (increment f) ≫ extract) ≫ _ = _
  rw [extract_curry]

theorem intercept (f : scalar ⟶ scalar) : coefficients (increment f) ≫ fst _ _ = f := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext A
  ext x
  change (universalValue (increment f) A.unop.unop x).fst = f.hom.app A x
  have h := universal_reconstruction (increment f) A.unop.unop ⟨0, mul_zero _⟩ x
  change f.hom.app A (x + 0) =
    (universalValue (increment f) A.unop.unop x).fst +
      (universalValue (increment f) A.unop.unop x).snd * 0 at h
  simpa only [add_zero, mul_zero] using h.symm

/-- First-order Taylor at every algebra stage and every infinitesimal. -/
theorem taylor (f : scalar ⟶ scalar) (A : Stage)
    (x : Carrier A) (d : infinitesimal.obj.obj (atStage A)) :
    f.hom.app (atStage A) (x + d.val) = f.hom.app (atStage A) x +
      (derivative f).hom.app (atStage A) x * d.val := by
  have h := universal_reconstruction (increment f) A d x
  have hi := congrArg (fun k : scalar ⟶ scalar => k.hom.app (atStage A) x) (intercept f)
  rw [derivative_coefficients]
  change _ = (universalValue (increment f) A x).fst +
    (universalValue (increment f) A x).snd * d.val at h
  change (universalValue (increment f) A x).fst = f.hom.app (atStage A) x at hi
  rw [hi] at h
  exact h

/-- All-stage slope uniqueness, through KL coefficient uniqueness. -/
theorem derivative_unique (f g : scalar ⟶ scalar)
    (hg : ∀ (A : Stage) (x : Carrier A) (d : infinitesimal.obj.obj (atStage A)),
      f.hom.app (atStage A) (x+d.val) =
        f.hom.app (atStage A) x + g.hom.app (atStage A) x * d.val) : derivative f = g := by
  have he : AffineEquation (increment f) f g := fun A d x => hg A x d
  have hc := coefficients_unique (increment f) (lift f g)
    (rebuild_eq_of_equation (increment f) f g he)
  rw [derivative_coefficients, hc]
  rfl

/-- Taylor after any natural parameter assignment, not only scalar points. -/
theorem taylor_parameters {X : Sheaf topology Type} (f : scalar ⟶ scalar) (p : X ⟶ scalar) :
    AffineEquation (parameterMap infinitesimal p ≫ increment f)
      (p ≫ f) (p ≫ derivative f) := by
  intro A d x
  exact taylor f A (p.hom.app (atStage A) x) d

theorem derivative_parameters {X : Sheaf topology Type} (f : scalar ⟶ scalar)
    (p : X ⟶ scalar) :
    coefficients (parameterMap infinitesimal p ≫ increment f) ≫ snd _ _ = p ≫ derivative f := by
  rw [coefficients_parameter, derivative_coefficients, Category.assoc]

end SquareKit.AlgebraicDerivative
