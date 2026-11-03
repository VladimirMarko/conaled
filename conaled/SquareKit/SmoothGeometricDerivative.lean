import SquareKit.SmoothGeometricKL
import SquareKit.SmoothDerivative

/-! Experimental synthetic derivatives defined by the constructed KL inverse.
The topology is explicit; only scalar sheafness is assumed. Every equation
concerns natural scalar morphisms, with all stage parameters.
-/
noncomputable section
namespace SquareKit.SmoothGeometricDerivative
open CategoryTheory
open SmoothPresentationSite SmoothGeometricKL SheafRelation SheafFunction

variable {J : GrothendieckTopology SmoothPresentationSite.Site}
  [Fact (Presieve.IsSheaf J SmoothPresentationSite.scalarData)]

local notation "R" => PresentationGeometry.scalar J
local notation "D" => PresentationGeometry.infinitesimal J

/-- Add the infinitesimal to the parameter. -/
def translate : product D R ⟶ R :=
  lift (snd _ _) (fst _ _ ≫ (PresentationGeometry.inclusion (J := J))) ≫ PresentationGeometry.add

def increment (f : R ⟶ R) : product D R ⟶ R := translate ≫ f

/-- Extract the slope through the actual inverse of the affine map. -/
def derivative (f : R ⟶ R) : R ⟶ R := curry (increment f) ≫ kl.inv ≫ snd _ _

theorem derivative_coefficients (f : R ⟶ R) :
    derivative f = coefficients (increment f) ≫ snd _ _ := by
  unfold derivative
  rw [← Category.assoc]
  change (curry (increment f) ≫ extract) ≫ _ = _
  rw [extract_curry]

theorem intercept (f : R ⟶ R) : coefficients (increment f) ≫ fst _ _ = f := by
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
theorem taylor (f : R ⟶ R) (A : Code)
    (x : Carrier A) (d : (D).obj.obj (atStage A)) :
    f.hom.app (atStage A) (x + d.val) = f.hom.app (atStage A) x +
      (derivative f).hom.app (atStage A) x * d.val := by
  have h := universal_reconstruction (increment f) A d x
  have hi := congrArg (fun k : R ⟶ R => k.hom.app (atStage A) x) (intercept f)
  rw [derivative_coefficients]
  change _ = (universalValue (increment f) A x).fst +
    (universalValue (increment f) A x).snd * d.val at h
  change (universalValue (increment f) A x).fst = f.hom.app (atStage A) x at hi
  rw [hi] at h
  exact h

/-- All-stage slope uniqueness, through KL coefficient uniqueness. -/
theorem derivative_unique (f g : R ⟶ R)
    (hg : ∀ (A : Code) (x : Carrier A) (d : (D).obj.obj (atStage A)),
      f.hom.app (atStage A) (x+d.val) =
        f.hom.app (atStage A) x + g.hom.app (atStage A) x * d.val) : derivative f = g := by
  have he : AffineEquation (increment f) f g := fun A d x => hg A x d
  have hc := coefficients_unique (increment f) (lift f g)
    (rebuild_eq_of_equation (increment f) f g he)
  rw [derivative_coefficients, hc]
  rfl

/-- Taylor after any natural parameter assignment, not only scalar points. -/
theorem taylor_parameters {X : Sheaf J Type} (f : R ⟶ R) (p : X ⟶ R) :
    AffineEquation (parameterMap D p ≫ increment f)
      (p ≫ f) (p ≫ derivative f) := by
  intro A d x
  exact taylor f A (p.hom.app (atStage A) x) d

theorem derivative_parameters {X : Sheaf J Type} (f : R ⟶ R)
    (p : X ⟶ R) :
    coefficients (parameterMap D p ≫ increment f) ≫ snd _ _ = p ≫ derivative f := by
  rw [coefficients_parameter, derivative_coefficients, Category.assoc]


open SmoothAlgebra
open scoped ContDiff

abbrev unaryOperation := SmoothDerivative.unaryOperation
abbrev analyticDerivative_smooth := SmoothDerivative.analyticDerivative_smooth
abbrev unary_derivative := SmoothDerivative.unary_derivative

/-- Every ordinary globally smooth unary function acts naturally on the scalar. -/
def interpret (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) : R ⟶ R :=
  ⟨{app _ := ↾fun x => act (unaryOperation f hf) (fun _ => x)
    naturality _ _ g := by
      ext x
      exact ((smoothMap g.unop.unop).map_act (unaryOperation f hf) (fun _ => x)).symm}⟩

/-- Extraction at the actual universal dual stage gives the analytic derivative.
The left side is defined by the categorical KL inverse, not by this formula. -/
theorem derivative_interpret (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    derivative (interpret (J := J) f hf) = interpret (deriv f) (analyticDerivative_smooth f hf) := by
  apply derivative_unique
  intro A x d
  change act (unaryOperation f hf) (fun _ => x+d.val) =
    act (unaryOperation f hf) (fun _ => x) +
    act (unaryOperation (deriv f) (analyticDerivative_smooth f hf)) (fun _ => x) * d.val
  have h := nilsquare_taylor (unaryOperation f hf) (fun _ => x) (fun _ => (1 : Carrier A)) d.val d.property
  simpa only [one_mul, mul_one, Fin.sum_univ_one, unary_derivative, mul_comm] using h

/-- The real presentation is Free(0); this map observes its scalar section in ℝ. -/
def realValue : Hom (Carrier (free 0)) ℝ :=
  Hom.comp (evaluate (fun i : Fin 0 => Fin.elim0 i)) (PresentedLocalization.freeValue 0)

def realInput (x : ℝ) : Carrier (free 0) := algebraMap ℝ _ x

theorem interpret_real (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    realValue ((interpret (J := J) f hf).hom.app (atStage (free 0)) (realInput x)) = f x := by
  change realValue (act (unaryOperation f hf) (fun _ => realInput x)) = _
  rw [realValue.map_act]
  have hx : realValue (realInput x) = x := by
    exact (realValue.map_scalar x).trans (by simp)
  simp only [hx]
  rfl

/-- The coefficient is observed only after extracting through the geometric KL inverse. -/
theorem derivative_real (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    HasDerivAt f (realValue ((derivative (interpret (J := J) f hf)).hom.app
      (atStage (free 0)) (realInput x))) x := by
  rw [derivative_interpret, interpret_real]
  exact (hf.differentiable (by simp) x).hasDerivAt

end SquareKit.SmoothGeometricDerivative
