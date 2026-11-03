import SquareKit.SmoothDerivative
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Experimental smooth presheaf KL clients: exponential, finite presentation,
nonidentity restriction, substitution, and the external-function boundary. -/
noncomputable section
namespace Examples.SmoothKL
open CategoryTheory Opposite
open SquareKit SmoothStage SmoothKL SmoothDerivative SmoothAlgebra SheafRelation SheafFunction

abbrev exponential : scalar ⟶ scalar := interpret Real.exp Real.contDiff_exp

theorem exponential_derivative : SmoothDerivative.derivative exponential = exponential := by
  rw [derivative_interpret]
  congr 1
  exact Real.deriv_exp

theorem exponential_real (x : ℝ) :
    HasDerivAt Real.exp ((SmoothDerivative.derivative exponential).hom.app (atStage .real) x) x :=
  derivative_real Real.exp Real.contDiff_exp x

theorem exponential_taylor (A : Stage) (x : Carrier A) (d : infinitesimal.obj.obj (atStage A)) :
    exponential.hom.app (atStage A) (x+d.val) = exponential.hom.app (atStage A) x +
      exponential.hom.app (atStage A) x*d.val := by
  have h := taylor exponential A x d
  rw [exponential_derivative] at h
  exact h

/-- Substitution into the parameter of an infinitesimal operation is checked internally. -/
theorem nonlinear_parameter :
    coefficients (parameterMap infinitesimal exponential ≫ increment exponential) ≫ snd _ _ =
      exponential ≫ exponential := by
  rw [derivative_parameters, exponential_derivative]

theorem epsilon_nonzero : (DualNumber.eps : Carrier (.dual .real)) ≠ 0 := by
  intro h
  have he := congrArg TrivSqZeroExt.snd h
  exact one_ne_zero (show (1 : ℝ) = 0 from he)

attribute [local instance] DualExtension.smoothStructure

def doubleEps : DualNumber ℝ := DualNumber.eps + DualNumber.eps
theorem doubleEps_square : doubleEps * doubleEps = 0 := by
  simp [doubleEps, add_mul, mul_add, DualNumber.eps_mul_eps]

def scaling : Stage.dual .real ⟶ Stage.dual .real :=
  DualExtension.lift (A := ℝ) (B := DualNumber ℝ) DualExtension.realHom doubleEps doubleEps_square

theorem scaling_not_identity : scaling ≠ 𝟙 _ := by
  intro h
  have he := congrArg (fun f : Stage.dual .real ⟶ Stage.dual .real => (ringMap f DualNumber.eps).snd) h
  have hs : ringMap scaling DualNumber.eps = doubleEps :=
    DualExtension.lift_eps (B := DualNumber ℝ) DualExtension.realHom doubleEps doubleEps_square
  rw [hs] at he
  change (1 : ℝ)+1=1 at he
  norm_num at he

theorem exponential_restriction (x : Carrier (.dual .real)) :
    ringMap scaling (exponential.hom.app (atStage (.dual .real)) x) =
      exponential.hom.app (atStage (.dual .real)) (ringMap scaling x) :=
  (congrArg (fun k => k x) (exponential.hom.naturality (stageMap scaling))).symm

/-- A one-relation ordinary presentation is an actual object of the stage category. -/
abbrev pointStage : Stage := .presented 1 1 (fun _ => generator 0)

def pointEvaluation : pointStage ⟶ .real :=
  SmoothAlgebra.Quotient.lift (Ideal.span (Set.range (fun _ : Fin 1 => generator (0 : Fin 1))))
    (evaluate (fun _ => (0 : ℝ))) (by
      have hi : Ideal.span (Set.range (fun _ : Fin 1 => generator (0 : Fin 1))) ≤
          RingHom.ker (evaluate (fun _ : Fin 1 => (0 : ℝ))).toAlgHom := by
        apply Ideal.span_le.mpr
        rintro f ⟨i, rfl⟩
        change evaluate (fun _ : Fin 1 => (0 : ℝ)) (generator 0) = 0
        exact evaluate_generator _ _
      exact fun f hf => hi hf)

def pointCoordinate : Carrier pointStage := Ideal.Quotient.mk _ (generator 0)

theorem presented_exponential :
    ringMap pointEvaluation (exponential.hom.app (atStage pointStage) pointCoordinate) = 1 := by
  have h := congrArg (fun k => k pointCoordinate) (exponential.hom.naturality (stageMap pointEvaluation))
  change Real.exp (ringMap pointEvaluation pointCoordinate) = _ at h
  have hz : ringMap pointEvaluation pointCoordinate = 0 := evaluate_generator (fun _ : Fin 1 => (0 : ℝ)) 0
  rw [hz] at h
  erw [Real.exp_zero] at h
  exact h.symm

/-- At a reduced real stage every external D-point is zero. -/
theorem real_infinitesimal_zero (d : infinitesimal.obj.obj (atStage .real)) : d.val=0 := by
  have hd : (show ℝ from d.val) * (show ℝ from d.val) = 0 := d.property
  have hh : (show ℝ from d.val) = 0 := mul_self_eq_zero.mp hd
  exact hh

theorem external_slopes_equal :
    (fun d : infinitesimal.obj.obj (atStage .real) => (0 : Carrier .real) + 0*d.val) =
      (fun d => (0 : Carrier .real)+1*d.val) := by
  funext d
  simp [real_infinitesimal_zero d]

/-- Evaluation of the two internal functions agrees on every real-stage external point. -/
theorem same_real_evaluation (d : infinitesimal.obj.obj (atStage .real)) :
    (evaluation infinitesimal scalar).hom.app (atStage .real)
      (d, affine.hom.app (atStage .real) (0,0)) =
    (evaluation infinitesimal scalar).hom.app (atStage .real)
      (d, affine.hom.app (atStage .real) (0,1)) := by
  rw [affine_evaluation, affine_evaluation, real_infinitesimal_zero d]
  simp

/-- Internal functions retain the hidden slope, unlike the preceding external functions. -/
theorem internal_slopes_distinct :
    affine.hom.app (atStage .real) (0,0) ≠ affine.hom.app (atStage .real) (0,1) := by
  intro h
  have he := congrArg (extract.hom.app (atStage .real)) h
  have hi (p : (product scalar scalar).obj.obj (atStage .real)) :=
    congrArg (fun k : product scalar scalar ⟶ product scalar scalar => k.hom.app (atStage .real) p) affine_extract
  have h01 := (hi (0,0)).symm.trans (he.trans (hi (0,1)))
  exact zero_ne_one (show (0 : ℝ)=1 from congrArg Prod.snd h01)

end Examples.SmoothKL
