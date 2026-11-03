import SquareKit.SmoothLocalizationStage
import SquareKit.SmoothLocalizationPoints
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Experimental localization clients: exponential, iterated inversion, nullary
and improper presentations, and the distinction between residue and tangent units. -/
noncomputable section
namespace Examples.SmoothLocalization
open scoped ContDiff
open SquareKit.SmoothAlgebra SquareKit.SmoothAlgebra.Localization

def exponential : Free 1 := ⟨fun x => Real.exp (x 0), by
  change ContDiff ℝ ∞ (fun x : Fin 1 → ℝ => Real.exp (x 0))
  exact Real.contDiff_exp.comp (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) (0 : Fin 1))⟩
def coordinate : Free 1 := generator 0

def exponentialPoint (x : ℝ) : Hom (Principal exponential) ℝ :=
  principalLift exponential (evaluate (fun _ => x)) (isUnit_iff_ne_zero.mpr (Real.exp_ne_zero x))

theorem exponentialPoint_base (x : ℝ) :
    Hom.comp (exponentialPoint x) (principalBase exponential) = evaluate (fun _ => x) :=
  lift_base _ _ (fun _ => isUnit_iff_ne_zero.mpr (Real.exp_ne_zero x))

theorem exponentialPoint_inverse (x : ℝ) :
    exponentialPoint x (inverse exponential) = 1 / Real.exp x :=
  real_inverse exponential ⟨fun _ => x, Real.exp_ne_zero x⟩

theorem exponential_fderiv (x v : Fin 1 → ℝ) :
    fderiv ℝ exponential.val x v = Real.exp (x 0) * v 0 := by
  have h := ((Real.hasDerivAt_exp (x 0)).comp_hasFDerivAt x (hasFDerivAt_apply (𝕜 := ℝ) 0 x)).fderiv
  exact congrArg (fun d => d v) h

theorem exponential_dual_inverse (x v : ℝ) :
    (dualPoints exponential).symm ⟨(fun _ => x, fun _ => v), Real.exp_ne_zero x⟩ (inverse exponential) =
      (⟨1 / Real.exp x, -(Real.exp x * v) / (Real.exp x)^2⟩ : DualNumber ℝ) := by
  rw [dual_inverse, exponential_fderiv]
  rfl

/-- Invert both exp(x) and x, then evaluate at x=1 through the iterated UP. -/
def twicePoint : Hom (Iterated exponential coordinate) ℝ :=
  iteratedLift exponential coordinate (exponentialPoint 1) (by
    have h := congrArg (fun k : Hom (Free 1) ℝ => k coordinate) (exponentialPoint_base 1)
    change IsUnit (exponentialPoint 1 (principalBase exponential coordinate))
    rw [show exponentialPoint 1 (principalBase exponential coordinate) = 1 from h]
    exact isUnit_one)

theorem twicePoint_restriction : Hom.comp twicePoint (first exponential coordinate) = exponentialPoint 1 :=
  iteratedLift_first _ _ _ _

theorem product_roundtrip :
    Hom.comp (iteratedToProduct exponential coordinate) (productToIterated exponential coordinate) = Hom.ident :=
  product_iterated_inverse _ _

theorem nullary_one_unchanged :
    Hom.comp (principalBase (1 : Free 0)) oneRetraction = Hom.ident := one_inverse_base

theorem nullary_zero_improper : Subsingleton (Principal (0 : Free 0)) := zero_subsingleton

theorem epsilon_not_unit : ¬IsUnit (DualNumber.eps : DualNumber ℝ) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  exact not_isUnit_zero

theorem scaling_nonidentity : tangentScale 2 ≠ Hom.ident := by
  intro h
  have hs := congrArg (fun k : Hom (DualNumber ℝ) (DualNumber ℝ) => (k DualNumber.eps).snd) h
  change (TrivSqZeroExt.map (2 • LinearMap.id) DualNumber.eps).snd = _ at hs
  simp only [TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at hs
  change (2 : ℝ) * 1 = 1 at hs
  norm_num at hs

end Examples.SmoothLocalization
