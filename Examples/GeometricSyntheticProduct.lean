import SquareKit.GeometricProductRule
import SquareKit.SmoothGeometricComparison
import SquareKit.SmoothGeometricRepresentable
import SquareKit.SmoothGeometricLocality
import Examples.SmoothGeometricSite
import Examples.SyntheticProduct

/-! Experimental geometric source-to-model-to-ordinary product calculation.
The source supplies the coefficient; ordinary exp calculus observes it at the
real presentation. Proper-cover gluing and nilpotent restrictions remain visible. -/
noncomputable section
namespace Examples.GeometricSyntheticProduct
open CategoryTheory Opposite SquareKit
open SmoothPresentationSite SmoothGeometricKL SmoothGeometricDerivative SheafRelation
open scoped ContDiff

variable {J : GrothendieckTopology Site} [Fact (Presieve.IsSheaf J scalarData)]
local notation "R" => PresentationGeometry.scalar J
local notation "D" => PresentationGeometry.infinitesimal J

abbrev expMap : R ⟶ R := interpret Real.exp Real.contDiff_exp
def expProduct : R ⟶ R := lift (expMap (J := J)) (expMap (J := J)) ≫ PresentationGeometry.mul

theorem derivative_exp : derivative (expMap (J := J)) = (expMap (J := J)) := by
  rw [derivative_interpret]
  simp only [Real.deriv_exp]

/-- This coefficient calculation invokes the existing source product derivation. -/
theorem product_coefficient (A : Code) (x : Carrier A) :
    (derivative (expProduct (J := J))).hom.app (atStage A) x =
      (expMap (J := J)).hom.app (atStage A) x * (expMap (J := J)).hom.app (atStage A) x +
      (expMap (J := J)).hom.app (atStage A) x * (expMap (J := J)).hom.app (atStage A) x := by
  have h := GeometricProductRule.component (expMap (J := J)) (expMap (J := J)) A x
  rw [derivative_exp] at h
  exact h

/-- An ordinary smooth operation and a source-derived derivative coexist. -/
theorem mixed_styles (x : ℝ) :
    realValue ((expMap (J := J)).hom.app (atStage (free 0)) (realInput x)) = Real.exp x ∧
    (derivative (expProduct (J := J))).hom.app (atStage (free 0)) (realInput x) =
      (expMap (J := J)).hom.app (atStage (free 0)) (realInput x) * (expMap (J := J)).hom.app (atStage (free 0)) (realInput x) +
      (expMap (J := J)).hom.app (atStage (free 0)) (realInput x) * (expMap (J := J)).hom.app (atStage (free 0)) (realInput x) :=
  ⟨interpret_real _ _ x, product_coefficient _ _⟩

def modelCoefficient (x : ℝ) : ℝ :=
  realValue ((derivative (expProduct (J := J))).hom.app (atStage (free 0)) (realInput x))

theorem modelCoefficient_eq (x : ℝ) :
    (modelCoefficient (J := J)) x = Real.exp x * Real.exp x + Real.exp x * Real.exp x := by
  unfold modelCoefficient
  rw [product_coefficient, SmoothAlgebra.Hom.map_add, SmoothAlgebra.Hom.map_mul]
  rw [interpret_real]

/-- The coefficient is extracted in the geometric model through the source proof.
The ordinary analytic verification uses exp(x+x) and the chain rule. -/
theorem analytic_product (x : ℝ) :
    HasDerivAt (fun y => Real.exp y * Real.exp y) ((modelCoefficient (J := J)) x) x := by
  rw [modelCoefficient_eq]
  have hi : HasDerivAt (fun y : ℝ => y+y) (1+1) x := (hasDerivAt_id x).add (hasDerivAt_id x)
  have h := (Real.hasDerivAt_exp (x+x)).comp x (h := fun y : ℝ => y+y) hi
  simp only [Real.exp_add, Function.comp_def] at h
  convert h using 1; ring

/-- General analytic comparison, separately retained for every smooth unary map. -/
theorem exp_analytic (x : ℝ) :
    HasDerivAt Real.exp (realValue ((derivative (expMap (J := J))).hom.app (atStage (free 0)) (realInput x))) x :=
  derivative_real _ _ x

/-- Arbitrary parameter substitution still uses the source-derived product rule. -/
theorem source_parameters {X : Sheaf J Type} (p : X ⟶ R) :
    coefficients (SheafFunction.parameterMap D p ≫ increment (expProduct (J := J))) ≫ snd R R =
      p ≫ (lift (lift (derivative (expMap (J := J))) (expMap (J := J)) ≫ PresentationGeometry.mul)
        (lift (expMap (J := J)) (derivative (expMap (J := J))) ≫ PresentationGeometry.mul) ≫ PresentationGeometry.add) := by
  rw [derivative_parameters]
  exact GeometricProductRule.parameters p (expMap (J := J)) (expMap (J := J))

/-- Gluing the locally extracted slope on a genuine proper cover recovers it. -/
theorem proper_cover_coefficient (x : Carrier SmoothGeometricSite.line) :
    SmoothGeometricLocality.gluedSlope (increment (expProduct (J := topology))) SmoothGeometricSite.line x
      (principalSieve SmoothGeometricSite.line SmoothGeometricSite.lineOpens) SmoothGeometricSite.line_cover =
      (expMap (J := topology)).hom.app (atStage SmoothGeometricSite.line) x * (expMap (J := topology)).hom.app (atStage SmoothGeometricSite.line) x +
      (expMap (J := topology)).hom.app (atStage SmoothGeometricSite.line) x * (expMap (J := topology)).hom.app (atStage SmoothGeometricSite.line) x :=
  (SmoothGeometricLocality.gluedDerivative _ _ _ _ _).trans (product_coefficient _ _)

theorem cover_is_proper :
    principalSieve SmoothGeometricSite.line SmoothGeometricSite.lineOpens ≠ ⊤ :=
  SmoothGeometricSite.line_cover_proper

abbrev nilStage := SmoothGeometricSite.Nilpotent.stage
abbrev scale : nilStage ⟶ nilStage := SmoothFormalLocalization.scaling

theorem scale_nonidentity : scale ≠ 𝟙 nilStage := by
  change SmoothFormalLocalization.scaling ≠ SmoothAlgebra.Hom.ident
  exact SmoothFormalLocalization.scaling_nonidentity

/-- A nonidentity restriction of the source-derived coefficient. -/
theorem coefficient_scale (x : Carrier nilStage) :
    (derivative (expProduct (J := J))).hom.app (atStage nilStage) (ringMap scale x) =
      ringMap scale ((derivative (expProduct (J := J))).hom.app (atStage nilStage) x) :=
  (congrArg (fun k : (R).obj.obj (atStage nilStage) ⟶ (R).obj.obj (atStage nilStage) => k x)
    ((derivative (expProduct (J := J))).hom.naturality (stageMap scale)))

/-- The geometric scalar retains an internally nonzero section invisible at real points. -/
theorem internal_external_boundary : SmoothGeometricSite.Nilpotent.glued ≠ 0 ∧
    ∀ h : SmoothAlgebra.Hom (Carrier nilStage) ℝ, h SmoothGeometricSite.Nilpotent.glued = 0 :=
  ⟨SmoothGeometricSite.Nilpotent.glued_nonzero, SmoothGeometricSite.Nilpotent.glued_real_zero⟩

/-- Ring normalization alone still cannot discard the source cross term. -/
abbrev source_boundary := SyntheticProduct.boundary_no_ring_certificate

end Examples.GeometricSyntheticProduct
