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

abbrev expMap : scalar ⟶ scalar := interpret Real.exp Real.contDiff_exp
def expProduct : scalar ⟶ scalar := lift expMap expMap ≫ SmoothPresentationSite.mul

theorem derivative_exp : derivative expMap = expMap := by
  rw [derivative_interpret]
  simp only [Real.deriv_exp]

/-- This coefficient calculation invokes the existing source product derivation. -/
theorem product_coefficient (A : Code) (x : Carrier A) :
    (derivative expProduct).hom.app (atStage A) x =
      expMap.hom.app (atStage A) x * expMap.hom.app (atStage A) x +
      expMap.hom.app (atStage A) x * expMap.hom.app (atStage A) x := by
  have h := GeometricProductRule.component expMap expMap A x
  rw [derivative_exp] at h
  exact h

/-- An ordinary smooth operation and a source-derived derivative coexist. -/
theorem mixed_styles (x : ℝ) :
    realValue (expMap.hom.app (atStage (free 0)) (realInput x)) = Real.exp x ∧
    (derivative expProduct).hom.app (atStage (free 0)) (realInput x) =
      expMap.hom.app (atStage (free 0)) (realInput x) * expMap.hom.app (atStage (free 0)) (realInput x) +
      expMap.hom.app (atStage (free 0)) (realInput x) * expMap.hom.app (atStage (free 0)) (realInput x) :=
  ⟨interpret_real _ _ x, product_coefficient _ _⟩

def modelCoefficient (x : ℝ) : ℝ :=
  realValue ((derivative expProduct).hom.app (atStage (free 0)) (realInput x))

theorem modelCoefficient_eq (x : ℝ) :
    modelCoefficient x = Real.exp x * Real.exp x + Real.exp x * Real.exp x := by
  unfold modelCoefficient
  rw [product_coefficient, SmoothAlgebra.Hom.map_add, SmoothAlgebra.Hom.map_mul]
  rw [interpret_real]

/-- The coefficient is extracted in the geometric model through the source proof.
The ordinary analytic verification uses exp(x+x) and the chain rule. -/
theorem analytic_product (x : ℝ) :
    HasDerivAt (fun y => Real.exp y * Real.exp y) (modelCoefficient x) x := by
  rw [modelCoefficient_eq]
  have hi : HasDerivAt (fun y : ℝ => y+y) (1+1) x := (hasDerivAt_id x).add (hasDerivAt_id x)
  have h := (Real.hasDerivAt_exp (x+x)).comp x (h := fun y : ℝ => y+y) hi
  simp only [Real.exp_add, Function.comp_def] at h
  convert h using 1; ring

/-- General analytic comparison, separately retained for every smooth unary map. -/
theorem exp_analytic (x : ℝ) :
    HasDerivAt Real.exp (realValue ((derivative expMap).hom.app (atStage (free 0)) (realInput x))) x :=
  derivative_real _ _ x

/-- Arbitrary parameter substitution still uses the source-derived product rule. -/
theorem source_parameters {X : Sheaf topology Type} (p : X ⟶ scalar) :
    coefficients (SheafFunction.parameterMap infinitesimal p ≫ increment expProduct) ≫ snd scalar scalar =
      p ≫ (lift (lift (derivative expMap) expMap ≫ SmoothPresentationSite.mul)
        (lift expMap (derivative expMap) ≫ SmoothPresentationSite.mul) ≫ SmoothPresentationSite.add) := by
  rw [derivative_parameters]
  exact GeometricProductRule.parameters p expMap expMap

/-- Gluing the locally extracted slope on a genuine proper cover recovers it. -/
theorem proper_cover_coefficient (x : Carrier SmoothGeometricSite.line) :
    SmoothGeometricLocality.gluedSlope (increment expProduct) SmoothGeometricSite.line x
      (principalSieve SmoothGeometricSite.line SmoothGeometricSite.lineOpens) SmoothGeometricSite.line_cover =
      expMap.hom.app (atStage SmoothGeometricSite.line) x * expMap.hom.app (atStage SmoothGeometricSite.line) x +
      expMap.hom.app (atStage SmoothGeometricSite.line) x * expMap.hom.app (atStage SmoothGeometricSite.line) x :=
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
    (derivative expProduct).hom.app (atStage nilStage) (ringMap scale x) =
      ringMap scale ((derivative expProduct).hom.app (atStage nilStage) x) :=
  (congrArg (fun k : scalar.obj.obj (atStage nilStage) ⟶ scalar.obj.obj (atStage nilStage) => k x)
    ((derivative expProduct).hom.naturality (stageMap scale)))

/-- The geometric scalar retains an internally nonzero section invisible at real points. -/
theorem internal_external_boundary : SmoothGeometricSite.Nilpotent.glued ≠ 0 ∧
    ∀ h : SmoothAlgebra.Hom (Carrier nilStage) ℝ, h SmoothGeometricSite.Nilpotent.glued = 0 :=
  ⟨SmoothGeometricSite.Nilpotent.glued_nonzero, SmoothGeometricSite.Nilpotent.glued_real_zero⟩

/-- Ring normalization alone still cannot discard the source cross term. -/
abbrev source_boundary := SyntheticProduct.boundary_no_ring_certificate

end Examples.GeometricSyntheticProduct
