import SquareKit.SmoothTopologyKLComparison
import Examples.GeometricSyntheticProduct
import Examples.ArbitrarySmoothCovers

/-! Experimental first-order synthetic differentiation in the arbitrary-cover
model. The shared source proof supplies the analytic product coefficient;
locality is checked on a countable cover with no finite subcover. -/
noncomputable section
namespace Examples.OpenSyntheticProduct
open CategoryTheory Opposite SquareKit SmoothPresentationSite SmoothGeometricKL
open SmoothGeometricDerivative SheafRelation

abbrev expMap := GeometricSyntheticProduct.expMap (J := SmoothOpenSite.topology)
abbrev expProduct := GeometricSyntheticProduct.expProduct (J := SmoothOpenSite.topology)
abbrev modelCoefficient := GeometricSyntheticProduct.modelCoefficient (J := SmoothOpenSite.topology)

/-- This instance reuses the all-rule soundness and source product derivation. -/
theorem source_coefficient (A : Code) (x : Carrier A) :
    (SmoothOpenSite.derivative expProduct).hom.app (atStage A) x =
      expMap.hom.app (atStage A) x * expMap.hom.app (atStage A) x +
      expMap.hom.app (atStage A) x * expMap.hom.app (atStage A) x :=
  GeometricSyntheticProduct.product_coefficient A x

theorem analytic_product (x : ℝ) :
    HasDerivAt (fun y => Real.exp y * Real.exp y) (modelCoefficient x) x :=
  GeometricSyntheticProduct.analytic_product (J := SmoothOpenSite.topology) x

theorem analytic_exp (x : ℝ) :
    HasDerivAt Real.exp (realValue ((SmoothOpenSite.derivative expMap).hom.app
      (atStage (free 0)) (realInput x))) x :=
  derivative_real (J := SmoothOpenSite.topology) _ _ x

/-- The scalar matching family is glued in the stronger category, on the genuinely infinite cover. -/
theorem infinite_locality (x : Carrier ArbitrarySmoothCovers.line) :
    SmoothGeometricLocality.gluedSlope (increment expProduct) ArbitrarySmoothCovers.line x
      (principalSieve ArbitrarySmoothCovers.line ArbitrarySmoothCovers.opens) ArbitrarySmoothCovers.covering =
      (SmoothOpenSite.derivative expProduct).hom.app (atStage ArbitrarySmoothCovers.line) x :=
  SmoothGeometricLocality.gluedDerivative _ _ _ _ _

theorem no_finite_cover (S : Finset ℕ) :
    ¬ SmoothAlgebra.OpenCover.Covers (fun i : S => ArbitrarySmoothCovers.opens i.val) :=
  ArbitrarySmoothCovers.no_finite_subcover S

/-- Taylor in the stronger model includes the internally nonzero infinitesimal. -/
theorem nilpotent_taylor (x : Carrier ArbitrarySmoothCovers.thickLine) :
    expMap.hom.app (atStage ArbitrarySmoothCovers.thickLine) (x+ArbitrarySmoothCovers.epsilon) =
      expMap.hom.app (atStage ArbitrarySmoothCovers.thickLine) x +
      (SmoothOpenSite.derivative expMap).hom.app (atStage ArbitrarySmoothCovers.thickLine) x *
        ArbitrarySmoothCovers.epsilon :=
  taylor expMap ArbitrarySmoothCovers.thickLine x (eps ArbitrarySmoothCovers.line)

theorem nilpotent_boundary : ArbitrarySmoothCovers.gluedEpsilon ≠ 0 ∧
    ∀ h : SmoothAlgebra.Hom (Carrier ArbitrarySmoothCovers.thickLine) ℝ,
      h ArbitrarySmoothCovers.gluedEpsilon=0 :=
  ⟨ArbitrarySmoothCovers.gluedEpsilon_nonzero,ArbitrarySmoothCovers.gluedEpsilon_real_zero⟩

/-- The old nonidentity stage map still acts naturally on the new inverse-defined coefficient. -/
theorem nonidentity_naturality (x : Carrier GeometricSyntheticProduct.nilStage) :
    GeometricSyntheticProduct.scale ≠ 𝟙 GeometricSyntheticProduct.nilStage ∧
    (SmoothOpenSite.derivative expProduct).hom.app (atStage GeometricSyntheticProduct.nilStage)
      (ringMap GeometricSyntheticProduct.scale x) =
      ringMap GeometricSyntheticProduct.scale
        ((SmoothOpenSite.derivative expProduct).hom.app (atStage GeometricSyntheticProduct.nilStage) x) :=
  ⟨GeometricSyntheticProduct.scale_nonidentity,
    GeometricSyntheticProduct.coefficient_scale (J := SmoothOpenSite.topology) x⟩

/-- Forgetting stronger sheafness compares the actual derivatives. -/
theorem derivative_comparison :
    SmoothOpenSite.toFinite.map (SmoothOpenSite.derivative expProduct) =
      derivative (SmoothOpenSite.toFinite.map expProduct) :=
  SmoothTopologyKLComparison.derivative_comparison SmoothOpenSite.finite_topology_le expProduct

end Examples.OpenSyntheticProduct
