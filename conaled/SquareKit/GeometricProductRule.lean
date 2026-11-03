import SquareKit.Internal.SyntheticScalarGeometric

/-! Experimental optional source-to-model consequence for ordinary sheaf maps.
The public product theorem consumes a source derivation through all-rule
soundness. Ordinary scalar/model modules do not import this adapter.
-/
noncomputable section
namespace SquareKit.GeometricProductRule
open CategoryTheory
open SmoothPresentationSite SmoothGeometricKL SmoothGeometricDerivative SheafRelation
open Internal.SyntheticScalar

variable {J : GrothendieckTopology SmoothPresentationSite.Site}
  [Fact (Presieve.IsSheaf J SmoothPresentationSite.scalarData)]

local notation "R" => PresentationGeometry.scalar J
local notation "D" => PresentationGeometry.infinitesimal J

/-- Ordinary natural-map product rule, obtained from the source proof. -/
theorem product (f g : R ⟶ R) :
    derivative (lift f g ≫ PresentationGeometry.mul) =
      lift (lift (derivative f) g ≫ PresentationGeometry.mul)
        (lift f (derivative g) ≫ PresentationGeometry.mul) ≫ PresentationGeometry.add := by
  have h := GeometricSem.slope_sound (fun i : Fin 2 => if i = 0 then f else g)
    (product_rule (.param 0) (.param 1))
  simpa only [GeometricSem.map, productSlope, ite_eq_left (show (0 : Fin 2) = 0 from rfl),
    ite_eq_right (show (1 : Fin 2) ≠ 0 by decide), ite_true] using h

theorem component (f g : R ⟶ R) (A : Code) (x : Carrier A) :
    (derivative (lift f g ≫ PresentationGeometry.mul)).hom.app (atStage A) x =
      (derivative f).hom.app (atStage A) x * g.hom.app (atStage A) x +
      f.hom.app (atStage A) x * (derivative g).hom.app (atStage A) x :=
  congrArg (fun k : R ⟶ R => k.hom.app (atStage A) x) (product f g)

/-- Product differentiation remains valid under any natural parameter substitution. -/
theorem parameters {X : Sheaf J Type} (p : X ⟶ R) (f g : R ⟶ R) :
    p ≫ derivative (lift f g ≫ PresentationGeometry.mul) =
      p ≫ (lift (lift (derivative f) g ≫ PresentationGeometry.mul)
        (lift f (derivative g) ≫ PresentationGeometry.mul) ≫ PresentationGeometry.add) :=
  congrArg (fun k => p ≫ k) (product f g)

end SquareKit.GeometricProductRule
