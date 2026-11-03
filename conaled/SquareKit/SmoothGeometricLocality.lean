import SquareKit.SmoothGeometricDerivative
import SquareKit.SmoothCoverCharacterization

/-! Experimental locality of the extracted geometric coefficient. Gluing uses
the actual scalar sheaf condition on covering sieves, including proper covers. -/
noncomputable section
namespace SquareKit.SmoothGeometricLocality
open CategoryTheory Opposite SmoothPresentationSite SmoothGeometricKL SheafRelation

variable {J : GrothendieckTopology SmoothPresentationSite.Site}
  [Fact (Presieve.IsSheaf J SmoothPresentationSite.scalarData)]


variable {X : Sheaf J Type} (h : product (PresentationGeometry.infinitesimal J) X ⟶ (PresentationGeometry.scalar J))
variable (A : Code) (x : X.obj.obj (atStage A)) (S : Sieve (op A))

def slopeMatching : Presieve.FamilyOfElements scalarData S.arrows :=
  fun _ f _ => ((coefficients h) ≫ snd (PresentationGeometry.scalar J) (PresentationGeometry.scalar J)).hom.app _ (X.obj.map f.op x)

theorem slope_amalgamation : (slopeMatching h A x S).IsAmalgamation
    (((coefficients h) ≫ snd (PresentationGeometry.scalar J) (PresentationGeometry.scalar J)).hom.app (atStage A) x) := by
  intro V f hf
  exact (NatTrans.naturality_apply ((coefficients h) ≫ snd (PresentationGeometry.scalar J) (PresentationGeometry.scalar J)).hom f.op x).symm

theorem slope_compatible : (slopeMatching h A x S).Compatible :=
  Presieve.is_compatible_of_exists_amalgamation _ ⟨_,slope_amalgamation h A x S⟩

def gluedSlope (hS : S ∈ J (op A)) : Carrier A :=
  ((Fact.out : Presieve.IsSheaf J scalarData) S hS).amalgamate (slopeMatching h A x S) (slope_compatible h A x S)

theorem gluedSlope_eq (hS : S ∈ J (op A)) :
    gluedSlope h A x S hS = ((coefficients h) ≫ snd (PresentationGeometry.scalar J) (PresentationGeometry.scalar J)).hom.app (atStage A) x :=
  ((Fact.out : Presieve.IsSheaf J scalarData) S hS).isSeparatedFor _ _ _
    (((Fact.out : Presieve.IsSheaf J scalarData) S hS).isAmalgamation (slope_compatible h A x S))
    (slope_amalgamation h A x S)

/-- Actual cover gluing computes the inverse-defined derivative. -/
theorem gluedDerivative (f : (PresentationGeometry.scalar J) ⟶ (PresentationGeometry.scalar J)) (A : Code) (x : Carrier A)
    (S : Sieve (op A)) (hS : S ∈ J (op A)) :
    gluedSlope (SmoothGeometricDerivative.increment f) A x S hS =
      (SmoothGeometricDerivative.derivative f).hom.app (atStage A) x := by
  rw [gluedSlope_eq, SmoothGeometricDerivative.derivative_coefficients]

end SquareKit.SmoothGeometricLocality
