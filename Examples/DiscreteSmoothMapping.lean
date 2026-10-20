import SquareKit.SmoothDiscreteMapping

/-! The discrete comparison retains both affine coefficients and their
restriction to zero for independently supplied scalar maps. -/
noncomputable section
namespace DiscreteSmoothMappingExamples
open CategoryTheory SquareKit SheafRelation SheafFunction SmoothGeometricKL SmoothDiscreteMapping
local notation "R" => PresentationGeometry.scalar SmoothOpenSite.topology
local notation "D" => PresentationGeometry.infinitesimal SmoothOpenSite.topology
variable {X Y : Sheaf SmoothOpenSite.topology Type}

example (a b : X ⟶ R) :
    SmoothOpenSite.parameterZero X ≫ rebuild (lift a b) = a :=
  zero_rebuild (lift a b)

example (a b : X ⟶ R) :
    coefficients (rebuild (lift a b)) ≫ snd R R = b := by
  rw [coefficients_rebuild]
  rfl

example (a b : X ⟶ R) (f : Y ⟶ X) :
    coefficients (parameterMap D f ≫ rebuild (lift a b)) = lift (f ≫ a) (f ≫ b) := by
  rw [coefficients_parameter, coefficients_rebuild]
  rfl

example (a b : X ⟶ R) (A : SmoothPresentationSite.Code)
    (d : (D).obj.obj (SmoothGeometricKL.atStage A))
    (x : X.obj.obj (SmoothGeometricKL.atStage A)) :
    ((((klMappingIso.hom.app (Opposite.op X)).toFunctor.obj ⟨lift a b⟩) :
      Discrete (product D X ⟶ R)).as).hom.app (SmoothGeometricKL.atStage A) (d,x) =
      a.hom.app (SmoothGeometricKL.atStage A) x +
        b.hom.app (SmoothGeometricKL.atStage A) x * d.val :=
  comparison_evaluation (lift a b) A d x

end DiscreteSmoothMappingExamples
