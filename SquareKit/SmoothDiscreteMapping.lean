import SquareKit.DiscreteSheaf
import SquareKit.SmoothGeometricKL
import SquareKit.SmoothTorsorParameters

/-! The discrete mapping comparison preserves the existing smooth KL map,
its affine evaluation, and zero restriction over every sheaf parameter. -/
noncomputable section
namespace SquareKit.SmoothDiscreteMapping
open CategoryTheory Opposite SheafRelation SheafFunction SmoothPresentationSite
open SmoothOpenSite SmoothGeometricKL
local notation "R" => PresentationGeometry.scalar SmoothOpenSite.topology
local notation "D" => PresentationGeometry.infinitesimal SmoothOpenSite.topology

/-- This is the discrete image of the previously proved KL isomorphism,
followed by the actual mapping comparison. -/
def klMappingIso : DiscreteSheaf.inclusion.obj (product R R) ≅
    DiscreteSheaf.mapping D R :=
  (DiscreteSheaf.inclusion.mapIso (SmoothGeometricKL.kl (J := SmoothOpenSite.topology))) ≪≫
    DiscreteSheaf.mappingIso D R

variable {X Y : Sheaf SmoothOpenSite.topology Type}

/-- The component is the original affine reconstruction map. -/
theorem klMappingIso_apply (p : X ⟶ product R R) :
    (((klMappingIso.hom.app (op X)).toFunctor.obj ⟨p⟩) :
      Discrete (product D X ⟶ R)).as = rebuild p := by
  change uncurry (p ≫ SmoothGeometricKL.kl.hom) = rebuild p
  change uncurry (p ≫ PresentationGeometry.affine) = rebuild p
  rw [← PresentationGeometry.affine_parameters]
  exact beta _

/-- Its inverse is exactly the checked coefficient extraction operation. -/
theorem klMappingIso_inv_apply (h : product D X ⟶ R) :
    (((klMappingIso.inv.app (op X)).toFunctor.obj ⟨h⟩) :
      Discrete (X ⟶ product R R)).as = coefficients h :=
  extract_curry h

/-- Coefficients commute with every change of sheaf parameter. -/
theorem coefficients_natural (h : product D X ⟶ R) (f : Y ⟶ X) :
    coefficients (parameterMap D f ≫ h) = f ≫ coefficients h :=
  coefficients_parameter h f

/-- The forward comparison also commutes with arbitrary parameter maps. -/
theorem rebuild_natural (p : X ⟶ product R R) (f : Y ⟶ X) :
    rebuild (f ≫ p) = parameterMap D f ≫ rebuild p := rfl

/-- Affine evaluation after the discrete comparison has the original
constant and linear coefficients at every smooth presentation. -/
theorem comparison_evaluation (p : X ⟶ product R R) (A : Code)
    (d : (D).obj.obj (atStage A)) (x : X.obj.obj (atStage A)) :
    ((((klMappingIso.hom.app (op X)).toFunctor.obj ⟨p⟩) :
      Discrete (product D X ⟶ R)).as).hom.app (atStage A) (d,x) =
      (p.hom.app (atStage A) x).1 + (p.hom.app (atStage A) x).2 * d.val := by
  rw [klMappingIso_apply]
  rfl

/-- Zero evaluation is precisely projection of the constant coefficient. -/
theorem zero_coefficients (h : product D X ⟶ R) :
    parameterZero X ≫ h = coefficients h ≫ fst R R := by
  ext U x
  have he := universal_reconstruction h U.unop.unop (⟨0, by simp⟩) x
  change h.hom.app (atStage U.unop.unop) (⟨0, by simp⟩, x) =
    (universalValue h U.unop.unop x).fst
  simpa using he

theorem zero_rebuild (p : X ⟶ product R R) :
    parameterZero X ≫ rebuild p = p ≫ fst R R := by
  rw [zero_coefficients, coefficients_rebuild]

/-- The discrete product comparison returns the same two coefficient maps. -/
theorem coefficient_product (h : product D X ⟶ R) :
    (DiscreteSheaf.productEquiv R R X).functor.obj
      ⟨coefficients h⟩ =
    (⟨coefficients h ≫ fst R R⟩, ⟨coefficients h ≫ snd R R⟩) := rfl

/-- In particular the mapping comparison uses the existing internal evaluation. -/
theorem evaluation_coefficients (A : Code) (d : (D).obj.obj (atStage A))
    (f : (exponential D R).obj.obj (atStage A)) :
    (evaluation D R).hom.app (atStage A) (d,f) =
      (SmoothGeometricKL.kl.inv.hom.app (atStage A) f).1 +
        (SmoothGeometricKL.kl.inv.hom.app (atStage A) f).2 * d.val :=
  evaluation_extract A d f

end SquareKit.SmoothDiscreteMapping
