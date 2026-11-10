import SquareKit.SmoothOpenKL
import SquareKit.SmoothGeometricKL
import SquareKit.SmoothRealPointCovers

/-! Two overlapping copies can agree at the zero boundary while supplying
incompatible internal arcs. This is a stage-level obstruction to matching,
not a construction of the whole parameter-section contract. -/
noncomputable section
namespace Examples.ParameterSectionRejection
open CategoryTheory SquareKit SmoothPresentationSite SmoothOpenSite
open SheafRelation SheafFunction
local notation "R" => PresentationGeometry.scalar SmoothOpenSite.topology
local notation "D" => PresentationGeometry.infinitesimal SmoothOpenSite.topology
local notation "U" => SmoothGeometricKL.atStage (free 0)

/-- The copies supply slope zero and slope one at the same zero base value. -/
def sheetArc (b : Bool) : (exponential D R).obj.obj U :=
  (PresentationGeometry.affine (J := SmoothOpenSite.topology)).hom.app U (0, if b then 1 else 0)

/-- Testing only the boundary value accepts both local choices. -/
theorem sheetArc_zero (b : Bool) :
    (evaluation D R).hom.app U (⟨0, by simp⟩, sheetArc b) = 0 := by
  change (evaluation D R).hom.app U (⟨0, by simp⟩,
    (PresentationGeometry.affine (J := SmoothOpenSite.topology)).hom.app U (0, if b then 1 else 0)) = _
  rw [PresentationGeometry.affine_evaluation]
  simp

/-- Coefficient extraction distinguishes the two actual internal arcs. -/
theorem sheetArc_distinct : sheetArc false ≠ sheetArc true := by
  intro h
  have he := congrArg ((SmoothGeometricKL.extract (J := SmoothOpenSite.topology)).hom.app U) h
  have hi (p : (product R R).obj.obj U) :=
    congrArg (fun k : product R R ⟶ product R R => k.hom.app U p)
      (SmoothGeometricKL.affine_extract (J := SmoothOpenSite.topology))
  have h01 := (hi (0,0)).symm.trans (he.trans (hi (0,1)))
  have hc : (0 : Carrier (free 0)) = 1 := congrArg Prod.snd h01
  have hr := congrArg realEvaluation hc
  change realEvaluation.toAlgHom 0 = realEvaluation.toAlgHom 1 at hr
  simp only [map_zero, map_one, zero_ne_one] at hr

/-- There is no common value on the overlap of these two copies. Thus boundary
agreement alone cannot replace overlap matching in local-section gluing. -/
theorem no_common_arc : ¬ ∃ v : (exponential D R).obj.obj U, ∀ b, sheetArc b = v := by
  rintro ⟨v,hv⟩
  exact sheetArc_distinct ((hv false).trans (hv true).symm)

end Examples.ParameterSectionRejection
