import Examples.ArbitraryCoverSections
import SquareKit.SmoothQuotientDeformationCharts
import SquareKit.SmoothGeometricKL
import SquareKit.SmoothRealPointCovers

/-! Incompatible deformations on the two sheets of an actual sheaf cover. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Examples.OriginalCoverRejection
open CategoryTheory SquareKit SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations SheafRelation SheafFunction
local notation "R" => PresentationGeometry.scalar topology
local notation "D" => PresentationGeometry.infinitesimal topology

/-- Even the trivial finite group gives the overlap obstruction. -/
def trivialAction : Action (locallyConstantGroup Unit) R where
  act _ _ x := x
  one_act _ _ := rfl
  mul_act _ _ _ _ := rfl
  natural _ _ _ := rfl

/-- Both arcs have the same base point, but their slopes are zero and one. -/
def coefficients (b : Bool) : R ⟶ product R R := ⟨{
  app U := ↾fun x => (x, if b then 1 else 0)
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · change (if b then 1 else 0) =
        (SmoothPresentationSite.smoothMap f.unop.unop) (if b then 1 else 0)
      change (if b then 1 else 0) =
        (SmoothPresentationSite.smoothMap f.unop.unop).toAlgHom (if b then 1 else 0)
      cases b <;> simp }⟩

def arc (b : Bool) : QuotientFixedArcs.Arcs (parameterZero R) (𝟙 R) :=
  ⟨parameterMap D (coefficients b) ≫ PresentationGeometry.affineBody, by
    ext U x
    change x + (if b then 1 else 0) * 0 = x
    simp⟩

def deformation (b : Bool) : Deformation (chart trivialAction (𝟙 R)) :=
  ofArc (arc b)

theorem arc_distinct : arc false ≠ arc true := by
  intro h
  have he := congrArg (fun k => curry k.val) h
  simp only [arc, curry_parameter] at he
  have hc := congrArg (fun k => k ≫ SmoothGeometricKL.extract) he
  change (coefficients false ≫ PresentationGeometry.affine) ≫ SmoothGeometricKL.extract =
    (coefficients true ≫ PresentationGeometry.affine) ≫ SmoothGeometricKL.extract at hc
  simp only [Category.assoc, SmoothGeometricKL.affine_extract, Category.comp_id] at hc
  have hp := congrArg (fun k : R ⟶ product R R =>
    (k.hom.app (SmoothGeometricKL.atStage (SmoothPresentationSite.free 0)) 0).2) hc
  change (0 : SmoothPresentationSite.Carrier (SmoothPresentationSite.free 0)) = 1 at hp
  have hr := congrArg SmoothOpenSite.realEvaluation hp
  change SmoothOpenSite.realEvaluation.toAlgHom 0 =
    SmoothOpenSite.realEvaluation.toAlgHom 1 at hr
  simp only [map_zero, map_one, zero_ne_one] at hr

theorem deformation_distinct : deformation false ≠ deformation true := by
  intro h
  exact arc_distinct ((chartEquiv (a := trivialAction) (𝟙 R)).symm.injective h)

/-- No matching section family on the original two-sheet cover can supply
these two deformations, although both have the prescribed zero boundary. -/
theorem no_matching_family : ¬ ∃ s : CoverSectionFamily (a := trivialAction)
    (ArbitraryCoverSections.twoSheet R),
    ((s.sections Limits.coprod.inl).obj (chart trivialAction (𝟙 R))).as = deformation false ∧
    ((s.sections Limits.coprod.inr).obj (chart trivialAction (𝟙 R))).as = deformation true := by
  rintro ⟨s, hl, hr⟩
  exact deformation_distinct (hl.symm.trans
    ((ArbitraryCoverSections.sheet_matching s _).trans hr))

end Examples.OriginalCoverRejection
