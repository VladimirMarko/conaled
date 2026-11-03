import SquareKit.SmoothGeometricKL

/-! Experimental represented dual products on the geometric site. Both variables
are natural; the target uses all smooth maps, not merely real points. -/
noncomputable section
namespace SquareKit.SmoothGeometricKL
open CategoryTheory Opposite SmoothAlgebra SmoothPresentationSite SheafRelation SheafFunction

variable {J : GrothendieckTopology SmoothPresentationSite.Site}
  [Fact (Presieve.IsSheaf J SmoothPresentationSite.scalarData)]

local notation "R" => PresentationGeometry.scalar J
local notation "D" => PresentationGeometry.infinitesimal J

variable [J.Subcanonical]

abbrev representable (A : Code) : Sheaf J Type :=
  ⟨yoneda.obj (op A), (isSheaf_iff_isSheaf_of_type _ _).mpr
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)⟩
abbrev representableMap {A B : Code} (f : A ⟶ B) : representable (J := J) B ⟶ representable (J := J) A :=
  ⟨yoneda.map f.op⟩

theorem dualLift_natural (A B C : Code) (f : A ⟶ B)
    (d : {d : Carrier B // d*d=0}) (g : B ⟶ C) :
    dualLift A B f d ≫ g = dualLift A C (f ≫ g)
      (infinitesimalData.map (stageMap g) d) := by
  apply dual_ext
  · rw [← Category.assoc, dualLift_inl, dualLift_inl]
  · change (smoothMap g) ((smoothMap (dualLift A B f d)) (eps A).val) = _
    rw [dualLift_eps, dualLift_eps]
    rfl

def dualRepresentable (A : Code) :
    product D (representable A) ≅ representable (dual A) where
  hom := ⟨{
    app T := ↾fun p => (dualLift A T.unop.unop p.2.unop p.1).op
    naturality T U g := by
      ext p
      exact congrArg Quiver.Hom.op (dualLift_natural A T.unop.unop U.unop.unop
        p.2.unop p.1 g.unop.unop).symm }⟩
  inv := ⟨{
    app T := ↾fun f => ((D).obj.map (stageMap f.unop) (eps A),
      (inl A ≫ f.unop).op)
    naturality T U g := by
      ext f
      apply Prod.ext
      · rfl
      · rfl }⟩
  hom_inv_id := by
    ext T p
    apply Prod.ext
    · exact Subtype.ext (dualLift_eps _ _ _ _)
    · exact congrArg Quiver.Hom.op (dualLift_inl _ _ _ _)
  inv_hom_id := by
    ext T f
    apply Quiver.Hom.unop_inj
    apply dual_ext
    · exact dualLift_inl _ _ _ _
    · exact dualLift_eps _ _ _ _

theorem dualLift_source {A B T : Code} (f : A ⟶ B) (g : B ⟶ T)
    (d : {d : Carrier T // d*d=0}) :
    dualMap f ≫ dualLift B T g d = dualLift A T (f ≫ g) d := by
  apply dual_ext
  · rw [← Category.assoc, dualMap_inl, Category.assoc, dualLift_inl, dualLift_inl]
  · change (smoothMap (dualLift B T g d)) ((smoothMap (dualMap f)) (eps A).val) = _
    rw [dualLift_eps, dualLift_eps, dualLift_eps]

theorem dualRepresentable_parameter {A B : Code} (f : A ⟶ B) :
    parameterMap D (representableMap f) ≫ (dualRepresentable A).hom =
      (dualRepresentable B).hom ≫ representableMap (dualMap f) := by
  ext T p
  exact congrArg Quiver.Hom.op (dualLift_source f p.2.unop p.1).symm

/-- The extracted actual dual number is the transported Yoneda value. -/
theorem universalValue_yoneda {X : Sheaf J Type}
    (h : product D X ⟶ R) (A : Code) (x : X.obj.obj (atStage A)) :
    universalValue h A x = dualToActual A (yonedaEquiv
      (((dualRepresentable A).inv ≫ parameterMap D
        (show representable A ⟶ X from ⟨yonedaEquiv.symm x⟩) ≫ h).hom)) := rfl

end SquareKit.SmoothGeometricKL
