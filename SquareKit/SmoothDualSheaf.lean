import SquareKit.SmoothDualCover
import SquareKit.SmoothOpenKL
import SquareKit.SmoothGeometricRepresentable

/-! Precomposition by the dual-stage functor is the actual exponential by D.
This constructs sheafness of dual-stage sections for arbitrary sheaves. -/
noncomputable section
namespace SquareKit.SmoothOpenSite
open CategoryTheory Opposite SmoothPresentationSite SmoothGeometricKL SheafFunction SheafRelation

local notation "D" => PresentationGeometry.infinitesimal topology

abbrev dualStages : Siteᵒᵖ ⥤ Siteᵒᵖ := dualFunctor.op.op

/-- Sheaf morphisms out of a representable are ordinary sections. -/
def sheafYonedaEquiv (A : Code) (F : Sheaf topology Type) :
    (representable (J := topology) A ⟶ F) ≃ F.obj.obj (atStage A) where
  toFun f := yonedaEquiv f.hom
  invFun x := ⟨yonedaEquiv.symm x⟩
  left_inv f := by apply Sheaf.hom_ext; exact yonedaEquiv.symm_apply_apply f.hom
  right_inv x := yonedaEquiv.apply_symm_apply x

/-- This comparison retains maps out of D × yA, not functions on real points. -/
def dualSectionsEquiv (F : Sheaf topology Type) (A : Code) :
    (exponential D F).obj.obj (atStage A) ≃ F.obj.obj (atStage (dual A)) :=
  (sheafYonedaEquiv A (exponential D F)).symm.trans
    ((show (representable A ⟶ exponential D F) ≃ (product D (representable A) ⟶ F) from
      { toFun := uncurry
        invFun := curry
        left_inv := eta
        right_inv := beta }).trans
      ((show (product D (representable A) ⟶ F) ≃ (representable (dual A) ⟶ F) from
        { toFun h := (dualRepresentable A).inv ≫ h
          invFun h := (dualRepresentable A).hom ≫ h
          left_inv h := by simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
          right_inv h := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] }).trans
        (sheafYonedaEquiv (dual A) F)))

theorem uncurry_parameter {X Y F : Sheaf topology Type} (h : X ⟶ exponential D F)
    (f : Y ⟶ X) : uncurry (f ≫ h) = parameterMap D f ≫ uncurry h := by
  apply (show Function.Injective (curry (A := D) (B := F) (X := Y)) from
    Function.LeftInverse.injective beta)
  rw [eta, curry_parameter, eta]

theorem dualSections_natural (F : Sheaf topology Type) {A B : Code} (f : A ⟶ B)
    (x : (exponential D F).obj.obj (atStage A)) :
    dualSectionsEquiv F B ((exponential D F).obj.map (stageMap f) x) =
      F.obj.map (stageMap (dualMap f)) (dualSectionsEquiv F A x) := by
  let h : representable (J := topology) A ⟶ exponential D F := (sheafYonedaEquiv A _).symm x
  have hx : (sheafYonedaEquiv B (exponential D F)).symm
      ((exponential D F).obj.map (stageMap f) x) = representableMap f ≫ h := by
    apply Sheaf.hom_ext
    exact yonedaEquiv_symm_naturality_left f.op _ x
  change yonedaEquiv (((dualRepresentable B).inv ≫ uncurry
    ((sheafYonedaEquiv B (exponential D F)).symm
      ((exponential D F).obj.map (stageMap f) x))).hom) = _
  rw [hx, uncurry_parameter]
  have hc : (dualRepresentable B).inv ≫ parameterMap D (representableMap f) =
      representableMap (dualMap f) ≫ (dualRepresentable A).inv := by
    apply (cancel_mono (dualRepresentable A).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [dualRepresentable_parameter, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hc, Category.assoc]
  exact (yonedaEquiv_naturality _ (dualMap f).op).symm

/-- The isomorphism proves that the dual-stage presheaf is a sheaf. -/
def dualSectionsIso (F : Sheaf topology Type) :
    (exponential D F).obj ≅ dualStages ⋙ F.obj :=
  NatIso.ofComponents (fun A => (dualSectionsEquiv F A.unop.unop).toIso) (by
    intro A B f
    ext x
    exact dualSections_natural F f.unop.unop x)

abbrev dualSheaf (F : Sheaf topology Type) : Sheaf topology Type :=
  ⟨dualStages ⋙ F.obj,
    (Presheaf.isSheaf_of_iso_iff (J := topology) (dualSectionsIso F)).mp (exponential D F).property⟩

/-- Restriction at zero is natural on the constructed dual-section sheaf. -/
def dualSheafZero (F : Sheaf topology Type) : dualSheaf F ⟶ F := ⟨{
  app A := F.obj.map (stageMap (dualZero A.unop.unop))
  naturality A B f := by
    change F.obj.map (stageMap (dualMap f.unop.unop)) ≫
      F.obj.map (stageMap (dualZero B.unop.unop)) =
      F.obj.map (stageMap (dualZero A.unop.unop)) ≫ F.obj.map (stageMap f.unop.unop)
    rw [← F.obj.map_comp, ← F.obj.map_comp]
    exact congrArg (fun k => F.obj.map (stageMap k)) (dualZero_natural f.unop.unop) }⟩

end SquareKit.SmoothOpenSite
