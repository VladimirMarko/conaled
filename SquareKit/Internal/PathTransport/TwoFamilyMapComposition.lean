import SquareKit.Internal.PathTransport.TwoFamilyMap
import SquareKit.Internal.PathTransport.TwoFamilyData
import SquareKit.Internal.PathTransport.TwoFunctorData
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w u' v' w'
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ]
variable {F G H : Family.{u,v,w,u',v',w'} Γ}
variable (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
variable (θ : Pseudofunctor.StrongTrans G.toPseudofunctor H.toPseudofunctor)
namespace StrongMap
theorem vcompComparison {x y : Γ} (f : x ⟶ y) (a : F.obj x) :
    ((Pseudofunctor.StrongTrans.vcomp η θ).naturality f).inv.app a =
      (θ.naturality f).inv.app ((η.app x).obj a) ≫
        (θ.app y).map ((η.naturality f).inv.app a) := by
  dsimp [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.vcomp, Oplax.StrongTrans.mkOfOplax]
  simp only [Strict.associator_eqToIso, eqToIso.inv, eqToIso.hom]
  repeat rw [StrictTwoTransformation.Trans.comp_app]
  simp only [classifier_eqToHom_app, classifier_whiskerLeft_app,
    classifier_whiskerRight_app, eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem comp_map {x y : Total F} (p : x ⟶ y) :
    HEq (((toHigher η).comp (toHigher θ)).map p)
      ((toHigher (Pseudofunctor.StrongTrans.vcomp η θ)).map p) := by
  refine total_hom_hext H rfl rfl _ _ ?_ ?_
  · rfl
  · change HEq ((θ.naturality p.base).inv.app ((η.app x.base).obj x.fiber) ≫
      (θ.app y.base).map ((η.naturality p.base).inv.app x.fiber ≫ (η.app y.base).map p.fiber))
      (((Pseudofunctor.StrongTrans.vcomp η θ).naturality p.base).inv.app x.fiber ≫ _)
    simp only [(θ.app y.base).map_comp]
    dsimp [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
      Oplax.StrongTrans.vcomp, Oplax.StrongTrans.mkOfOplax]
    simp only [Iso.trans_inv, Iso.symm_inv, Strict.associator_eqToIso, eqToIso.inv, eqToIso.hom,
      StrictTwoTransformation.Trans.comp_app, classifier_eqToHom_app,
      classifier_whiskerLeft_app, classifier_whiskerRight_app,
      Category.assoc, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    repeat rw [StrictTwoTransformation.Trans.comp_app]
    simp only [classifier_eqToHom_app, classifier_whiskerLeft_app,
      classifier_whiskerRight_app, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    simp only [eqToHom_refl, Category.id_comp]
    rfl
private theorem comp_cell {x y : Total F} {p q : x ⟶ y} (α : p ⟶ q) :
    HEq (((toHigher η).comp (toHigher θ)).map₂ α)
      ((toHigher (Pseudofunctor.StrongTrans.vcomp η θ)).map₂ α) := by
  refine total_cell_hext H rfl rfl (comp_map η θ p) (comp_map η θ q) _ _ ?_ ?_
  · rfl
  · change HEq ((θ.naturality p.base).inv.app ((η.app x.base).obj x.fiber) ◁
      (θ.app y.base).map₂ ((η.naturality p.base).inv.app x.fiber ◁
        (η.app y.base).map₂ α.fiber ≫ eqToHom _) ≫ eqToHom _)
      (((Pseudofunctor.StrongTrans.vcomp η θ).naturality p.base).inv.app x.fiber ◁
        ((η.app y.base) ≫ (θ.app y.base)).map₂ α.fiber ≫ eqToHom _)
    simp only [(θ.app y.base).map₂_comp, (θ.app y.base).map₂_eqToHom,
      (θ.app y.base).map₂_whisker_left, Bicategory.whiskerLeft_comp,
      Bicategory.whiskerLeft_eqToHom, Category.assoc, eqToHom_trans]
    simp only [(θ.app y.base).mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv,
      Bicategory.whiskerLeft_eqToHom, Category.assoc, eqToHom_trans]
    refine HEq.trans (eqToHom_comp_heq _ _) ?_
    refine HEq.trans (comp_eqToHom_heq _ _) ?_
    apply HEq.trans _ (comp_eqToHom_heq _ _).symm
    rw [vcompComparison]
    simp only [nested_whiskerLeft]
    refine HEq.trans (eqToHom_comp_heq _ _) ?_
    refine HEq.trans (comp_eqToHom_heq _ _) ?_
    rfl

theorem toHigher_vcomp : (toHigher η).comp (toHigher θ) =
    toHigher (Pseudofunctor.StrongTrans.vcomp η θ) := by
  apply strictFunctorData_ext
  apply prelaxData_ext
  · intro x; rfl
  · intro x y p; exact comp_map η θ p
  · intro x y p q α; exact comp_cell η θ α

variable (F)
private theorem id_map {x y : Total F} (p : x ⟶ y) :
    HEq ((toHigher (Pseudofunctor.StrongTrans.id F.toPseudofunctor)).map p) p := by
  refine total_hom_hext F rfl rfl _ _ ?_ ?_
  · rfl
  · dsimp [toHigher, map, Pseudofunctor.StrongTrans.id]
    simp only [Iso.trans_inv, Strict.leftUnitor_eqToIso,
      Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
      eqToHom_trans, classifier_eqToHom_app, StrictTwoTransformation.Trans.comp_app,
      StrictTwoTransformation.Trans.eqToHom_app, Category.id_comp, Category.comp_id]
    exact eqToHom_comp_heq _ _

theorem toHigher_id : toHigher (Pseudofunctor.StrongTrans.id F.toPseudofunctor) =
    StrictPseudofunctor.id (Total F) := by
  apply strictFunctorData_ext
  apply prelaxData_ext
  · intro x; rfl
  · intro x y p; exact id_map F p
  · intro x y p q α
    refine total_cell_hext F rfl rfl (id_map F p) (id_map F q) _ _ ?_ ?_
    · rfl
    · change HEq (((((λ_ (F.map p.base)).hom ≫
        (ρ_ (F.map p.base)).inv).app x.fiber) ◁ α.fiber) ≫ eqToHom _) α.fiber
      refine HEq.trans (comp_eqToHom_heq _ _) ?_
      rw [@Strict.leftUnitor_eqToIso StrictTwoCategory _ _ _ _ (F.map p.base)]
      rw [@Strict.rightUnitor_eqToIso StrictTwoCategory _ _ _ _ (F.map p.base)]
      simp only [eqToIso.hom, eqToIso.inv]
      rw [eqToHom_trans, classifier_eqToHom_app]
      exact eqToHom_left_heq (B := F.obj y.base) _ α.fiber

end StrongMap
end SquareKit.Internal.PathTransport.TwoFamily
