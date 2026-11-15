import SquareKit.Internal.PathTransport.TwoFamilySectionLaws
import SquareKit.Internal.PathTransport.TwoFamilyMap
/-! Transport of arbitrary higher sections through coherent family maps. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Bicategory.Strict Γ]
variable {F G : Family.{u,v,w,u',v',w'} Γ}
variable (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
theorem StrongMap.toHigher_projection :
    (StrongMap.toHigher η).comp (projectionHigher G) = projectionHigher F :=
  StrictTwoTransformation.functor_ext rfl
/-- Transport every higher section through a coherent family transformation. -/
def Section.map (s : Section F) : Section G where
  lift := s.lift.comp (StrongMap.toHigher η)
  over := by
    calc
      (s.lift.comp (StrongMap.toHigher η)).comp (projectionHigher G) =
        s.lift.comp ((StrongMap.toHigher η).comp (projectionHigher G)) :=
          StrictTwoTransformation.functor_ext rfl
      _ = s.lift.comp (projectionHigher F) := congrArg (fun H => s.lift.comp H)
        (StrongMap.toHigher_projection η)
      _ = StrictPseudofunctor.id Γ := s.over
variable (F)

/-- The identity coherent family map fixes the entire section. -/
theorem Section.map_identity (s : Section F) :
    s.map (Pseudofunctor.StrongTrans.id F.toPseudofunctor) = s := by
  apply Section.ext_fiber F
  · intro x
    rfl
  · intro x y p
    dsimp [Section.map, StrongMap.toHigher, StrongMap.map,
      Pseudofunctor.StrongTrans.id]
    simp only [Iso.trans_inv, Bicategory.Strict.leftUnitor_eqToIso,
      Bicategory.Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
      eqToHom_trans, StrongMap.classifier_eqToHom_app,
      StrictTwoTransformation.Trans.comp_app, StrictTwoTransformation.Trans.eqToHom_app,
      Category.id_comp, Category.comp_id]
    exact eqToHom_comp_heq _ _
  · intro x y p q α
    change HEq (((((λ_ (F.map (s.lift.map p).base)).hom ≫
      (ρ_ (F.map (s.lift.map p).base)).inv).app (s.lift.obj x).fiber) ◁
        (s.lift.map₂ α).fiber) ≫ eqToHom _) (s.lift.map₂ α).fiber
    refine HEq.trans (comp_eqToHom_heq _ _) ?_
    rw [@Bicategory.Strict.leftUnitor_eqToIso StrictTwoCategory _ _ _ _
      (F.map (s.lift.map p).base)]
    rw [@Bicategory.Strict.rightUnitor_eqToIso StrictTwoCategory _ _ _ _
      (F.map (s.lift.map p).base)]
    simp only [eqToIso.hom, eqToIso.inv]
    rw [eqToHom_trans]
    rw [StrongMap.classifier_eqToHom_app]
    exact eqToHom_left_heq (B := F.obj (s.lift.obj y).base) _ (s.lift.map₂ α).fiber

end SquareKit.Internal.PathTransport.TwoFamily
