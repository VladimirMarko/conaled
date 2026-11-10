import SquareKit.Internal.PathTransport.GeneratedFamilyReindex
import SquareKit.Internal.PathTransport.GeneratedComparisonLaws

/-! Generated primitive fibers retain the actual base-term restriction square. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

theorem baseFunctor_familyImage_constant {Γ C D : Grpd.{u,u}}
    (x : GroupoidModel.Section (constant (Γ := Γ) C)) (F : C ⥤ D) :
    baseFunctor (x.familyImage (show constant C ⟶ constant D from
      { app := fun _ => F, naturality := fun {_ _} _ => rfl })) = baseFunctor x ⋙ F := by
  fapply CategoryTheory.Functor.ext
  · intro γ; rfl
  · intro γ δ f
    simp [baseFunctor, GroupoidModel.Section.familyImage, GroupoidModel.Section.lift,
      Grothendieck.map, Grpd.forgetToCat]

theorem baseFunctor_up_heq {C D : Grpd.{u,u}}
    (x : GroupoidModel.Section (constant (Γ := C) D))
    {E : Grpd.{u,u}} (h : C = E)
    {y : ULift.{u+1} (GroupoidModel.Section (constant (Γ := E) D))}
    (hy : HEq (ULift.up.{u+1} x) y) :
    HEq (ULift.up.{u+1} (baseFunctor x)) (ULift.up.{u+1} (baseFunctor y.down)) := by
  subst E
  cases eq_of_heq hy
  rfl

variable (S : Signature.{u})
local notation "M" => fullModel S
local notation "L" => Instance.fullModel S.base.left S.leftFiber
local notation "R" => Instance.fullModel S.base.right S.rightFiber

theorem generatedBaseTerm_commutes (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hx : Typed.TmDeriv.{u+1} Γ γ .base (Typed.baseCode γ) x ξ) :
    baseFunctor (ξ L).down ⋙ S.base.map =
      generatedContextMap S hΓ ⋙ baseFunctor (ξ R).down := by
  have ht := generatedTerm_commutes S hΓ (.base hΓ) hx
  rw [generatedFamilyMap_base] at ht
  have hb := congrArg baseFunctor ht
  rw [baseFunctor_familyImage_constant, baseFunctor_reindex] at hb
  exact hb

/-- Primitive fiber restriction is exactly reindexing along the checked base term. -/
theorem generatedFamilyMap_fiber (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hx : Typed.TmDeriv.{u+1} Γ γ .base (Typed.baseCode γ) x ξ) :
    generatedFamilyMap S hΓ (.fiber hx) =
      whiskerLeft (baseFunctor (ξ L).down) (whiskerRight S.fiberMap discrete) ≫
        eqToHom (congrArg (· ⋙ setFamily S.rightFiber)
          (generatedBaseTerm_commutes S hΓ hx)) := by
  apply eq_of_heq
  apply (Family.relabelMap_heq _ _ _ _ _).trans
  exact Family.reindex_map_heq S.primitive (S.baseSubstitution (ξ M)) rfl rfl
    ((leftSignatureMap S).generatedCtx hΓ) ((rightSignatureMap S).generatedCtx hΓ)
    HEq.rfl HEq.rfl
    (baseFunctor_up_heq _ ((leftSignatureMap S).generatedCtx hΓ)
      ((leftSignatureMap S).generatedTm hx).2)
    (baseFunctor_up_heq _ ((rightSignatureMap S).generatedCtx hΓ)
      ((rightSignatureMap S).generatedTm hx).2)
    (generatedBaseTerm_commutes S hΓ hx)

/-- Underlying set-valued restriction for a generated primitive fiber. -/
def generatedFiberSetMap (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hx : Typed.TmDeriv.{u+1} Γ γ .base (Typed.baseCode γ) x ξ) :
    baseFunctor (ξ L).down ⋙ S.leftFiber ⟶
      generatedContextMap S hΓ ⋙ baseFunctor (ξ R).down ⋙ S.rightFiber :=
  whiskerLeft (baseFunctor (ξ L).down) S.fiberMap ≫
    eqToHom (congrArg (· ⋙ S.rightFiber) (generatedBaseTerm_commutes S hΓ hx))

/-- Discretizing the set-valued map recovers the complete family restriction. -/
theorem generatedFamilyMap_fiber_set (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hx : Typed.TmDeriv.{u+1} Γ γ .base (Typed.baseCode γ) x ξ) :
    generatedFamilyMap S hΓ (.fiber hx) =
      whiskerRight (generatedFiberSetMap S hΓ hx) discrete := by
  rw [generatedFamilyMap_fiber]
  apply NatTrans.ext
  funext c
  simp only [generatedFiberSetMap, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.map_comp, eqToHom_app, eqToHom_map]

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
