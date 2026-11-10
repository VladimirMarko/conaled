import SquareKit.Internal.PathTransport.GeneratedIdentityFamilyMap

/-! Identity restriction before discretization retains the selected arrow. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (S : Signature.{u})
local notation "L" => Instance.fullModel S.base.left S.leftFiber
local notation "R" => Instance.fullModel S.base.right S.rightFiber

def generatedIdentitySetMap (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hA : Typed.TyDeriv.{u+1} Γ γ A a)
    (hx : Typed.TmDeriv.{u+1} Γ γ A a x ξ) (hy : Typed.TmDeriv.{u+1} Γ γ A a y η) :
    directIdentity (a L) (ξ L).down (η L).down ⟶
      generatedContextMap S hΓ ⋙ directIdentity (a R) (ξ R).down (η R).down :=
  directIdentityMap (generatedFamilyMap S hΓ hA) (ξ L).down (η L).down ≫
    eqToHom (by
      rw [generatedTerm_commutes S hΓ hA hx, generatedTerm_commutes S hΓ hA hy]
      rfl)

theorem generatedFamilyMap_identity_set (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hA : Typed.TyDeriv.{u+1} Γ γ A a)
    (hx : Typed.TmDeriv.{u+1} Γ γ A a x ξ) (hy : Typed.TmDeriv.{u+1} Γ γ A a y η) :
    generatedFamilyMap S hΓ (.identity hA hx hy) =
      whiskerRight (generatedIdentitySetMap S hΓ hA hx hy) discrete := by
  rw [generatedFamilyMap_identityType]
  apply NatTrans.ext
  funext c
  simp only [generatedIdentitySetMap, identityMap, NatTrans.comp_app,
    whiskerRight_app, Functor.map_comp, eqToHom_app, eqToHom_map]

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
