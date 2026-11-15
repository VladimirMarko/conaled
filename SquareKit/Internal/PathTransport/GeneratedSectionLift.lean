import SquareKit.Internal.PathTransport.GeneratedComparisonLaws

/-! A generated term's section lift commutes with the actual total restriction. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

theorem section_lift_commutes {C D : Grpd.{u,u}} (R : C ⥤ D)
    {A : C ⥤ Grpd.{u,u}} {B : D ⥤ Grpd.{u,u}} (α : A ⟶ R ⋙ B)
    (x : GroupoidModel.Section A) (y : GroupoidModel.Section B)
    (ht : x.familyImage α = y.reindex R) :
    x.lift ⋙ totalMap R α = R ⋙ y.lift := by
  change (x.familyImage α).lift ⋙ Grothendieck.pre (B ⋙ Grpd.forgetToCat) R = _
  rw [ht]
  rfl

variable (S : Signature.{u})
local notation "L" => Instance.fullModel S.base.left S.leftFiber
local notation "R" => Instance.fullModel S.base.right S.rightFiber

theorem generatedSectionLift_commutes (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hA : Typed.TyDeriv.{u+1} Γ γ A a) (hx : Typed.TmDeriv.{u+1} Γ γ A a x ξ) :
    (ξ L).down.lift ⋙ totalMap (generatedContextMap S hΓ) (generatedFamilyMap S hΓ hA) =
      generatedContextMap S hΓ ⋙ (ξ R).down.lift :=
  section_lift_commutes _ _ _ _ (generatedTerm_commutes S hΓ hA hx)

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
