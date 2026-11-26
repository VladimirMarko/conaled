import SquareKit.Internal.PathTransport.GeneratedComparisonLaws

/-! The generated identity-family map retains the chosen component arrow and
uses only the endpoint transports supplied by the generated term comparisons. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory Typed
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

namespace Family

theorem identity_relabel {Γ : Context.{u}} (A : Family Γ) (x y : Section A)
    {C D : Grpd.{u,u}} (hC : Γ.left = C) (hD : Γ.right = D)
    {B : C ⥤ Grpd.{u,u}} {E : D ⥤ Grpd.{u,u}}
    (hB : HEq A.left B) (hE : HEq A.right E)
    {xl yl : ULift.{u+1} (GroupoidModel.Section B)}
    {xr yr : ULift.{u+1} (GroupoidModel.Section E)}
    (hxl : HEq (ULift.up.{u+1} x.left) xl) (hxr : HEq (ULift.up.{u+1} x.right) xr)
    (hyl : HEq (ULift.up.{u+1} y.left) yl) (hyr : HEq (ULift.up.{u+1} y.right) yr)
    (hI : HEq (A.identity x y).left (identityFamily B xl.down yl.down))
    (hJ : HEq (A.identity x y).right (identityFamily E xr.down yr.down)) :
    (A.identity x y).relabelMap hC hD hI hJ =
      identityMap (A.relabelMap hC hD hB hE) xl.down yl.down ≫
        eqToHom (by
          rw [Section.relabel_commutes x hC hD hB hE hxl hxr,
            Section.relabel_commutes y hC hD hB hE hyl hyr]
          rfl) := by
  subst C; subst D
  cases eq_of_heq hB; cases eq_of_heq hE
  cases eq_of_heq hxl; cases eq_of_heq hxr
  cases eq_of_heq hyl; cases eq_of_heq hyr
  rfl

end Family
variable (S : Signature.{u})
local notation "M" => fullModel S
local notation "L" => Instance.fullModel S.base.left S.leftFiber
local notation "R" => Instance.fullModel S.base.right S.rightFiber

theorem generatedFamilyMap_identity_type (hΓ : CtxDeriv.{u+1} Γ γ)
    (hA : TyDeriv.{u+1} Γ γ A a)
    (hx : TmDeriv.{u+1} Γ γ A a x ξ) (hy : TmDeriv.{u+1} Γ γ A a y η) :
    generatedFamilyMap S hΓ (.identity hA hx hy) =
      identityMap (generatedFamilyMap S hΓ hA) (ξ L).down (η L).down ≫
        eqToHom (by rw [generatedFamilyMap_term_commutes S hΓ hA hx,
          generatedFamilyMap_term_commutes S hΓ hA hy]; rfl) :=
  Family.identity_relabel (a M) (ξ M) (η M)
    ((leftSignatureMap S).generated_ctx hΓ) ((rightSignatureMap S).generated_ctx hΓ)
    ((leftSignatureMap S).generated_ty hA).2 ((rightSignatureMap S).generated_ty hA).2
    ((leftSignatureMap S).generated_tm hx).2 ((rightSignatureMap S).generated_tm hx).2
    ((leftSignatureMap S).generated_tm hy).2 ((rightSignatureMap S).generated_tm hy).2
    ((leftSignatureMap S).generated_ty (.identity hA hx hy)).2
    ((rightSignatureMap S).generated_ty (.identity hA hx hy)).2

/-- The formula applies to every supplied identity arrow, retaining its image
before the explicit endpoint comparison transports it. -/
theorem generatedFamilyMap_identity_type_arrow (hΓ : CtxDeriv.{u+1} Γ γ)
    (hA : TyDeriv.{u+1} Γ γ A a)
    (hx : TmDeriv.{u+1} Γ γ A a x ξ) (hy : TmDeriv.{u+1} Γ γ A a y η)
    (c : (show Grpd.{u,u} from γ L)) (p : (ξ L).down.obj c ⟶ (η L).down.obj c) :
    ((generatedFamilyMap S hΓ (.identity hA hx hy)).app c).obj (Discrete.mk p) =
      ((eqToHom (show identityFamily _
        ((ξ L).down.familyImage (generatedFamilyMap S hΓ hA))
        ((η L).down.familyImage (generatedFamilyMap S hΓ hA)) =
        generatedContextMap S hΓ ⋙ identityFamily _ (ξ R).down (η R).down by
          rw [generatedFamilyMap_term_commutes S hΓ hA hx, generatedFamilyMap_term_commutes S hΓ hA hy]
          rfl)).app c).obj
        (Discrete.mk (((generatedFamilyMap S hΓ hA).app c).map p)) := by
  rw [generatedFamilyMap_identity_type]
  rfl

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
