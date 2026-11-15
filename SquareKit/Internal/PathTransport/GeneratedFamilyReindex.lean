import SquareKit.Internal.PathTransport.GeneratedComparisonRestriction

/-! Whole generated family maps preserve reindexing, with explicit endpoint transport. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

theorem Family.reindex_map_heq {Γ Δ : Context.{u}} (A : Family Γ)
    (σ : Substitution Δ Γ) {C D E F : Grpd.{u,u}}
    (hC : Γ.left = C) (hD : Γ.right = D) (hE : Δ.left = E) (hF : Δ.right = F)
    {B : C ⥤ Grpd.{u,u}} {Q : D ⥤ Grpd.{u,u}}
    (hB : HEq A.left B) (hQ : HEq A.right Q)
    {s : E ⥤ C} {t : F ⥤ D} (hs : HEq (ULift.up.{u+1} σ.left) (ULift.up.{u+1} s))
    (ht : HEq (ULift.up.{u+1} σ.right) (ULift.up.{u+1} t))
    (hc : s ⋙ Γ.relabel hC hD = Δ.relabel hE hF ⋙ t) :
    HEq (A.reindex σ).map
      (whiskerLeft s (A.relabelMap hC hD hB hQ) ≫
        eqToHom (congrArg (· ⋙ Q) hc)) := by
  subst C; subst D; subst E; subst F
  cases eq_of_heq hB
  cases eq_of_heq hQ
  cases congrArg ULift.down (eq_of_heq hs)
  cases congrArg ULift.down (eq_of_heq ht)
  rfl

variable (S : Signature.{u})
local notation "M" => fullModel S
local notation "L" => Instance.fullModel S.base.left S.leftFiber
local notation "R" => Instance.fullModel S.base.right S.rightFiber

theorem generatedFamilyMap_sub (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hΔ : Typed.CtxDeriv.{u+1} Δ δ) (hA : Typed.TyDeriv.{u+1} Γ γ A a)
    (hs : Typed.SubDeriv.{u+1} Δ δ Γ γ σ s) :
    generatedFamilyMap S hΔ (.sub hA hs) =
      whiskerLeft (s L).down (generatedFamilyMap S hΓ hA) ≫
        eqToHom (congrArg (· ⋙ (show (show Grpd.{u,u} from γ R) ⥤ Grpd.{u,u} from a R))
          (generatedSubstitution_commutes S hΓ hΔ hs)) := by
  apply eq_of_heq
  apply (Family.relabelMap_heq _ _ _ _ _).trans
  exact Family.reindex_map_heq (a M) (s M)
    ((leftSignatureMap S).generatedCtx hΓ) ((rightSignatureMap S).generatedCtx hΓ)
    ((leftSignatureMap S).generatedCtx hΔ) ((rightSignatureMap S).generatedCtx hΔ)
    ((leftSignatureMap S).generatedTy hA).2 ((rightSignatureMap S).generatedTy hA).2
    (by exact ((leftSignatureMap S).generatedSub hs).2.2)
    (by exact ((rightSignatureMap S).generatedSub hs).2.2)
    (generatedSubstitution_commutes S hΓ hΔ hs)

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
