import SquareKit.Internal.PathTransport.ComparisonComposition

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory Typed
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

theorem Family.relabel_totalMap_heq {Γ : Context.{u}} (A : Family Γ)
    {C D : Grpd.{u,u}} (hC : Γ.left = C) (hD : Γ.right = D)
    {B : C ⥤ Grpd.{u,u}} {E : D ⥤ Grpd.{u,u}}
    (hB : HEq A.left B) (hE : HEq A.right E) :
    HEq (totalMap (Γ.relabel hC hD) (A.relabelMap hC hD hB hE)) A.extend.map := by
  subst C; subst D
  cases eq_of_heq hB; cases eq_of_heq hE
  rfl

variable (S : Signature.{u})

@[simp] theorem generatedContextMap_empty :
    generatedContextMap S (CtxDeriv.empty : CtxDeriv [] emptyCode.{u+1}) = 𝟭 _ := rfl

/-- The extracted map of a generated extension is the actual comprehension
map of the extracted base and family comparisons. -/
theorem generatedContextMap_extend (hΓ : CtxDeriv.{u+1} Γ γ)
    (hA : TyDeriv.{u+1} Γ γ A a) :
    generatedContextMap S (.ext hΓ hA) =
      totalMap (generatedContextMap S hΓ) (generatedFamilyMap S hΓ hA) := by
  apply eq_of_heq
  apply (Context.relabel_heq _ _ _).trans
  exact ((a (fullModel S)).relabel_totalMap_heq
    ((leftSignatureMap S).generatedCtx hΓ) ((rightSignatureMap S).generatedCtx hΓ)
    ((leftSignatureMap S).generatedTy hA).2 ((rightSignatureMap S).generatedTy hA).2).symm

theorem Signature.baseFamily_relabel (S : Signature.{u}) (Γ : Context.{u})
    {C D : Grpd.{u,u}} (hC : Γ.left = C) (hD : Γ.right = D) :
    (S.baseFamily Γ).relabelMap hC hD
      (show HEq (S.baseFamily Γ).left (constant (Γ := C) S.base.left) from by cases hC; rfl)
      (show HEq (S.baseFamily Γ).right (constant (Γ := D) S.base.right) from by cases hD; rfl) =
      (show constant (Γ := C) S.base.left ⟶ Γ.relabel hC hD ⋙ constant S.base.right from
        { app := fun _ => S.base.map, naturality := fun {_ _} _ => rfl }) := by
  subst C; subst D
  rfl

theorem generatedFamilyMap_base (hΓ : CtxDeriv.{u+1} Γ γ) :
    generatedFamilyMap S hΓ (.base hΓ) =
      (show constant S.base.left ⟶ generatedContextMap S hΓ ⋙ constant S.base.right from
        { app := fun _ => S.base.map, naturality := fun {_ _} _ => rfl }) :=
  S.baseFamily_relabel (γ (fullModel S))
    ((leftSignatureMap S).generatedCtx hΓ) ((rightSignatureMap S).generatedCtx hΓ)

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
