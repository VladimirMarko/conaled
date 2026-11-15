import SquareKit.Internal.PathTransport.ComparisonCompositionRelations

/-! The horizontal signature has the same direct endpoint interpretations.
Generated endpoint comparisons therefore come from existing signature maps. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

theorem Signature.middleModel (S T : Signature.{u})
    (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber) :
    Instance.fullModel S.base.right S.rightFiber = Instance.fullModel T.base.left T.leftFiber := by
  cases S; cases T; rename_i baseS leftS rightS mapS baseT leftT rightT mapT
  cases baseS; cases baseT; dsimp at h; cases h
  dsimp at hB; cases eq_of_heq hB; rfl

theorem Signature.horizontal_leftModel (S T : Signature.{u})
    (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber) :
    Instance.fullModel (S.horizontal T h hB).base.left (S.horizontal T h hB).leftFiber =
      Instance.fullModel S.base.left S.leftFiber := by
  cases S; cases T; rename_i baseS leftS rightS mapS baseT leftT rightT mapT
  cases baseS; cases baseT; dsimp at h; cases h
  dsimp at hB; cases eq_of_heq hB; rfl

theorem Signature.horizontal_rightModel (S T : Signature.{u})
    (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber) :
    Instance.fullModel (S.horizontal T h hB).base.right (S.horizontal T h hB).rightFiber =
      Instance.fullModel T.base.right T.rightFiber := by
  cases S; cases T; rename_i baseS leftS rightS mapS baseT leftT rightT mapT
  cases baseS; cases baseT; dsimp at h; cases h
  dsimp at hB; cases eq_of_heq hB; rfl

private theorem code_heq {α : Sort*} {F : α → Sort*} (x : ∀ a, F a) {a b : α} (h : a = b) :
    HEq (x a) (x b) := by cases h; rfl

variable (S T : Signature.{u}) (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber)

include h hB

theorem generated_middle_context (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    (γ (fullModel S)).right = (γ (fullModel T)).left := by
  apply ((rightSignatureMap S).generatedCtx hΓ).trans
  apply Eq.trans _ ((leftSignatureMap T).generatedCtx hΓ).symm
  exact eq_of_heq (code_heq γ (S.middleModel T h hB))

theorem generated_middle_family (hA : Typed.TyDeriv.{u+1} Γ γ A a) :
    HEq (a (fullModel S)).right (a (fullModel T)).left :=
  ((rightSignatureMap S).generatedTy hA).2.trans
    ((code_heq a (S.middleModel T h hB)).trans ((leftSignatureMap T).generatedTy hA).2.symm)

theorem generated_middle_section (hx : Typed.TmDeriv.{u+1} Γ γ A a t x) :
    HEq (ULift.up.{u+1} (x (fullModel S)).right) (ULift.up.{u+1} (x (fullModel T)).left) :=
  ((rightSignatureMap S).generatedTm hx).2.trans
    ((code_heq x (S.middleModel T h hB)).trans ((leftSignatureMap T).generatedTm hx).2.symm)

theorem generated_left_section (hx : Typed.TmDeriv.{u+1} Γ γ A a t x) :
    HEq (ULift.up.{u+1} (x (fullModel S)).left)
      (ULift.up.{u+1} (x (fullModel (S.horizontal T h hB))).left) :=
  ((leftSignatureMap S).generatedTm hx).2.trans
    ((code_heq x (S.horizontal_leftModel T h hB).symm).trans
      ((leftSignatureMap (S.horizontal T h hB)).generatedTm hx).2.symm)

theorem generated_right_section (hx : Typed.TmDeriv.{u+1} Γ γ A a t x) :
    HEq (ULift.up.{u+1} (x (fullModel T)).right)
      (ULift.up.{u+1} (x (fullModel (S.horizontal T h hB))).right) :=
  ((rightSignatureMap T).generatedTm hx).2.trans
    ((code_heq x (S.horizontal_rightModel T h hB).symm).trans
      ((rightSignatureMap (S.horizontal T h hB)).generatedTm hx).2.symm)

theorem generated_left_substitution (hx : Typed.SubDeriv.{u+1} Δ δ Γ γ σ x) :
    HEq (ULift.up.{u+1} (x (fullModel S)).left)
      (ULift.up.{u+1} (x (fullModel (S.horizontal T h hB))).left) :=
  ((leftSignatureMap S).generatedSub hx).2.2.trans
    ((code_heq x (S.horizontal_leftModel T h hB).symm).trans
      ((leftSignatureMap (S.horizontal T h hB)).generatedSub hx).2.2.symm)

theorem generated_right_substitution (hx : Typed.SubDeriv.{u+1} Δ δ Γ γ σ x) :
    HEq (ULift.up.{u+1} (x (fullModel T)).right)
      (ULift.up.{u+1} (x (fullModel (S.horizontal T h hB))).right) :=
  ((rightSignatureMap T).generatedSub hx).2.2.trans
    ((code_heq x (S.horizontal_rightModel T h hB).symm).trans
      ((rightSignatureMap (S.horizontal T h hB)).generatedSub hx).2.2.symm)

theorem generated_middle_substitution (hx : Typed.SubDeriv.{u+1} Δ δ Γ γ σ x) :
    HEq (ULift.up.{u+1} (x (fullModel S)).right) (ULift.up.{u+1} (x (fullModel T)).left) :=
  ((rightSignatureMap S).generatedSub hx).2.2.trans
    ((code_heq x (S.middleModel T h hB)).trans ((leftSignatureMap T).generatedSub hx).2.2.symm)

omit h hB in
private theorem section_down_heq {C D : Grpd.{u,u}} (hC : C = D)
    {A : C ⥤ Grpd.{u,u}} {B : D ⥤ Grpd.{u,u}} (hA : HEq A B)
    {s : GroupoidModel.Section A} {t : GroupoidModel.Section B}
    (hs : HEq (ULift.up.{u+1} s) (ULift.up.{u+1} t)) : HEq s t := by
  cases hC; cases eq_of_heq hA
  exact heq_of_eq (congrArg ULift.down (eq_of_heq hs))

theorem generated_section_composes (hx : Typed.TmDeriv.{u+1} Γ γ A a t x)
    (ha : (a (fullModel S)).Composes (a (fullModel T)) (a (fullModel (S.horizontal T h hB)))) :
    (x (fullModel S)).Composes (x (fullModel T)) (x (fullModel (S.horizontal T h hB))) :=
  Section.Composes.of_endpoints ha _ _ _
    (section_down_heq ha.context.middle ha.middle (generated_middle_section S T h hB hx))
    (section_down_heq ha.context.left ha.endpoints.1 (generated_left_section S T h hB hx))
    (section_down_heq ha.context.right ha.endpoints.2 (generated_right_section S T h hB hx))

omit h hB in
private theorem substitution_down_heq {C C' D D' : Grpd.{u,u}} (hC : C = C') (hD : D = D')
    {F : D ⥤ C} {G : D' ⥤ C'} (hs : HEq (ULift.up.{u+1} F) (ULift.up.{u+1} G)) : HEq F G := by
  cases hC; cases hD
  exact heq_of_eq (congrArg ULift.down (eq_of_heq hs))

theorem generated_substitution_composes (hx : Typed.SubDeriv.{u+1} Δ δ Γ γ σ x)
    (hΓ : (γ (fullModel S)).Composes (γ (fullModel T)) (γ (fullModel (S.horizontal T h hB))))
    (hΔ : (δ (fullModel S)).Composes (δ (fullModel T)) (δ (fullModel (S.horizontal T h hB)))) :
    (x (fullModel S)).Composes (x (fullModel T)) (x (fullModel (S.horizontal T h hB))) :=
  Substitution.Composes.of_endpoints hΓ hΔ _ _ _
    (substitution_down_heq hΓ.middle hΔ.middle (generated_middle_substitution S T h hB hx))
    (substitution_down_heq hΓ.left hΔ.left (generated_left_substitution S T h hB hx))
    (substitution_down_heq hΓ.right hΔ.right (generated_right_substitution S T h hB hx))

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
