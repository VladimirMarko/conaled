import SquareKit.Internal.PathTransport.AlignedSignatureComparisonLaws

/-! Normalize a selected recovery triangle before specializing its generated models. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
variable {C D E : Type u} [Groupoid.{v} C] [Groupoid.{v} D] [Groupoid.{v} E]
variable (P : C ⥤ Type w) (Q : D ⥤ Type w) (R : E ⥤ Type w)
variable {F G : C ⥤ D} (η : F ≅ G) (K₁ K₂ : D ⥤ E)
variable (θ : G ⋙ K₁ ≅ G ⋙ K₂)
variable (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q)
variable (κ₁ : Q ⟶ K₁ ⋙ R) (κ₂ : Q ⟶ K₂ ⋙ R)
variable (hη : α ≫ whiskerRight η.hom Q = β)
variable (h₁ : (α ≫ whiskerLeft F κ₁) ≫ whiskerRight (isoWhiskerRight η K₁).hom R = β ≫ whiskerLeft G κ₁)
variable (h₂ : (α ≫ whiskerLeft F κ₂) ≫ whiskerRight (isoWhiskerRight η K₂).hom R = β ≫ whiskerLeft G κ₂)
variable (hθ : (β ≫ whiskerLeft G κ₁) ≫ whiskerRight θ.hom R = β ≫ whiskerLeft G κ₂)
variable (hf : F ⋙ K₁ = F ⋙ K₂) (hα : HEq (α ≫ whiskerLeft F κ₁) (α ≫ whiskerLeft F κ₂))
variable (hc : isoWhiskerRight η K₁ ≪≫ θ = eqToIso hf ≪≫ isoWhiskerRight η K₂)

include h₁ h₂ hc in
theorem alignedRecovery_square (hΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ) :
    isoWhiskerRight (alignedContextComparison η P Q α β hη hΓ)
      (generatedContextMap (alignedUniverseSignature K₁ Q R κ₁) hΓ) ≪≫
      (eqToIso (alignedGenerated_comp P Q K₁ R β κ₁ hΓ) ≪≫
        alignedContextComparison θ P R (β ≫ whiskerLeft G κ₁) (β ≫ whiskerLeft G κ₂) hθ hΓ ≪≫
        (eqToIso (alignedGenerated_comp P Q K₂ R β κ₂ hΓ)).symm) =
    (eqToIso (alignedGenerated_comp P Q K₁ R α κ₁ hΓ) ≪≫
      eqToIso (alignedGenerated_eq P R hf hα hΓ) ≪≫
      (eqToIso (alignedGenerated_comp P Q K₂ R α κ₂ hΓ)).symm) ≪≫
      isoWhiskerRight (alignedContextComparison η P Q α β hη hΓ)
        (generatedContextMap (alignedUniverseSignature K₂ Q R κ₂) hΓ) := by
  have h := alignedContextComparison_cocycle_presentations P R
    (isoWhiskerRight η K₁) θ (isoWhiskerRight η K₂)
    (α ≫ whiskerLeft F κ₁) (β ≫ whiskerLeft G κ₁)
    (β ≫ whiskerLeft G κ₁) (β ≫ whiskerLeft G κ₂)
    (α ≫ whiskerLeft F κ₂) (β ≫ whiskerLeft G κ₂)
    rfl hf rfl hα HEq.rfl HEq.rfl
    (by simpa only [eqToIso_refl, Iso.trans_refl, Iso.refl_trans, Iso.refl_symm] using hc) h₁ hθ h₂ hΓ
  rw [alignedContextComparison_postcompose P Q K₁ R η α β κ₁ hη h₁ hΓ,
    alignedContextComparison_postcompose P Q K₂ R η α β κ₂ hη h₂ hΓ] at h
  have hn := congrArg (fun i => eqToIso (alignedGenerated_comp P Q K₁ R α κ₁ hΓ) ≪≫ i ≪≫
    (eqToIso (alignedGenerated_comp P Q K₂ R β κ₂ hΓ)).symm) h
  simpa [Iso.trans_assoc] using hn

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
