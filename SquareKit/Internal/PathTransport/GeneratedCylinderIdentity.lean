import SquareKit.Internal.PathTransport.GeneratedCylinderCoherence

/-! The selected generated comparison preserves identity primitive squares. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Grpd.{u,u}} (F : C ⥤ D) (P : C ⥤ Type u)

theorem generatedEndpointIso_refl (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedEndpointIso F P (Iso.refl F) hΓ = Iso.refl _ := by
  let : (projectionSignature F P).base.map.IsEquivalence :=
    inferInstanceAs (projection F).IsEquivalence
  let := generatedContextMap_equivalence (projectionSignature F P)
    (fun _ => Function.bijective_id) hΓ
  unfold generatedEndpointIso
  apply selectedLift_unique
  ext x
  simp

theorem contextComparison_formula {G : C ⥤ D} (η : F ≅ G)
    (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q)
    (h : α ≫ whiskerRight η.hom Q = β) (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    contextComparison F P η Q α β h hΓ =
      (eqToIso (generatedInclusion_evaluation F P Q α hΓ)).symm ≪≫
        generatedComparison F P η Q α hΓ ≪≫
        eqToIso (generatedEndpoint_evaluation F P η Q α hΓ) ≪≫
        eqToIso (show generatedContextMap (Signature.mk (Context.mk C D G) P Q
          (α ≫ whiskerRight η.hom Q)) hΓ =
          generatedContextMap (Signature.mk (Context.mk C D G) P Q β) hΓ by cases h; rfl) := by
  cases h
  simp [contextComparison]

theorem contextComparison_refl (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q)
    (h : α ≫ whiskerRight (Iso.refl F).hom Q = α)
    (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    contextComparison F P (Iso.refl F) Q α α h hΓ = Iso.refl _ := by
  rw [contextComparison_formula]
  simp only [generatedComparison, generatedEndpointIso_refl]
  ext x
  simp

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
