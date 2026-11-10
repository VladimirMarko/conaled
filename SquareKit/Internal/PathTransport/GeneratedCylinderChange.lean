import SquareKit.Internal.PathTransport.SignatureCylinderChange
import SquareKit.Internal.PathTransport.GeneratedCylinderIdentity

/-! Generated maps retain the cylinder change-of-reference equations. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Grpd.{u,u}} {F G H : C ⥤ D} (η : F ≅ G) (P : C ⥤ Type u)

theorem generatedChange_inclusion  (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (inclusionSignature G P) hΓ ⋙ generatedContextMap (changeReferenceSignature η P) hΓ =
      generatedContextMap (endpointSignature F P η) hΓ := by
  have hc := Context.relabel_composition
    (GeneratedComposition.generatedCtx (inclusionSignature G P) (changeReferenceSignature η P) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  exact eq_of_heq ((heq_of_eq hc).trans (generatedContextMap_heq (inclusion_changeReference_signature η P) hΓ))

theorem generatedChange_endpoint (θ : G ≅ H) (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (endpointSignature G P θ) hΓ ⋙ generatedContextMap (changeReferenceSignature η P) hΓ =
      generatedContextMap (endpointSignature F P (η ≪≫ θ)) hΓ := by
  have hc := Context.relabel_composition
    (GeneratedComposition.generatedCtx (endpointSignature G P θ) (changeReferenceSignature η P) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  exact eq_of_heq ((heq_of_eq hc).trans (generatedContextMap_heq (endpoint_changeReference_signature η P θ) hΓ))

theorem generatedChange_projection  (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (changeReferenceSignature η P) hΓ ⋙ generatedContextMap (projectionSignature F P) hΓ =
      generatedContextMap (projectionSignature G P) hΓ := by
  have hc := Context.relabel_composition
    (GeneratedComposition.generatedCtx (changeReferenceSignature η P) (projectionSignature F P) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  exact eq_of_heq ((heq_of_eq hc).trans (generatedContextMap_heq (changeReference_projection_signature η P) hΓ))

theorem generatedChange_evaluation (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q) (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (changeReferenceSignature η P) hΓ ⋙ generatedContextMap (evaluationSignature F P Q α) hΓ =
      generatedContextMap (evaluationSignature G P Q (α ≫ whiskerRight η.hom Q)) hΓ := by
  have hc := Context.relabel_composition
    (GeneratedComposition.generatedCtx (changeReferenceSignature η P) (evaluationSignature F P Q α) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  exact eq_of_heq ((heq_of_eq hc).trans (generatedContextMap_heq (changeReference_evaluation_signature η P Q α) hΓ))

theorem generatedEndpointIso_trans (θ : G ≅ H) (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedEndpointIso F P (η ≪≫ θ) hΓ =
      generatedEndpointIso F P η hΓ ≪≫
        (eqToIso (generatedChange_inclusion η P hΓ)).symm ≪≫
        isoWhiskerRight (generatedEndpointIso G P θ hΓ)
          (generatedContextMap (changeReferenceSignature η P) hΓ) ≪≫
        eqToIso (generatedChange_endpoint η P θ hΓ) := by
  let : (projectionSignature F P).base.map.IsEquivalence :=
    inferInstanceAs (projection F).IsEquivalence
  let := generatedContextMap_equivalence (projectionSignature F P)
    (fun _ => Function.bijective_id) hΓ
  let : (projectionSignature G P).base.map.IsEquivalence :=
    inferInstanceAs (projection G).IsEquivalence
  let := generatedContextMap_equivalence (projectionSignature G P)
    (fun _ => Function.bijective_id) hΓ
  change selectedSectionIso _ _ _ _ _ = _
  rw [selectedSectionIso_trans _ _ (generatedContextMap (endpointSignature F P η) hΓ) _
    _ (generatedEndpoint_projection F P η hΓ)]
  rw [selectedSectionIso_transport _ (generatedContextMap (projectionSignature G P) hΓ)
    _ _ (generatedContextMap (inclusionSignature G P) hΓ)
    (generatedContextMap (endpointSignature G P θ) hΓ) _ _
    (generatedInclusion_projection G P hΓ) (generatedEndpoint_projection G P θ hΓ)
    (generatedContextMap (changeReferenceSignature η P) hΓ)
    (generatedChange_projection η P hΓ) (generatedChange_inclusion η P hΓ)
    (generatedChange_endpoint η P θ hΓ)]
  rfl

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
