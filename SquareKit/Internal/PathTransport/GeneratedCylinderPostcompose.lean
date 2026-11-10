import SquareKit.Internal.PathTransport.SignatureCylinderPostcompose
import SquareKit.Internal.PathTransport.GeneratedCylinderComposition

/-! Selected generated comparisons under postcomposition. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D E : Grpd.{u,u}} (F : C ⥤ D) (K : D ⥤ E) (P : C ⥤ Type u)

theorem generatedPostcompose_inclusion  (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (inclusionSignature F P) hΓ ⋙ generatedContextMap (postcomposeSignature F K P) hΓ =
      generatedContextMap (inclusionSignature (F ⋙ K) P) hΓ := by
  have hc := Context.relabel_composition
    (GeneratedComposition.generatedCtx (inclusionSignature F P) (postcomposeSignature F K P) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  exact eq_of_heq ((heq_of_eq hc).trans (generatedContextMap_heq (inclusion_postcompose_signature F K P) hΓ))

theorem generatedPostcompose_endpoint {G : C ⥤ D} (η : F ≅ G) (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (endpointSignature F P η) hΓ ⋙ generatedContextMap (postcomposeSignature F K P) hΓ =
      generatedContextMap (endpointSignature (F ⋙ K) P (isoWhiskerRight η K)) hΓ := by
  have hc := Context.relabel_composition
    (GeneratedComposition.generatedCtx (endpointSignature F P η) (postcomposeSignature F K P) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  exact eq_of_heq ((heq_of_eq hc).trans (generatedContextMap_heq (endpoint_postcompose_signature F K P η) hΓ))

theorem generatedPostcompose_projection  (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (postcomposeSignature F K P) hΓ ⋙ generatedContextMap (projectionSignature (F ⋙ K) P) hΓ =
      generatedContextMap (projectionSignature F P) hΓ := by
  have hc := Context.relabel_composition
    (GeneratedComposition.generatedCtx (postcomposeSignature F K P) (projectionSignature (F ⋙ K) P) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  exact eq_of_heq ((heq_of_eq hc).trans (generatedContextMap_heq (postcompose_projection_signature F K P) hΓ))

theorem generatedEndpointIso_postcompose {G : C ⥤ D} (η : F ≅ G)
    (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedEndpointIso (F ⋙ K) P (isoWhiskerRight η K) hΓ =
      (eqToIso (generatedPostcompose_inclusion F K P hΓ)).symm ≪≫
        isoWhiskerRight (generatedEndpointIso F P η hΓ)
          (generatedContextMap (postcomposeSignature F K P) hΓ) ≪≫
        eqToIso (generatedPostcompose_endpoint F K P η hΓ) := by
  let : (projectionSignature F P).base.map.IsEquivalence :=
    inferInstanceAs (projection F).IsEquivalence
  let := generatedContextMap_equivalence (projectionSignature F P)
    (fun _ => Function.bijective_id) hΓ
  let : (projectionSignature (F ⋙ K) P).base.map.IsEquivalence :=
    inferInstanceAs (projection (F ⋙ K)).IsEquivalence
  let := generatedContextMap_equivalence (projectionSignature (F ⋙ K) P)
    (fun _ => Function.bijective_id) hΓ
  exact selectedSectionIso_transport
    (generatedContextMap (projectionSignature (F ⋙ K) P) hΓ)
    (generatedContextMap (projectionSignature F P) hΓ) _ _ _ _ _ _ _ _
    (generatedContextMap (postcomposeSignature F K P) hΓ)
    (generatedPostcompose_projection F K P hΓ)
    (generatedPostcompose_inclusion F K P hΓ) (generatedPostcompose_endpoint F K P η hΓ)

variable (Q : D ⥤ Type u) (R : E ⥤ Type u) (α : P ⟶ F ⋙ Q) (κ : Q ⟶ K ⋙ R)
theorem generatedPostcompose_evaluation (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (postcomposeSignature F K P) hΓ ⋙ generatedContextMap (evaluationSignature (F ⋙ K) P R (α ≫ whiskerLeft F κ)) hΓ =
      generatedContextMap (evaluationSignature F P Q α) hΓ ⋙ generatedContextMap (Signature.mk (Context.mk D E K) Q R κ) hΓ := by
  have hc := Context.relabel_composition
    (GeneratedComposition.generatedCtx (postcomposeSignature F K P) (evaluationSignature (F ⋙ K) P R (α ≫ whiskerLeft F κ)) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  have hd := Context.relabel_composition
    (GeneratedComposition.generatedCtx (evaluationSignature F P Q α) (Signature.mk (Context.mk D E K) Q R κ) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  exact eq_of_heq ((heq_of_eq hc).trans
    ((generatedContextMap_heq (postcompose_evaluation_signature F K P Q R α κ) hΓ).trans
      (heq_of_eq hd.symm)))

theorem generatedPostcompose_signature (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (Signature.mk (Context.mk C D F) P Q α) hΓ ⋙
      generatedContextMap (Signature.mk (Context.mk D E K) Q R κ) hΓ =
    generatedContextMap (Signature.mk (Context.mk C E (F ⋙ K)) P R
      (α ≫ whiskerLeft F κ)) hΓ :=
  Context.relabel_composition
    (GeneratedComposition.generatedCtx (Signature.mk (Context.mk C D F) P Q α)
      (Signature.mk (Context.mk D E K) Q R κ) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)

theorem contextComparison_postcompose {G : C ⥤ D} (η : F ≅ G)
    (β : P ⟶ G ⋙ Q) (h : α ≫ whiskerRight η.hom Q = β)
    (hk : (α ≫ whiskerLeft F κ) ≫ whiskerRight (isoWhiskerRight η K).hom R =
      β ≫ whiskerLeft G κ)
    (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    contextComparison (F ⋙ K) P (isoWhiskerRight η K) R
      (α ≫ whiskerLeft F κ) (β ≫ whiskerLeft G κ) hk hΓ =
      (eqToIso (generatedPostcompose_signature F K P Q R α κ hΓ)).symm ≪≫
        isoWhiskerRight (contextComparison F P η Q α β h hΓ)
          (generatedContextMap (Signature.mk (Context.mk D E K) Q R κ) hΓ) ≪≫
        eqToIso (generatedPostcompose_signature G K P Q R β κ hΓ) := by
  cases h
  rw [contextComparison_formula, contextComparison_formula]
  simp only [generatedComparison, generatedEndpointIso_postcompose]
  ext x
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    eqToIso.hom, Iso.symm_hom, eqToIso.inv, eqToHom_app, Functor.map_comp,
    Category.assoc, eqToHom_map]
  have hn := (eqToHom (generatedPostcompose_evaluation F K P Q R α κ hΓ)).naturality
    ((generatedEndpointIso F P η hΓ).hom.app x)
  have hn' := congrArg (fun f => f ≫ eqToHom (congrArg
    (fun J => J.obj ((generatedContextMap (endpointSignature F P η) hΓ).obj x))
      (generatedPostcompose_evaluation F K P Q R α κ hΓ).symm)) hn
  simp only [Functor.comp_map, eqToHom_app, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id] at hn'
  rw [hn']
  simp [Category.assoc]

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
