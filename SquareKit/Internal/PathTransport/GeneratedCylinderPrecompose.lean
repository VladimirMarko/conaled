import SquareKit.Internal.PathTransport.SignatureCylinderPrecompose
import SquareKit.Internal.PathTransport.GeneratedCylinderPostcompose

/-! Selected generated comparisons under precomposition. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {B C D : Grpd.{u,u}} (K : B ⥤ C) (F : C ⥤ D)
variable (O : B ⥤ Type u) (P : C ⥤ Type u) (κ : O ⟶ K ⋙ P)

theorem generatedPrecompose_inclusion  (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (inclusionSignature (K ⋙ F) O) hΓ ⋙ generatedContextMap (precomposeSignature K F O P κ) hΓ =
      generatedContextMap (Signature.mk (Context.mk B C K) O P κ) hΓ ⋙ generatedContextMap (inclusionSignature F P) hΓ := by
  have hc := Context.relabel_composition
    (GeneratedComposition.generatedCtx (inclusionSignature (K ⋙ F) O) (precomposeSignature K F O P κ) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  have hd := Context.relabel_composition
    (GeneratedComposition.generatedCtx (Signature.mk (Context.mk B C K) O P κ) (inclusionSignature F P) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  exact eq_of_heq ((heq_of_eq hc).trans
    ((generatedContextMap_heq (inclusion_precompose_signature K F O P κ) hΓ).trans (heq_of_eq hd.symm)))

theorem generatedPrecompose_endpoint {G : C ⥤ D} (η : F ≅ G) (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (endpointSignature (K ⋙ F) O (isoWhiskerLeft K η)) hΓ ⋙ generatedContextMap (precomposeSignature K F O P κ) hΓ =
      generatedContextMap (Signature.mk (Context.mk B C K) O P κ) hΓ ⋙ generatedContextMap (endpointSignature F P η) hΓ := by
  have hc := Context.relabel_composition
    (GeneratedComposition.generatedCtx (endpointSignature (K ⋙ F) O (isoWhiskerLeft K η)) (precomposeSignature K F O P κ) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  have hd := Context.relabel_composition
    (GeneratedComposition.generatedCtx (Signature.mk (Context.mk B C K) O P κ) (endpointSignature F P η) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  exact eq_of_heq ((heq_of_eq hc).trans
    ((generatedContextMap_heq (endpoint_precompose_signature K F O P κ η) hΓ).trans (heq_of_eq hd.symm)))

theorem generatedPrecompose_projection  (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (precomposeSignature K F O P κ) hΓ ⋙ generatedContextMap (projectionSignature F P) hΓ =
      generatedContextMap (projectionSignature (K ⋙ F) O) hΓ ⋙ generatedContextMap (Signature.mk (Context.mk B C K) O P κ) hΓ := by
  have hc := Context.relabel_composition
    (GeneratedComposition.generatedCtx (precomposeSignature K F O P κ) (projectionSignature F P) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  have hd := Context.relabel_composition
    (GeneratedComposition.generatedCtx (projectionSignature (K ⋙ F) O) (Signature.mk (Context.mk B C K) O P κ) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  exact eq_of_heq ((heq_of_eq hc).trans
    ((generatedContextMap_heq (precompose_projection_signature K F O P κ) hΓ).trans (heq_of_eq hd.symm)))

theorem generatedEndpointIso_precompose {G : C ⥤ D} (η : F ≅ G)
    (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    isoWhiskerLeft (generatedContextMap (Signature.mk (Context.mk B C K) O P κ) hΓ)
        (generatedEndpointIso F P η hΓ) ≪≫
      (eqToIso (generatedPrecompose_endpoint K F O P κ η hΓ)).symm =
    (eqToIso (generatedPrecompose_inclusion K F O P κ hΓ)).symm ≪≫
      isoWhiskerRight (generatedEndpointIso (K ⋙ F) O (isoWhiskerLeft K η) hΓ)
        (generatedContextMap (precomposeSignature K F O P κ) hΓ) := by
  let : (projectionSignature F P).base.map.IsEquivalence :=
    inferInstanceAs (projection F).IsEquivalence
  let := generatedContextMap_equivalence (projectionSignature F P)
    (fun _ => Function.bijective_id) hΓ
  let : (projectionSignature (K ⋙ F) O).base.map.IsEquivalence :=
    inferInstanceAs (projection (K ⋙ F)).IsEquivalence
  let := generatedContextMap_equivalence (projectionSignature (K ⋙ F) O)
    (fun _ => Function.bijective_id) hΓ
  exact selectedSectionIso_square
    (generatedContextMap (projectionSignature F P) hΓ)
    (generatedContextMap (projectionSignature (K ⋙ F) O) hΓ) _ _ _ _ _ _ _ _
    (generatedContextMap (Signature.mk (Context.mk B C K) O P κ) hΓ)
    (generatedContextMap (precomposeSignature K F O P κ) hΓ)
    (generatedPrecompose_projection K F O P κ hΓ)
    (generatedPrecompose_inclusion K F O P κ hΓ).symm
    (generatedPrecompose_endpoint K F O P κ η hΓ).symm

variable (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q)
theorem generatedPrecompose_evaluation (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (precomposeSignature K F O P κ) hΓ ⋙ generatedContextMap (evaluationSignature F P Q α) hΓ =
      generatedContextMap (evaluationSignature (K ⋙ F) O Q (κ ≫ whiskerLeft K α)) hΓ := by
  have hc := Context.relabel_composition
    (GeneratedComposition.generatedCtx (precomposeSignature K F O P κ) (evaluationSignature F P Q α) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  exact eq_of_heq ((heq_of_eq hc).trans
    (generatedContextMap_heq (precompose_evaluation_signature K F O P κ Q α) hΓ))

theorem contextComparison_precompose {G : C ⥤ D} (η : F ≅ G)
    (β : P ⟶ G ⋙ Q) (h : α ≫ whiskerRight η.hom Q = β)
    (hk : (κ ≫ whiskerLeft K α) ≫ whiskerRight (isoWhiskerLeft K η).hom Q =
      κ ≫ whiskerLeft K β)
    (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    isoWhiskerLeft (generatedContextMap (Signature.mk (Context.mk B C K) O P κ) hΓ)
        (contextComparison F P η Q α β h hΓ) ≪≫
      eqToIso (generatedPostcompose_signature K G O P Q κ β hΓ) =
    eqToIso (generatedPostcompose_signature K F O P Q κ α hΓ) ≪≫
      contextComparison (K ⋙ F) O (isoWhiskerLeft K η) Q
        (κ ≫ whiskerLeft K α) (κ ≫ whiskerLeft K β) hk hΓ := by
  cases h
  rw [contextComparison_formula, contextComparison_formula]
  ext x
  have hh := congrArg (fun z => (generatedContextMap (evaluationSignature F P Q α) hΓ).map
    (z.hom.app x)) (generatedEndpointIso_precompose K F O P κ η hΓ)
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Iso.symm_hom, eqToIso.inv, eqToHom_app, Functor.map_comp, eqToHom_map] at hh
  have hn := (eqToHom (generatedPrecompose_evaluation K F O P κ Q α hΓ)).naturality
    ((generatedEndpointIso (K ⋙ F) O (isoWhiskerLeft K η) hΓ).hom.app x)
  have hn' := congrArg (fun f => f ≫ eqToHom (congrArg
    (fun J => J.obj ((generatedContextMap
      (endpointSignature (K ⋙ F) O (isoWhiskerLeft K η)) hΓ).obj x))
      (generatedPrecompose_evaluation K F O P κ Q α hΓ).symm)) hn
  simp only [Functor.comp_map, eqToHom_app, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id] at hn'
  rw [hn'] at hh
  simp only [generatedComparison, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    eqToIso.hom, Iso.symm_hom, eqToIso.inv, eqToHom_app, Category.assoc]
  have ha := congrArg (fun f => f ≫ eqToHom (congrArg
    (fun J => (generatedContextMap (evaluationSignature F P Q α) hΓ).obj (J.obj x))
      (generatedPrecompose_endpoint K F O P κ η hΓ))) hh
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at ha
  rw [ha]
  simp [Category.assoc]

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
