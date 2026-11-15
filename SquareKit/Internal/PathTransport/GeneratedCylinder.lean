import SquareKit.Internal.PathTransport.SignatureCylinder
import SquareKit.Internal.PathTransport.GeneratedComparisonIdentity
import SquareKit.Internal.PathTransport.GeneratedComparisonCompositionMaps
import SquareKit.Internal.PathTransport.GeneratedEquivalenceMaps

/-! Selected generated cylinder comparisons. The same generated interpretation,
including contextual identity elimination, is used at each endpoint. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SignatureCylinder
variable {C D : Grpd.{u,u}} (F : C ⥤ D) (P : C ⥤ Type u)
variable {G : C ⥤ D} (η : F ≅ G)

theorem generatedInclusion_projection (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (inclusionSignature F P) hΓ ⋙
      generatedContextMap (projectionSignature F P) hΓ = 𝟭 _ := by
  have hc := Context.relabel_composition
    (GeneratedComposition.generatedCtx (inclusionSignature F P)
      (projectionSignature F P) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  change _ = generatedContextMap (Signature.diagonal C P) hΓ at hc
  rw [generatedContextMap_identity] at hc
  exact hc

theorem generatedEndpoint_projection (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (endpointSignature F P η) hΓ ⋙
      generatedContextMap (projectionSignature F P) hΓ = 𝟭 _ := by
  have hc := Context.relabel_composition
    (GeneratedComposition.generatedCtx (endpointSignature F P η)
      (projectionSignature F P) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  change _ = generatedContextMap (Signature.diagonal C P) hΓ at hc
  rw [generatedContextMap_identity] at hc
  exact hc

/-- The selected comparison is the unique lift of the identity through the
actual generated projection, which is an equivalence. -/
def generatedEndpointIso (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (inclusionSignature F P) hΓ ≅
      generatedContextMap (endpointSignature F P η) hΓ := by
  letI : (projectionSignature F P).base.map.IsEquivalence :=
    inferInstanceAs (projection F).IsEquivalence
  letI := generatedContextMap_equivalence (projectionSignature F P)
    (fun _ => Function.bijective_id) hΓ
  exact fullyFaithfulCancelRight (generatedContextMap (projectionSignature F P) hΓ)
    (eqToIso (generatedInclusion_projection F P hΓ) ≪≫
      (eqToIso (generatedEndpoint_projection F P η hΓ)).symm)

/-- Comparison at the target is induced by the cylinder's signature map;
no equivalence hypothesis is imposed on that map. -/
def generatedComparison (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q)
    (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (inclusionSignature F P) hΓ ⋙
        generatedContextMap (evaluationSignature F P Q α) hΓ ≅
      generatedContextMap (endpointSignature F P η) hΓ ⋙
        generatedContextMap (evaluationSignature F P Q α) hΓ :=
  isoWhiskerRight (generatedEndpointIso F P η hΓ)
    (generatedContextMap (evaluationSignature F P Q α) hΓ)

theorem generatedContextMap_heq {S T : Signature.{u}} (h : S = T)
    (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    HEq (generatedContextMap S hΓ) (generatedContextMap T hΓ) := by
  cases h
  rfl

theorem generatedInclusion_evaluation (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q)
    (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (inclusionSignature F P) hΓ ⋙
      generatedContextMap (evaluationSignature F P Q α) hΓ =
      generatedContextMap ⟨⟨C, D, F⟩, P, Q, α⟩ hΓ := by
  have hc := Context.relabel_composition
    (GeneratedComposition.generatedCtx (inclusionSignature F P)
      (evaluationSignature F P Q α) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  exact eq_of_heq ((heq_of_eq hc).trans
    (generatedContextMap_heq (inclusion_evaluation_signature F P Q α) hΓ))

theorem generatedEndpoint_evaluation (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q)
    (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap (endpointSignature F P η) hΓ ⋙
      generatedContextMap (evaluationSignature F P Q α) hΓ =
      generatedContextMap ⟨⟨C, D, G⟩, P, Q, α ≫ whiskerRight η.hom Q⟩ hΓ := by
  have hc := Context.relabel_composition
    (GeneratedComposition.generatedCtx (endpointSignature F P η)
      (evaluationSignature F P Q α) rfl HEq.rfl hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
    ((leftSignatureMap _).generatedCtx hΓ) ((rightSignatureMap _).generatedCtx hΓ)
  exact eq_of_heq ((heq_of_eq hc).trans
    (generatedContextMap_heq (endpoint_evaluation_signature F P Q α η) hΓ))

/-- A selected primitive square induces a natural isomorphism on every
supported generated context, with the original direct endpoint interpretations.
Only the auxiliary cylinder projection uses an equivalence. -/
def contextComparison (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q)
    (h : α ≫ whiskerRight η.hom Q = β) (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap ⟨⟨C, D, F⟩, P, Q, α⟩ hΓ ≅
      generatedContextMap ⟨⟨C, D, G⟩, P, Q, β⟩ hΓ := by
  cases h
  exact (eqToIso (generatedInclusion_evaluation F P Q α hΓ)).symm ≪≫
    generatedComparison F P η Q α hΓ ≪≫
      eqToIso (generatedEndpoint_evaluation F P η Q α hΓ)

end SignatureCylinder
end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
