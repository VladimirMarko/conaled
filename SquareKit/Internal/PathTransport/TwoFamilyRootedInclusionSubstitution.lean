import SquareKit.Internal.PathTransport.TwoFamilyRootedNormalization
import SquareKit.Internal.PathTransport.TwoFamilyRootedEmbeddingSubstitution
import SquareKit.Internal.PathTransport.TwoFunctorFaithful
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)]
variable (x : Section F)
theorem rootedEndpoint_obj_injective : Function.Injective (rootedEndpoint F x).obj := by
  intro a b h
  have h' := congrArg (endpointProjection F false).obj h
  have ha := congrArg (fun K => K.obj a) (rootedEndpoint_second F x)
  have hb := congrArg (fun K => K.obj b) (rootedEndpoint_second F x)
  exact ha.symm.trans (h'.trans hb)
theorem rootedPathEmbedding_obj_injective : Function.Injective (rootedPathEmbedding F x).obj := by
  rw [rootedPathEmbedding_familySubstitution]
  exact familySubstitution_obj_injective _ _ _ (rootedEndpoint_obj_injective F x)
variable {Δ : Type*} [Bicategory Δ] [Strict Δ] [IsLocallyGroupoid Δ]
variable (σ : StrictPseudofunctor Δ Γ)
theorem rootedSubstitution_reflexivity :
    (rootedReflexivity (reindex σ F) (x.reindex F σ)).comp (rootedSubstitution F x σ) =
      σ.comp (rootedReflexivity F x) := by
  apply strictFunctor_postcomp_injective (rootedPathEmbedding F x)
    (rootedPathEmbedding_obj_injective F x)
    (fun {_ _} => rootedPathEmbedding_map_injective F x)
    (fun {_ _ _ _} => rootedPathEmbedding_cell_injective F x)
  rw [strictFunctor_comp_assoc, rootedSubstitution_embedding, ← strictFunctor_comp_assoc,
    rootedReflexivity_embedding, strictFunctor_comp_assoc, pathReindex_reflexivity,
    ← strictFunctor_comp_assoc, Section.reindex_lift,
    strictFunctor_comp_assoc, strictFunctor_comp_assoc, rootedReflexivity_embedding]
end SquareKit.Internal.PathTransport.TwoFamily
