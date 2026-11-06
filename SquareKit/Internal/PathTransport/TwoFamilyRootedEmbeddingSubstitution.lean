import SquareKit.Internal.PathTransport.TwoFamilyRootedSubstitution
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)]
variable {Δ : Type*} [Bicategory Δ] [Strict Δ]
variable (x : Section F) (σ : StrictPseudofunctor Δ Γ)
theorem rootedPathEmbedding_familySubstitution :
    rootedPathEmbedding F x = familySubstitution (openIdHigher F) (rootedEndpoint F x) (rootedPathFamily_direct F x) :=
  (rootedPathEmbedding_direct F x).symm

theorem rootedSubstitution_embedding :
    (rootedSubstitution F x σ).comp (rootedPathEmbedding F x) =
      (rootedPathEmbedding (reindex σ F) (x.reindex F σ)).comp (pathReindex F σ) := by
  rw [rootedPathEmbedding_familySubstitution, rootedPathEmbedding_familySubstitution,
    rootedSubstitution, pathReindex_familySubstitution, familySubstitution_comp, familySubstitution_comp]
  exact familySubstitution_congr (openIdHigher F) (rootedEndpoint_reindex F x σ).symm _ _

theorem rootedSubstitution_retraction :
    (rootedSubstitution F x σ).comp (rootedRetraction F x) =
      (rootedRetraction (reindex σ F) (x.reindex F σ)).comp σ := by
  unfold rootedRetraction rootedSubstitution
  rw [← strictFunctor_comp_assoc, familySubstitution_projection, strictFunctor_comp_assoc,
    reindexHigher_projection, ← strictFunctor_comp_assoc]
end SquareKit.Internal.PathTransport.TwoFamily
