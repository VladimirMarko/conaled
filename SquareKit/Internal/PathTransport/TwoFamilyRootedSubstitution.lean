import SquareKit.Internal.PathTransport.TwoFamilyRootedTransport
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)]
variable {Δ : Type*} [Bicategory Δ] [Strict Δ]
variable (x : Section F) (σ : StrictPseudofunctor Δ Γ)
theorem rootedEndpoint_reindex :
    (rootedEndpoint (reindex σ F) (x.reindex F σ)).comp (endpointReindex F σ) =
      (reindexHigher F σ).comp (rootedEndpoint F x) := by
  apply endpoint_functor_ext F
  · rw [strictFunctor_comp_assoc, endpointReindex_projection, ← strictFunctor_comp_assoc,
      rootedEndpoint_first, strictFunctor_comp_assoc, Section.reindex_lift,
      strictFunctor_comp_assoc, rootedEndpoint_first]
    rw [← strictFunctor_comp_assoc (reindexHigher F σ), reindexHigher_projection, strictFunctor_comp_assoc]
  · rw [strictFunctor_comp_assoc, endpointReindex_projection, ← strictFunctor_comp_assoc,
      rootedEndpoint_second, strictFunctor_id_comp, strictFunctor_comp_assoc,
      rootedEndpoint_second, strictFunctor_comp_id]

theorem rootedPathFamily_reindex :
    reindex (reindexHigher F σ) (rootedPathFamily F x) =
      rootedPathFamily (reindex σ F) (x.reindex F σ) := by
  rw [rootedPathFamily_direct, rootedPathFamily_direct]
  change (reindexHigher F σ).comp ((rootedEndpoint F x).comp (openIdHigher F)) =
    (rootedEndpoint (reindex σ F) (x.reindex F σ)).comp (openIdHigher (reindex σ F))
  rw [← strictFunctor_comp_assoc, ← rootedEndpoint_reindex, strictFunctor_comp_assoc]
  exact congrArg (fun H => (rootedEndpoint (reindex σ F) (x.reindex F σ)).comp H)
    (openIdHigher_reindex F σ).symm

noncomputable def rootedSubstitution :
    StrictPseudofunctor (Total (rootedPathFamily (reindex σ F) (x.reindex F σ)))
      (Total (rootedPathFamily F x)) :=
  familySubstitution (rootedPathFamily F x) (reindexHigher F σ) (rootedPathFamily_reindex F x σ).symm
end SquareKit.Internal.PathTransport.TwoFamily
