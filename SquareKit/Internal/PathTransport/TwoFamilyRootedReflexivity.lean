import SquareKit.Internal.PathTransport.TwoFamilyRootedFamily
import SquareKit.Internal.PathTransport.TwoFamilyReindexLift
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
variable (x : Section F)
omit [∀ (γ : Γ), IsGroupoid (F.obj γ).Carrier] [∀ (γ : Γ), IsLocallyGroupoid (F.obj γ).Carrier] in
theorem rootedEndpoint_reflexive :
    x.lift.comp (rootedEndpoint F x) = x.lift.comp (diagonalTotal F) := by
  apply endpoint_functor_ext F
  · rw [strictPseudofunctor_comp_assoc, rootedEndpoint_first, ← strictPseudofunctor_comp_assoc, x.over,
      strictPseudofunctor_id_comp, strictPseudofunctor_comp_assoc, diagonal_endpoint, strictPseudofunctor_comp_id]
  · rw [strictPseudofunctor_comp_assoc, rootedEndpoint_second, strictPseudofunctor_comp_id,
      strictPseudofunctor_comp_assoc, diagonal_endpoint, strictPseudofunctor_comp_id]

theorem rootedReflexivity_base :
    (x.lift.comp (pathReflexivity F)).comp (projectionHigher (openIdHigher F)) =
      x.lift.comp (rootedEndpoint F x) := by
  rw [strictPseudofunctor_comp_assoc]
  change x.lift.comp ((pathReflexivity F).comp (pathEndpoints F)) = _
  rw [pathReflexivity_endpoints]
  exact (rootedEndpoint_reflexive F x).symm

noncomputable def rootedReflexivityDirect :
    StrictPseudofunctor Γ (Total (reindex (rootedEndpoint F x) (openIdHigher F))) :=
  reindexLiftFunctor (openIdHigher F) (rootedEndpoint F x) x.lift
    (x.lift.comp (pathReflexivity F)) (rootedReflexivity_base F x)

theorem rootedReflexivityDirect_embedding :
    (rootedReflexivityDirect F x).comp (reindexHigher (openIdHigher F) (rootedEndpoint F x)) =
      x.lift.comp (pathReflexivity F) := reindexLiftFunctor_map _ _ _ _ _
theorem rootedReflexivityDirect_projection :
    (rootedReflexivityDirect F x).comp (projectionHigher (reindex (rootedEndpoint F x) (openIdHigher F))) =
      x.lift := reindexLiftFunctor_projection _ _ _ _ _

noncomputable def rootedRetractionDirect :
    StrictPseudofunctor (Total (reindex (rootedEndpoint F x) (openIdHigher F))) Γ :=
  (projectionHigher (reindex (rootedEndpoint F x) (openIdHigher F))).comp (projectionHigher F)
theorem rootedReflexivityDirect_retraction :
    (rootedReflexivityDirect F x).comp (rootedRetractionDirect F x) = StrictPseudofunctor.id Γ := by
  unfold rootedRetractionDirect
  rw [← strictPseudofunctor_comp_assoc, rootedReflexivityDirect_projection]
  exact x.over
end SquareKit.Internal.PathTransport.TwoFamily
