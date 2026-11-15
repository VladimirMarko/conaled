import SquareKit.Internal.PathTransport.TwoFamilyRootedTransport
import SquareKit.Internal.PathTransport.TwoFamilyPathContractionFirst
import SquareKit.Internal.PathTransport.TwoStrongCast
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
noncomputable abbrev rootedDirectFamily := reindex (rootedEndpoint F x) (openIdHigher F)
noncomputable abbrev rootedDirectEmbedding := reindexHigher (openIdHigher F) (rootedEndpoint F x)
noncomputable abbrev rootedDirectRetract := (rootedRetractionDirect F x).comp (rootedReflexivityDirect F x)
theorem rootedDirectEmbedding_first :
    (rootedDirectEmbedding F x).comp (pathFirst F) = (rootedRetractionDirect F x).comp x.lift := by
  rw [pathFirst_normal, ← strictFunctor_comp_assoc]
  change ((reindexHigher (openIdHigher F) (rootedEndpoint F x)).comp
    (projectionHigher (openIdHigher F))).comp (endpointProjection F true) = _
  rw [reindexHigher_projection, strictFunctor_comp_assoc, rootedEndpoint_first, ← strictFunctor_comp_assoc]
  rfl
theorem rootedDirectEmbedding_second :
    (rootedDirectEmbedding F x).comp (pathSecond F) = projectionHigher (rootedDirectFamily F x) := by
  rw [pathSecond_normal, ← strictFunctor_comp_assoc]
  change ((reindexHigher (openIdHigher F) (rootedEndpoint F x)).comp
    (projectionHigher (openIdHigher F))).comp (endpointProjection F false) = _
  rw [reindexHigher_projection, strictFunctor_comp_assoc, rootedEndpoint_second, strictFunctor_comp_id]

theorem rootedContractionMapped_source :
    (rootedDirectEmbedding F x).comp (contractionRetract F) =
      (rootedDirectRetract F x).comp (rootedDirectEmbedding F x) := by
  change (rootedDirectEmbedding F x).comp ((pathFirst F).comp (pathReflexivity F)) = _
  rw [← strictFunctor_comp_assoc, rootedDirectEmbedding_first, strictFunctor_comp_assoc,
    ← rootedReflexivityDirect_embedding, ← strictFunctor_comp_assoc]
theorem rootedContractionMapped_target :
    (rootedDirectEmbedding F x).comp (StrictPseudofunctor.id (PathContext F)) =
      (StrictPseudofunctor.id (Total (rootedDirectFamily F x))).comp (rootedDirectEmbedding F x) :=
  (StrictTwoTransformation.functor_comp_id _).trans (StrictTwoTransformation.functor_id_comp _).symm
variable [IsLocallyGroupoid Γ]
noncomputable def rootedContractionMapped : Pseudofunctor.StrongTrans
    ((rootedDirectRetract F x).comp (rootedDirectEmbedding F x)).toPseudofunctor
    ((StrictPseudofunctor.id (Total (rootedDirectFamily F x))).comp (rootedDirectEmbedding F x)).toPseudofunctor :=
  strongCast (rootedContractionMapped_source F x) (rootedContractionMapped_target F x)
    (strongPrecomp (pathContraction F) (rootedDirectEmbedding F x))
theorem rootedContractionMapped_heq : HEq (rootedContractionMapped F x)
    (strongPrecomp (pathContraction F) (rootedDirectEmbedding F x)) := strongCast_heq _ _ _

theorem rootedBaseContraction_source :
    ((rootedDirectRetract F x).comp (rootedDirectEmbedding F x)).comp (pathSecond F) =
      (rootedDirectRetract F x).comp (projectionHigher (rootedDirectFamily F x)) := by
  rw [strictFunctor_comp_assoc, rootedDirectEmbedding_second]
theorem rootedBaseContraction_target :
    ((StrictPseudofunctor.id (Total (rootedDirectFamily F x))).comp (rootedDirectEmbedding F x)).comp (pathSecond F) =
      (StrictPseudofunctor.id (Total (rootedDirectFamily F x))).comp (projectionHigher (rootedDirectFamily F x)) := by
  rw [strictFunctor_comp_assoc, rootedDirectEmbedding_second]
noncomputable def rootedBaseContraction : Pseudofunctor.StrongTrans
    ((rootedDirectRetract F x).comp (projectionHigher (rootedDirectFamily F x))).toPseudofunctor
    ((StrictPseudofunctor.id (Total (rootedDirectFamily F x))).comp (projectionHigher (rootedDirectFamily F x))).toPseudofunctor :=
  strongCast (rootedBaseContraction_source F x) (rootedBaseContraction_target F x)
    (strongPostcomp (rootedContractionMapped F x) (pathSecond F))
theorem rootedBaseContraction_heq : HEq (rootedBaseContraction F x)
    (strongPostcomp (rootedContractionMapped F x) (pathSecond F)) := strongCast_heq _ _ _
end SquareKit.Internal.PathTransport.TwoFamily
