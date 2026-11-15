import SquareKit.Internal.PathTransport.TwoFamilyClosedReflexivitySubstitution
import SquareKit.Internal.PathTransport.TwoFamilyPathSubstitutionLaws
import SquareKit.Internal.PathTransport.TwoFamilySectionReindexLift
import SquareKit.Internal.PathTransport.TwoFunctorComposition
import SquareKit.Internal.PathTransport.TwoFamilyPairLiftReindex
/-! Fixed-endpoint path contexts embed in the two-endpoint path context,
retaining the selected endpoint section and every higher cell. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
noncomputable def closedPathEmbedding (s t : Section F) :
    StrictPseudofunctor (Total (closedId F s t)) (PathContext F) :=
  reindexHigher (openIdHigher F) (endpointPair F s t).lift

theorem pathFirst_normal : pathFirst F = (pathEndpoints F).comp (endpointProjection F true) := by
  unfold endpointProjection
  rw [strictFunctorOfEqualData_eq]
  rfl

theorem pathSecond_normal : pathSecond F = (pathEndpoints F).comp (endpointProjection F false) := by
  unfold endpointProjection
  rw [strictFunctorOfEqualData_eq]
  rfl

theorem closedPathEmbedding_first (s t : Section F) :
    (closedPathEmbedding F s t).comp (pathFirst F) =
      (projectionHigher (closedId F s t)).comp s.lift := by
  rw [pathFirst_normal, ← strictFunctor_comp_assoc]
  change ((reindexHigher (openIdHigher F) (endpointPair F s t).lift).comp
    (projectionHigher (openIdHigher F))).comp (endpointProjection F true) = _
  rw [reindexHigher_projection, strictFunctor_comp_assoc, endpointPair_first]
  rfl

theorem closedPathEmbedding_second (s t : Section F) :
    (closedPathEmbedding F s t).comp (pathSecond F) =
      (projectionHigher (closedId F s t)).comp t.lift := by
  rw [pathSecond_normal, ← strictFunctor_comp_assoc]
  change ((reindexHigher (openIdHigher F) (endpointPair F s t).lift).comp
    (projectionHigher (openIdHigher F))).comp (endpointProjection F false) = _
  rw [reindexHigher_projection, strictFunctor_comp_assoc, endpointPair_second]
  rfl

theorem closedReflexivity_embedding (s : Section F) :
    (closedReflexivity F s).lift.comp (closedPathEmbedding F s s) =
      s.lift.comp (pathReflexivity F) := by
  change pairLift (openIdHigher F) (endpointPair F s s).lift
    (Section.cast (congrArg (fun H => reindex H (openIdHigher F)) (closedReflexivity_base F s))
      (sectionOfLift (openIdHigher F) (s.lift.comp (pathReflexivity F)))) = _
  rw [pairLift_cast_base (openIdHigher F) (closedReflexivity_base F s)]
  exact factorHigher_reindex (openIdHigher F) _

noncomputable def rootedPathFamily (x : Section F) : Family (Total F) :=
  closedId (reindex (projectionHigher F) F) (x.reindex F (projectionHigher F)) (variableSection F)

noncomputable def rootedPathEmbedding (x : Section F) :
    StrictPseudofunctor (Total (rootedPathFamily F x)) (PathContext F) :=
  (closedPathEmbedding (reindex (projectionHigher F) F)
    (x.reindex F (projectionHigher F)) (variableSection F)).comp
      (pathReindex F (projectionHigher F))

theorem rootedPathEmbedding_first (x : Section F) :
    (rootedPathEmbedding F x).comp (pathFirst F) =
      ((projectionHigher (rootedPathFamily F x)).comp (projectionHigher F)).comp x.lift := by
  unfold rootedPathEmbedding
  rw [strictFunctor_comp_assoc, pathReindex_first, ← strictFunctor_comp_assoc,
    closedPathEmbedding_first, strictFunctor_comp_assoc, Section.reindex_lift,
    ← strictFunctor_comp_assoc]
  rfl
theorem pathReindex_second {Δ : Type*} [Bicategory Δ] [Strict Δ]
    (σ : StrictPseudofunctor Δ Γ) :
    (pathReindex F σ).comp (pathSecond F) =
      (pathSecond (reindex σ F)).comp (reindexHigher F σ) := by
  rw [pathSecond_normal, ← strictFunctor_comp_assoc, pathReindex_endpoints,
    strictFunctor_comp_assoc, endpointReindex_projection, ← strictFunctor_comp_assoc,
    ← pathSecond_normal]

theorem rootedPathEmbedding_second (x : Section F) :
    (rootedPathEmbedding F x).comp (pathSecond F) = projectionHigher (rootedPathFamily F x) := by
  unfold rootedPathEmbedding
  rw [strictFunctor_comp_assoc, pathReindex_second, ← strictFunctor_comp_assoc,
    closedPathEmbedding_second, strictFunctor_comp_assoc, variableLift_recombined,
    strictFunctor_comp_id]
  rfl

end SquareKit.Internal.PathTransport.TwoFamily
