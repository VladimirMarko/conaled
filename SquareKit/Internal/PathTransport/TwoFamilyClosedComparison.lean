import SquareKit.Internal.PathTransport.TwoFamilyRootedNaturality
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
noncomputable def closedSectionEmbedding (s t : Section F) (p : Section (closedId F s t)) :=
 p.lift.comp (closedPathEmbedding F s t)
theorem closedSectionEmbedding_first (s t : Section F) (p : Section (closedId F s t)) :
 (closedSectionEmbedding F s t p).comp (pathFirst F) = s.lift := by
 unfold closedSectionEmbedding
 rw [strictFunctor_comp_assoc, closedPathEmbedding_first, ← strictFunctor_comp_assoc, p.over, strictFunctor_id_comp]
theorem closedSectionEmbedding_second (s t : Section F) (p : Section (closedId F s t)) :
 (closedSectionEmbedding F s t p).comp (pathSecond F) = t.lift := by
 unfold closedSectionEmbedding
 rw [strictFunctor_comp_assoc, closedPathEmbedding_second, ← strictFunctor_comp_assoc, p.over, strictFunctor_id_comp]
theorem pathReflexivity_second :
 (pathReflexivity F).comp (pathSecond F) = StrictPseudofunctor.id (Total F) := by
 rw [pathSecond_normal, ← strictFunctor_comp_assoc, pathReflexivity_endpoints, diagonal_endpoint]
theorem closedComparison_source (s t : Section F) (p : Section (closedId F s t)) :
 ((closedSectionEmbedding F s t p).comp (contractionRetract F)).comp (pathSecond F) = s.lift := by
 change ((closedSectionEmbedding F s t p).comp ((pathFirst F).comp (pathReflexivity F))).comp (pathSecond F) = _
 rw [strictFunctor_comp_assoc, strictFunctor_comp_assoc, pathReflexivity_second, strictFunctor_comp_id, closedSectionEmbedding_first]
theorem closedComparison_target (s t : Section F) (p : Section (closedId F s t)) :
 ((closedSectionEmbedding F s t p).comp (StrictPseudofunctor.id _)).comp (pathSecond F) = t.lift := by
 rw [strictFunctor_comp_id, closedSectionEmbedding_second]
noncomputable def closedComparison (s t : Section F) (p : Section (closedId F s t)) :
 Pseudofunctor.StrongTrans s.lift.toPseudofunctor t.lift.toPseudofunctor :=
 strongCast (closedComparison_source F s t p) (closedComparison_target F s t p)
  (strongPostcomp (strongPrecomp (pathContraction F) (closedSectionEmbedding F s t p)) (pathSecond F))
theorem closedComparison_heq (s t : Section F) (p : Section (closedId F s t)) :
 HEq (closedComparison F s t p)
  (strongPostcomp (strongPrecomp (pathContraction F) (closedSectionEmbedding F s t p)) (pathSecond F)) :=
 strongCast_heq _ _ _
end SquareKit.Internal.PathTransport.TwoFamily
