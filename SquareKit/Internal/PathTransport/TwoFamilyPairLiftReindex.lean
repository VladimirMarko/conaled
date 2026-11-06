import SquareKit.Internal.PathTransport.TwoFamilyPairLiftIdentities
import SquareKit.Internal.PathTransport.TwoFamilyHigherReindexLaws
import SquareKit.Internal.PathTransport.TwoFunctorComposition
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable {Δ : Type*} [Bicategory Δ] [Strict Δ] (σ : StrictPseudofunctor Δ Γ)
theorem Section.cast_lift {G H : Family.{uΓ,vΓ,wΓ,u,v,w} Γ} (e : G = H) (s : Section G) :
    (Section.cast e s).lift = s.lift.comp (familyCast e) := by
  cases e
  exact (strictFunctor_comp_id s.lift).symm

theorem variableLift_recombined :
    (variableSection F).lift.comp (reindexHigher F (projectionHigher F)) = StrictPseudofunctor.id (Total F) := by
  exact strictFunctorData_ext rfl

theorem pairLift_reindex :
    pairLift F ((projectionHigher (reindex σ F)).comp σ)
      (Section.cast (reindex_comp F σ (projectionHigher (reindex σ F)))
        (variableSection (reindex σ F))) = reindexHigher F σ := by
  unfold pairLift
  rw [Section.cast_lift, strictFunctor_comp_assoc]
  rw [familyCast_precomp_eq_of_heq (reindex_comp F σ (projectionHigher (reindex σ F)))
    _ _ (reindexHigher_comp_heq F σ (projectionHigher (reindex σ F)))]
  rw [← strictFunctor_comp_assoc, variableLift_recombined, strictFunctor_id_comp]
end SquareKit.Internal.PathTransport.TwoFamily
