import SquareKit.Internal.PathTransport.TwoFamilyPairLiftReindex
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
theorem pairLift_id (x : Section F) :
    pairLift F (StrictPseudofunctor.id Γ) (Section.cast (reindex_id F).symm x) = x.lift := by
  unfold pairLift
  rw [Section.cast_lift, strictFunctor_comp_assoc]
  rw [familyCast_precomp_eq_of_heq (reindex_id F).symm _ _ (reindexHigher_id_heq F).symm]
  exact strictFunctor_comp_id x.lift
end SquareKit.Internal.PathTransport.TwoFamily
