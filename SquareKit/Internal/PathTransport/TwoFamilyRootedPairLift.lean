import SquareKit.Internal.PathTransport.TwoFamilyRootedTransport
import SquareKit.Internal.PathTransport.TwoFamilyPairLiftReindex
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
theorem rootedPathFamily_root :
    reindex x.lift (rootedPathFamily F x) = closedId F x x := by
  rw [rootedPathFamily_direct]
  change x.lift.comp ((rootedEndpoint F x).comp (openIdHigher F)) =
    (endpointPair F x x).lift.comp (openIdHigher F)
  rw [← strictFunctor_comp_assoc, rootedEndpoint_reflexive, endpointPair_diagonal]

theorem rootedReflexivity_pairLift :
    pairLift (rootedPathFamily F x) x.lift
      (Section.cast (rootedPathFamily_root F x).symm (closedReflexivity F x)) =
      rootedReflexivity F x := by
  unfold pairLift closedReflexivity rootedReflexivity rootedReflexivityDirect reindexLiftFunctor
  rw [Section.cast_lift, Section.cast_lift]
  unfold familySubstitution
  simp only [strictFunctor_comp_assoc]
  rw [familyCast_reindex_square]
  simp only [← strictFunctor_comp_assoc, familyCast_comp]
  rfl
end SquareKit.Internal.PathTransport.TwoFamily
