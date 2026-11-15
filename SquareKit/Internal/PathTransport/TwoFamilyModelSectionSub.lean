import SquareKit.Internal.PathTransport.TwoFamilyModelComparisons
import SquareKit.Internal.PathTransport.TwoFamilyPairLiftIdentity
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u
variable (C D : Context.{u})
local notation "M" => structuralModel C D
theorem sectionSub_down_eq {Γ : Context.{u}} (A : Family Γ)
    (x : ULift.{u+1} (TwoFamily.Section A.data)) :
    ((M).sectionSub A x).down = x.down.lift := by
  unfold Typed.StructuralModel.sectionSub
  dsimp only [structuralModel]
  have hc := sectionCast_down (Family.reindex_id A).symm x
  have hp := congrArg (fun t => TwoFamily.pairLift A.data (StrictPseudofunctor.id Γ) t) hc
  exact hp.trans (TwoFamily.pairLift_id A.data x.down)
end SquareKit.Internal.PathTransport.HigherInterpretation
