import SquareKit.Internal.PathTransport.TwoFamilyModelComparisons
import SquareKit.Internal.PathTransport.TwoFamilyPairLiftSubstitution
import SquareKit.Internal.PathTransport.TwoFamilyContractionRetractionSubstitution
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u
variable (C D : Context.{u})
local notation "M" => structuralModel C D

theorem squareLift_down_eq {Γ Δ Γ' Δ' : Context.{u}}
    (F : ULift.{u+1} (StrictPseudofunctor Δ Γ))
    (F' : ULift.{u+1} (StrictPseudofunctor Δ' Γ'))
    (K : ULift.{u+1} (StrictPseudofunctor Γ' Γ))
    (L : ULift.{u+1} (StrictPseudofunctor Δ' Δ))
    (h : (M).compSub K F' = (M).compSub F L) (A : Family Γ) :
    ((M).squareLift F F' K L h A).down =
      TwoFamily.contractionBranchSubstitution F.down F'.down K.down L.down
        (congrArg ULift.down h) A.data := by
  unfold Typed.StructuralModel.squareLift
  dsimp only [structuralModel]
  have hc := sectionCast_down
    ((M).square_variable_type F F' K L h A).symm
    (ULift.up (TwoFamily.variableSection ((A.reindex K.down).reindex F'.down).data))
  have hp := congrArg (fun t => TwoFamily.pairLift (A.reindex F.down).data
    ((TwoFamily.projectionHigher ((A.reindex K.down).reindex F'.down).data).comp L.down) t) hc
  exact hp.trans (TwoFamily.pairLift_familySubstitution (A.reindex F.down).data L.down
    (TwoFamily.retractionBranch_family F.down F'.down K.down L.down
      (congrArg ULift.down h) A.data).symm _)
end SquareKit.Internal.PathTransport.HigherInterpretation
