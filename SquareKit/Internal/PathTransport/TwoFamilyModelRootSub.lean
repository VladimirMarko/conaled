import SquareKit.Internal.PathTransport.TwoFamilyModelSectionSub
import SquareKit.Internal.PathTransport.TwoFamilyRootedPairLift
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u
variable (C D : Context.{u})
local notation "M" => structuralModel C D
private theorem rootedReflexivity_of_section {Γ : Context.{u}} (A : Family Γ)
    (x : TwoFamily.Section A.data) (b : StrictPseudofunctor Γ A.total)
    (hb : b = x.lift)
    (e : TwoFamily.closedId A.data x x = TwoFamily.reindex b (TwoFamily.rootedPathFamily A.data x)) :
    TwoFamily.pairLift (TwoFamily.rootedPathFamily A.data x) b
      (TwoFamily.Section.cast e (TwoFamily.closedReflexivity A.data x)) =
      TwoFamily.rootedReflexivity A.data x := by
  subst b
  exact TwoFamily.rootedReflexivity_pairLift A.data x

theorem rootSub_down_eq {Γ : Context.{u}} (A : Family Γ)
    (x : ULift.{u+1} (TwoFamily.Section A.data)) :
    ((M).rootSub A x).down = TwoFamily.rootedReflexivity A.data x.down := by
  unfold Typed.StructuralModel.rootSub
  dsimp only [structuralModel]
  have hc := sectionCast_down ((M).pathFamily_root A x).symm
    (ULift.up (TwoFamily.closedReflexivity A.data x.down))
  have hp := congrArg (fun t => TwoFamily.pairLift (TwoFamily.rootedPathFamily A.data x.down)
    (((M).sectionSub A x).down) t) hc
  exact hp.trans (rootedReflexivity_of_section A x.down (((M).sectionSub A x).down)
    (sectionSub_down_eq C D A x) _)
end SquareKit.Internal.PathTransport.HigherInterpretation
