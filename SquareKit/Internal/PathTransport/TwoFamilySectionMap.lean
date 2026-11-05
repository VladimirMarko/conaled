import SquareKit.Internal.PathTransport.TwoFamilySections
import SquareKit.Internal.PathTransport.TwoFamilyMap
/-! Transport of arbitrary higher sections through coherent family maps. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Bicategory.Strict Γ]
variable {F G : Family.{u,v,w,u',v',w'} Γ}
variable (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
theorem StrongMap.toHigher_projection :
    (StrongMap.toHigher η).comp (projectionHigher G) = projectionHigher F :=
  StrictTwoTransformation.functor_ext rfl
/-- Transport every higher section through a coherent family transformation. -/
def Section.map (s : Section F) : Section G where
  lift := s.lift.comp (StrongMap.toHigher η)
  over := by
    calc
      (s.lift.comp (StrongMap.toHigher η)).comp (projectionHigher G) =
        s.lift.comp ((StrongMap.toHigher η).comp (projectionHigher G)) :=
          StrictTwoTransformation.functor_ext rfl
      _ = s.lift.comp (projectionHigher F) := congrArg (fun H => s.lift.comp H)
        (StrongMap.toHigher_projection η)
      _ = StrictPseudofunctor.id Γ := s.over
end SquareKit.Internal.PathTransport.TwoFamily
