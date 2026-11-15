import SquareKit.Internal.PathTransport.TwoFamilyPairLiftObjects
import SquareKit.Internal.PathTransport.TwoFamilyModelJObjects
import SquareKit.Internal.PathTransport.TwoFamilyModelSectionSub
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) {Γ : Context.{u}} (A : Family Γ)
variable (x y : ULift.{u+1} (TwoFamily.Section A.data))
local notation "M" => structuralModel C D
set_option maxHeartbeats 1000000 in
theorem endpointSub_objects :
    TwoFamily.PairLiftFiberFormula (TwoFamily.rootedPathFamily A.data x.down)
      (TwoFamily.closedId A.data x.down y.down)
      (fun p => ((M).endpointSub A x y ⟨p⟩).down) := by
  have h := TwoFamily.pairLift_cast_formula (TwoFamily.rootedPathFamily A.data x.down)
    ((M).sectionSub A y).down (TwoFamily.closedId A.data x.down y.down)
    (congrArg Family.data ((M).pathFamily_at A x y).symm)
  have e : (fun p => ((M).endpointSub A x y ⟨p⟩).down) =
      (fun p => TwoFamily.pairLift (TwoFamily.rootedPathFamily A.data x.down)
        ((M).sectionSub A y).down
        (TwoFamily.Section.cast (congrArg Family.data ((M).pathFamily_at A x y).symm) p)) := by
    funext p
    have hc := sectionCast_down ((M).pathFamily_at A x y).symm (ULift.up p)
    have he := congrArg (TwoFamily.pairLift (TwoFamily.rootedPathFamily A.data x.down)
      ((M).sectionSub A y).down) hc
    run_tac Lean.Elab.Tactic.withMainContext do
      let he ← Lean.Meta.getLocalDeclFromUserName `he
      (← Lean.Elab.Tactic.getMainGoal).assign he.toExpr
      Lean.Elab.Tactic.replaceMainGoal []
  exact (congrArg (TwoFamily.PairLiftFiberFormula (TwoFamily.rootedPathFamily A.data x.down)
    (TwoFamily.closedId A.data x.down y.down)) e).mpr h
variable (p : ULift.{u+1} (TwoFamily.Section (TwoFamily.closedId A.data x.down y.down)))
set_option maxHeartbeats 1000000 in
theorem endpointSub_projection :
    ((M).endpointSub A x y p).down.comp (TwoFamily.projectionHigher (TwoFamily.rootedPathFamily A.data x.down)) = y.down.lift := by
  have h := congrArg ULift.down ((M).weaken_pair ((M).pathFamily A x)
    ((M).sectionSub A y) (cast (congrArg ((M).Section Γ) ((M).pathFamily_at A x y).symm) p))
  exact h.trans (sectionSub_down_eq C D A y)

end SquareKit.Internal.PathTransport.HigherInterpretation
