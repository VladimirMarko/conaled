import SquareKit.Internal.PathTransport.TwoFamilyRootedComponent
import SquareKit.Internal.PathTransport.TwoFamilyModelRootContraction
import SquareKit.Internal.PathTransport.TwoFamilySourceContractionCast
/-! The source-model inclusion cast retains the constructed retraction and coherent homotopy. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
universe u
variable (C D : Context.{u}) {Γ : Context.{u}} (A : Family Γ)
 (x : ULift.{u+1} (TwoFamily.Section A.data))
theorem rootContraction_retraction : (rootContraction C D A x).val.retraction =
 (rawRootContraction C D A x).retraction := by
 have h := @SourceContraction.cast_retraction ((structuralModel C D).pathContext A x) Γ _ _ (rootSub_down_eq C D A x).symm (rawRootContraction C D A x)
 run_tac Lean.Elab.Tactic.withMainContext do
  let d ← Lean.Meta.getLocalDeclFromUserName `h
  (← Lean.Elab.Tactic.getMainGoal).assign d.toExpr
  Lean.Elab.Tactic.replaceMainGoal []


theorem rootContraction_homotopy : HEq (rootContraction C D A x).val.homotopy
 (rootedContraction A.data x.down) := by
 have h := @SourceContraction.cast_homotopy ((structuralModel C D).pathContext A x) Γ _ _ (rootSub_down_eq C D A x).symm (rawRootContraction C D A x)
 run_tac Lean.Elab.Tactic.withMainContext do
  let d ← Lean.Meta.getLocalDeclFromUserName `h
  (← Lean.Elab.Tactic.getMainGoal).assign d.toExpr
  Lean.Elab.Tactic.replaceMainGoal []
end SquareKit.Internal.PathTransport.HigherInterpretation
