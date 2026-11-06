import SquareKit.Internal.PathTransport.TwoFamilyModelTransportObjects
import SquareKit.Internal.PathTransport.TwoFamilyBranchReindexObjects
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) {Γ : Context.{u}} (A : Family Γ) (B : Family A.total)
variable (x y : ULift.{u+1} (TwoFamily.Section A.data))
variable (p : ULift.{u+1} (TwoFamily.Section (TwoFamily.closedId A.data x.down y.down)))
local notation "M" => fullModel C D
set_option maxHeartbeats 1000000 in
theorem transportValue_objects :
    (rootContraction C D A x).val.ReindexedBranchFormula (motive M A B x)
      ((M).subTy B ((M).toStructuralModel.sectionSub A x)) (motive_root M A B x).symm
      ((M).toStructuralModel.endpointSub A x y p).down
      ((M).subTy B ((M).toStructuralModel.sectionSub A y))
      (fun b => (transportValue M A B x y p ⟨b⟩).down) := by
  have r := @SourceContraction.BranchFormula.reindex_cast
    ((M).toStructuralModel.pathContext A x) Γ Γ ((M).toStructuralModel.rootSub A x).down
    (rootContraction C D A x).val (motive M A B x)
    ((M).subTy B ((M).toStructuralModel.sectionSub A x)) (motive_root M A B x).symm
    (fun b => (transportSection M A B x ⟨b⟩).down)
    (transportSection_objects C D A B x)
    ((M).toStructuralModel.endpointSub A x y p).down
    ((M).subTy B ((M).toStructuralModel.sectionSub A y)) (motive_endpoint M A B x y p)
  have e : (fun b => (transportValue M A B x y p ⟨b⟩).down) =
      (fun b => TwoFamily.Section.cast (congrArg Family.data (motive_endpoint M A B x y p))
        ((transportSection M A B x ⟨b⟩).down.reindex (motive M A B x).data
          ((M).toStructuralModel.endpointSub A x y p).down)) := by
    funext b
    have he := sectionCast_down (motive_endpoint M A B x y p)
      ((M).subTm (transportSection M A B x ⟨b⟩) ((M).toStructuralModel.endpointSub A x y p))
    run_tac Lean.Elab.Tactic.withMainContext do
      let he ← Lean.Meta.getLocalDeclFromUserName `he
      (← Lean.Elab.Tactic.getMainGoal).assign he.toExpr
      Lean.Elab.Tactic.replaceMainGoal []
  rw [e]
  exact r
end SquareKit.Internal.PathTransport.HigherInterpretation
