import SquareKit.Internal.PathTransport.TwoFamilyStructuralModel
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u})
local notation "M" => structuralModel C D
 theorem variable_two_weaken {Γ : Context.{u}} (H : Family Γ) (Q : Family H.total)
    (U : Family Q.total) (z : U.total) :
    HEq (((M).subTm ((M).subTm ((M).genericVariable Γ H) ((M).weaken H.total Q))
      ((M).weaken Q.total U)).down.lift.obj z).fiber z.base.base.fiber := by
  have h1 := (((TwoFamily.variableSection H.data).reindex _ (TwoFamily.projectionHigher Q.data)).reindex_obj_fiber
      _ (TwoFamily.projectionHigher U.data) z)
  have h2 := ((TwoFamily.variableSection H.data).reindex_obj_fiber _ (TwoFamily.projectionHigher Q.data) z.base)
  have h := h1.trans h2
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let d ← Lean.Meta.getLocalDeclFromUserName `h
      g.assign d.toExpr
    Lean.Elab.Tactic.replaceMainGoal []
end SquareKit.Internal.PathTransport.HigherInterpretation
