import SquareKit.Internal.PathTransport.TwoFamilyModelComparisons
import SquareKit.Internal.PathTransport.TwoFamilyModelSubstitution
import SquareKit.Internal.PathTransport.PathSubComparison
import SquareKit.Internal.PathTransport.TwoFamilyRootedSubstitution
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u
variable (C D : Context.{u})
local notation "M" => structuralModel C D
private theorem rootedSubstitution_of_lift {Γ Δ : Context.{u}} (A : Family Γ)
    (x : TwoFamily.Section A.data) (σ : StrictPseudofunctor Δ Γ)
    (κ : StrictPseudofunctor (A.reindex σ).total A.total)
    (hκ : κ = TwoFamily.reindexHigher A.data σ)
    (e : TwoFamily.rootedPathFamily (A.reindex σ).data (x.reindex A.data σ) =
      TwoFamily.reindex κ (TwoFamily.rootedPathFamily A.data x)) :
    TwoFamily.familySubstitution (TwoFamily.rootedPathFamily A.data x) κ e =
      TwoFamily.rootedSubstitution A.data x σ := by
  subst κ
  rfl

theorem pathSub_down_eq {Γ Δ : Context.{u}} (A : Family Γ)
    (x : ULift.{u+1} (TwoFamily.Section A.data))
    (σ : ULift.{u+1} (StrictPseudofunctor Δ Γ)) :
    ((M).pathSub A x σ).down = (by
      change StrictPseudofunctor
        (TwoFamily.Total (TwoFamily.rootedPathFamily (A.reindex σ.down).data (x.down.reindex A.data σ.down)))
        (TwoFamily.Total (TwoFamily.rootedPathFamily A.data x.down))
      exact TwoFamily.rootedSubstitution (Γ := Γ) (Δ := Δ) A.data x.down σ.down) := by
  have hs := congrArg ULift.down ((M).pathSub_lift_comparison A x σ)
  have hf := familySubstitution_down_eq C D ((M).pathFamily A x)
    ((M).pathFamily ((M).subTy A σ) ((M).subTm x σ)) ((M).lift A σ)
    ((M).pathFamily_sub A x σ).symm
  have he := congrArg Family.data ((M).pathFamily_sub A x σ).symm
  have hg := rootedSubstitution_of_lift A x.down σ.down (((M).lift A σ).down)
    (lift_down_eq_reindexHigher C D A σ) he
  have hsf := hs.trans hf
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let a ← Lean.Meta.getLocalDeclFromUserName `hsf
      let b ← Lean.Meta.getLocalDeclFromUserName `hg
      let ta ← Lean.Meta.whnf (← Lean.Meta.inferType a.toExpr)
      let bt ← Lean.Meta.whnf (← Lean.Meta.inferType b.toExpr)
      let #[ty, lhs, mid] := ta.getAppArgs | throwError "expected equality"
      let #[_, _, rhs] := bt.getAppArgs | throwError "expected equality"
      let .const _ [level] := ta.getAppFn | throwError "no level"
      g.assign (Lean.mkAppN (Lean.mkConst ``Eq.trans [level]) #[ty, lhs, mid, rhs, a.toExpr, b.toExpr])
    Lean.Elab.Tactic.replaceMainGoal []
end SquareKit.Internal.PathTransport.HigherInterpretation
