import Examples.CubicalFrozenOrdinaryActionData
import Examples.FrozenOrdinaryActionEvaluation

/-! The cubical action is the ordinary action of the original frozen source expression. -/
noncomputable section
namespace Examples.CubicalFrozenOrdinaryAction
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf SquareKit.Cubical.Contextual
open SquareKit.Cubical.CategoryCocycles
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open Examples.CubicalCocycleAssignment Examples.CubicalFrozenActionInputs
open Examples.FrozenOrdinaryAction
set_option maxHeartbeats 800000

private theorem lift_heq {A B : Type} {a : A} {b : B} (h : HEq a b) :
    HEq (ULift.up.{1} a) (ULift.up.{1} b) := by cases h; rfl

theorem assigned_action : HEq
    (cocycleModel.subTm (action cocycleModel cocycleBase cocycleRootedFamily) ⟨assignInput⟩)
    (ULift.up.{1} sourceHigherAction) := by
  have h₁ := action_reindex cocycleModel cocycleBase cocycleRootedFamily ⟨assignInput⟩
  have h₂ := ordinaryApValue_congr cocycleModel (A := assignedType) (A' := assignedLoopFamily)
    (C := assignedType) (C' := assignedLoopFamily) rfl rfl
    (t := reindexedTransport cocycleModel cocycleBase cocycleRootedFamily ⟨assignInput⟩)
    (t' := ⟨assignedTransport⟩) HEq.rfl
    (lift_heq (heq_of_eq assigned_p)) (lift_heq (heq_of_eq assigned_p')) (lift_heq assigned_h)
  have h₃ := cocycleOrdinaryAction_heq cocycleBase cocycleRootedFamily assignedType.filling assignedType.lawful
    assignedTransport selectedNormalizedHomotopy
  run_tac Lean.Elab.Tactic.withMainContext do
    let h₁ ← Lean.Meta.getLocalDeclFromUserName `h₁
    let h₂ ← Lean.Meta.getLocalDeclFromUserName `h₂
    let h₃ ← Lean.Meta.getLocalDeclFromUserName `h₃
    let t₁ ← Lean.instantiateMVars h₁.type
    let t₂ ← Lean.instantiateMVars h₂.type
    let t₃ ← Lean.instantiateMVars h₃.type
    let a := t₁.getAppArgs
    let b := t₂.getAppArgs
    let c := t₃.getAppArgs
    let hs := Lean.mkAppN (Lean.mkConst ``HEq.symm t₃.getAppFn.constLevels!)
      #[c[0]!,c[2]!,c[1]!,c[3]!,h₃.toExpr]
    let q := Lean.mkAppN (Lean.mkConst ``HEq.trans t₁.getAppFn.constLevels!)
      #[a[0]!,a[2]!,b[2]!,a[1]!,a[3]!,b[3]!,h₁.toExpr,h₂.toExpr]
    let proof := Lean.mkAppN (Lean.mkConst ``HEq.trans t₁.getAppFn.constLevels!)
      #[a[0]!,b[2]!,c[0]!,a[1]!,b[3]!,c[1]!,q,hs]
    Lean.Elab.Tactic.closeMainGoal `exact proof

end Examples.CubicalFrozenOrdinaryAction
