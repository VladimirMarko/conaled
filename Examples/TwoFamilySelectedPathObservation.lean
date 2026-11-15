import Examples.FrozenMemoSelectedPaths
import Examples.TwoFamilyFrozenPointData
import SquareKit.Internal.PathTransport.TwoFamilySectionValues
/-! Retain the original frozen higher witness through normalized section values.
The structural proof composes both weakenings before specializing the eight-binder context. -/
noncomputable section
namespace Examples.FrozenMemoStages
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport HigherInterpretation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u
variable (C D : Context.{u})
local notation "M" => structuralModel C D
theorem SelectedPaths.reindex_value (R : SelectedPaths M) {Δ : Context.{u}}
 (σ : (M).Substitution Δ R.context) (δ : Δ) :
 HEq (sectionValue (R.reindex σ).toParallel.identity (R.reindex σ).h δ)
 (sectionValue R.toParallel.identity R.h (σ.down.obj δ)) := by
  have h₁ := sectionValue_cast (R.toParallel.identity_reindex σ) ((M).subTm R.h σ) δ
  have h₂ := heq_of_eq (sectionValue_reindex R.toParallel.identity R.h σ.down δ)
  run_tac Lean.Elab.Tactic.withMainContext do
    let h₁ ← Lean.Meta.getLocalDeclFromUserName `h₁
    let h₂ ← Lean.Meta.getLocalDeclFromUserName `h₂
    let t₁ ← Lean.instantiateMVars h₁.type
    let t₂ ← Lean.instantiateMVars h₂.type
    let a := t₁.getAppArgs
    let b := t₂.getAppArgs
    let proof := Lean.mkAppN (Lean.mkConst ``HEq.trans t₁.getAppFn.constLevels!)
      #[a[0]!,a[2]!,b[2]!,a[1]!,a[3]!,b[3]!,h₁.toExpr,h₂.toExpr]
    Lean.Elab.Tactic.closeMainGoal `exact proof
theorem Parallel.addH_value (P : Parallel M) (z : (show Family (show Context from P.context) from P.identity).total) :
 HEq (sectionValue P.addH.toParallel.identity P.addH.h z) z.fiber := by
  have h₁ := sectionValue_cast (P.identity_reindex ((M).weaken P.context P.identity))
    ((M).genericVariable P.context P.identity) z
  have h₂ := (TwoFamily.variableSection P.identity.data).normalObj_fiber_heq (TwoFamily.reindex (TwoFamily.projectionHigher P.identity.data) P.identity.data) z
  run_tac Lean.Elab.Tactic.withMainContext do
    let h₁ ← Lean.Meta.getLocalDeclFromUserName `h₁
    let h₂ ← Lean.Meta.getLocalDeclFromUserName `h₂
    let t₁ ← Lean.instantiateMVars h₁.type
    let t₂ ← Lean.instantiateMVars h₂.type
    let a := t₁.getAppArgs
    let b := t₂.getAppArgs
    let proof := Lean.mkAppN (Lean.mkConst ``HEq.trans t₁.getAppFn.constLevels!)
      #[a[0]!,a[2]!,b[2]!,a[1]!,a[3]!,b[3]!,h₁.toExpr,h₂.toExpr]
    Lean.Elab.Tactic.closeMainGoal `exact proof
theorem selectedPaths_two_weaken (P : Parallel M)
 (Q : Family P.addH.context) (U : Family Q.total) (z : U.total) :
 HEq (sectionValue
  (((P.addH.reindex ((M).weaken P.addH.context Q)).reindex ((M).weaken Q.total U)).toParallel.identity)
  (((P.addH.reindex ((M).weaken P.addH.context Q)).reindex ((M).weaken Q.total U)).h) z)
 z.base.base.fiber := by
  have h₁ := SelectedPaths.reindex_value C D (P.addH.reindex ((M).weaken P.addH.context Q)) ((M).weaken Q.total U) z
  have hmid := SelectedPaths.reindex_value C D P.addH ((M).weaken P.addH.context Q) z.base
  have hlast := Parallel.addH_value C D P z.base.base
  run_tac Lean.Elab.Tactic.withMainContext do
    let h₁ ← Lean.Meta.getLocalDeclFromUserName `h₁
    let h₂ ← Lean.Meta.getLocalDeclFromUserName `hmid
    let h₃ ← Lean.Meta.getLocalDeclFromUserName `hlast
    let t₁ ← Lean.instantiateMVars h₁.type
    let t₂ ← Lean.instantiateMVars h₂.type
    let t₃ ← Lean.instantiateMVars h₃.type
    let a := t₁.getAppArgs
    let b := t₂.getAppArgs
    let c := t₃.getAppArgs
    let q := Lean.mkAppN (Lean.mkConst ``HEq.trans t₁.getAppFn.constLevels!)
      #[a[0]!,a[2]!,b[2]!,a[1]!,a[3]!,b[3]!,h₁.toExpr,h₂.toExpr]
    let proof := Lean.mkAppN (Lean.mkConst ``HEq.trans t₁.getAppFn.constLevels!)
      #[a[0]!,b[2]!,c[2]!,a[1]!,b[3]!,c[3]!,q,h₃.toExpr]
    Lean.Elab.Tactic.closeMainGoal `exact proof
variable (A : Family Context.empty) (B : Family A.total)
set_option linter.defProp false
def inputPaths_normalPayload (z : higherInputContext C D A B) :=
  selectedPaths_two_weaken C D (parallel M A B) (qFamily M A B) (uFamily M A B) z
/-- The normalized value of the original selected input homotopy is its assigned payload. -/
theorem inputPaths_normalValue (z : higherInputContext C D A B) :
 HEq (sectionValue (inputPaths M A B).toParallel.identity (inputPaths M A B).h z)
   z.base.base.fiber := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let args ← #[`C, `D, `A, `B, `z].mapM fun n => return (← Lean.Meta.getLocalDeclFromUserName n).toExpr
    Lean.Elab.Tactic.closeMainGoal `exact
      (Lean.mkAppN (Lean.mkConst ``inputPaths_normalPayload [Lean.Level.param `u]) args)
end Examples.FrozenMemoStages
namespace Examples.TwoFamilyFrozenPoint
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport HigherInterpretation
open Examples.TwoFamilyModelData Examples.FrozenMemoStages
set_option maxRecDepth 2000
set_option linter.defProp false
/-- Retain the entire normalized selected witness at the concrete integer assignment. -/
def normalizedPathOperands_retained (k : ℤ) :=
 inputPaths_normalValue integerContext integerContext emptyA emptyB (assignedPoint k)
/-- The selected normalized two-cell has multiplicative integer label `k`. -/
def normalizedPathObservation (k : ℤ) :=
 congrArg (fun t : LocallyDiscrete (Discrete (Multiplicative ℤ)) => t.as.as)
  (@eq_of_heq (LocallyDiscrete (Discrete (Multiplicative ℤ))) _ _ (normalizedPathOperands_retained k))
/-- The additive integer observation of the same selected normalized value is `k`. -/
def normalizedIntegerObservation (k : ℤ) :=
 congrArg Multiplicative.toAdd (normalizedPathObservation k)
end Examples.TwoFamilyFrozenPoint
