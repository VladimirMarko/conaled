import EmittedAcceptance
import ValueRejectionComposition
import EmittedEnvironment
import ConLeche.Verify.CheckerSplit
/-! Experimental #135 checkpoint. Kernel-checked rejection controls for the actual emitted family.
See [measurement and scope report](../../docs/research/relative-emitted-acceptance.md). -/
namespace EmittedRejections
open ConLeche
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 8
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_fvar Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj CheckerReduction.depth_eq


measured_theorem wrong_parameters : checkDecl .verified (fueledOps .verified 32) [] AndInstallation.andEnv (.indDecl GraphEnvironment.existsBlock 1) = .error (.invalid "number of parameters mismatch") := by
  have hb : basisPinHit GraphEnvironment.existsBlock = none := by cbv
  have hn : indParamsOk 1 GraphEnvironment.existsBlock = false := by cbv
  simp only [checkDecl, hb, hn, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem missing_tables : checkDeclsPure .verified (fueledOps .verified 32) [] EmittedEnvironment.declarations ≠ .ok {EmittedEnvironment.environment with tables := []} := by
  intro h
  have he := Except.ok.inj (EmittedAcceptance.accepted.symm.trans h)
  have ht := congrArg Env.tables he
  change [GraphEnvironment.existsTable, GraphEnvironment.andTable] = [] at ht
  contradiction

checked_normal_form wrongDirection : Except CheckError Bool := isDefEqCore .verified EmittedForwardAcceptance.before 32 0 EmittedForwardAcceptance.vtype EmittedGraph.backwardType
measured_theorem direction_mismatch : isDefEqCore .verified EmittedForwardAcceptance.before 32 0 EmittedForwardAcceptance.vtype EmittedGraph.backwardType = .ok false := wrongDirection_eq
checked_normal_form badCv : ConstantVal := {EmittedForwardAcceptance.cv with type := EmittedGraph.backwardType}
checked_normal_form inferred : Except CheckError Expr := inferTypeCore .verified EmittedForwardAcceptance.before 32 0 badCv.type
checked_normal_form u : Level := match inferred with | .ok (.sort u) => u | _ => .zero
measured_theorem infer_ok : inferTypeCore .verified EmittedForwardAcceptance.before 32 0 badCv.type = .ok (.sort u) := inferred_eq
measured_theorem sort_ok : ensureSortCore .verified EmittedForwardAcceptance.before 32 0 (.sort u) = .ok u := by
  rw [ensureSortCore_eq, whnf_sort EmittedForwardAcceptance.before 30 0 u]
  rfl
measured_theorem constant_ok : checkConstantVal (fueledOps .verified 32) EmittedForwardAcceptance.before badCv = .ok () := by
  exact checkConstantVal_of_facts (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) infer_ok sort_ok
measured_theorem value_rejected : checkThmVal (fueledOps .verified 32) EmittedForwardAcceptance.before badCv EmittedForwardAcceptance.value = .error (.invalid s!"type mismatch in theorem {badCv.name}") := by
  exact ValueRejectionComposition.thm_mismatch infer_ok sort_ok (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) EmittedForwardAcceptance.valInfer_ok direction_mismatch
measured_theorem wrong_direction : checkDecl .verified (fueledOps .verified 32) [] EmittedForwardAcceptance.before (.thmDecl badCv EmittedForwardAcceptance.value) = .error (.invalid s!"type mismatch in theorem {badCv.name}") := by
  simp only [checkDecl, constant_ok, value_rejected, bind, Except.bind]
end EmittedRejections
#audit_graph_module
