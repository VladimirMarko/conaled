import AndRecursorStages
import RecursorComposition
import ConLeche.Verify.CheckerSplit
/-! Experimental #135 checkpoint. Checked generated recursor type and its definitional equality to the stream type.
See [measurement and scope report](../../docs/research/relative-and-root-checkpoint.md). -/
namespace AndGeneratedType
open AndRecursorStages ConLeche AcceptanceStages.Reference AndPositivityStages AndInstallation AndInstallationTail
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 8
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_fvar Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj CheckerReduction.depth_eq


checked_normal_form generated : ConstantVal := { AndRecursorType.recCv with type := (classGenRecTy g 0).getD (.sort .zero) }
checked_normal_form inferred : Except CheckError Expr := inferTypeCore .verified ctorEnv 32 0 generated.type
checked_normal_form u : Level := match inferred with | .ok (.sort u) => u | _ => .zero
measured_theorem infer_ok : inferTypeCore .verified ctorEnv 32 0 generated.type = .ok (.sort u) := inferred_eq
measured_theorem sort_ok : ensureSortCore .verified ctorEnv 32 0 (.sort u) = .ok u := by
  rw [ensureSortCore_eq, whnf_sort ctorEnv 30 0 u]
  rfl
checked_normal_form equalResult : Except CheckError Bool := isDefEqCore .verified ctorEnv 32 0 AndRecursorType.recCv.type generated.type
measured_theorem equal_ok : isDefEqCore .verified ctorEnv 32 0 AndRecursorType.recCv.type generated.type = .ok true := equalResult_eq
measured_theorem constant_ok : classConstOk (fueledOps .verified 32) (mkFEnv ctorEnv) generated = .ok () := by
  exact RecursorComposition.classConstOk_of_facts (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) infer_ok sort_ok
measured_theorem generated_ty : classGenRecTy g 0 = some generated.type := by cbv
measured_theorem recType_ok : classRecTyOk (fueledOps .verified 32) (mkFEnv ctorEnv) g q.p.k (q.p.recs.headD default) AndRecursorType.recCv 0 = .ok generated := by
  have h1 : ((q.p.recs.headD default).tgt == (g.cls.getD 0 default).member.getD q.p.k) = true := by cbv
  have h2 : ((q.p.recs.headD default).rP == g.nP + g.slots.length && (q.p.recs.headD default).mI == (q.p.recs.headD default).rP + (g.cls.getD 0 default).nIdx) = true := by cbv
  simp only [classRecTyOk, h1, h2, ↓reduceIte, generated_ty, unwrapOr, bind, Except.bind, pure, Except.pure]
  have hcv : { (q.p.recs.headD default).cvR with type := generated.type } = generated := by cbv
  rw [hcv, constant_ok]
  simp only [fueledOps_isDefEq, mkFEnv_env, equal_ok, ↓reduceIte]
measured_theorem types_ok : classRecTysOk (fueledOps .verified 32) (mkFEnv ctorEnv) g q.p.k q.p.recs [AndRecursorType.recCv] q.rd.recCls = .ok [generated] := by
  have hr : q.p.recs = [q.p.recs.headD default] := by cbv
  have hc : q.rd.recCls = [0] := by cbv
  rw [hr,hc]
  simp only [classRecTysOk, recType_ok, bind, Except.bind, pure, Except.pure]
end AndGeneratedType
#audit_graph_module
