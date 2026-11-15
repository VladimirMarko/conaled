import AndInstallationTail
import ConLeche.Verify.CheckerSplit
/-! Experimental #135 checkpoint. Fixed-fuel acceptance of the actual stream recursor constant in the constructor environment.
See [measurement and scope report](../../docs/research/relative-and-root-checkpoint.md). -/
namespace AndRecursorType
open ConLeche AcceptanceStages.Reference AndPositivityStages AndInstallation AndInstallationTail
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 8
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_fvar Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj CheckerReduction.depth_eq


checked_normal_form recCv : ConstantVal := (q.p.recs.headD default).cvR
checked_normal_form inferred : Except CheckError Expr := inferTypeCore .verified ctorEnv 32 0 recCv.type
checked_normal_form u : Level := match inferred with | .ok (.sort u) => u | _ => .zero
measured_theorem infer_ok : inferTypeCore .verified ctorEnv 32 0 recCv.type = .ok (.sort u) := inferred_eq
measured_theorem sort_ok : ensureSortCore .verified ctorEnv 32 0 (.sort u) = .ok u := by
  rw [ensureSortCore_eq, whnf_sort ctorEnv 30 0 u]
  rfl
measured_theorem constant_ok : checkConstantVal (fueledOps .verified 32) ctorEnv recCv = .ok () := by
  exact checkConstantVal_of_facts (by cbv) (by cbv) (by cbv) (by cbv) (by cbv)
    (by cbv) (by cbv) infer_ok sort_ok
measured_theorem stream_ok : classStreamRecs (fueledOps .verified 32) (mkFEnv ctorEnv) q.p.recs = .ok [recCv] := by
  have hrs : q.p.recs = [q.p.recs.headD default] := by cbv
  rw [hrs]
  simp only [classStreamRecs, checkConstantValF_eq]
  change (do checkConstantVal (fueledOps .verified 32) ctorEnv recCv; pure [recCv]) = .ok [recCv]
  rw [constant_ok]
  rfl
end AndRecursorType
#audit_graph_module
