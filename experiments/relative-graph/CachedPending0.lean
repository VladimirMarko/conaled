import CachedPendingComposition
/-! Experimental actual cached pending check for native rfl in #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedPending0
open ConLeche ConLeche.Cached CachedFamilyInstallation
set_option acceptance.measureTreeSize false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 2000000
set_option pp.deepTerms.threshold 4
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj
attribute [local cbv_eval] whnfLoopI.eq_1 whnfLoopI.eq_2 whnfCoreLoopI.eq_1 whnfCoreLoopI.eq_2
attribute [local cbv_opaque] coreKnotI mkFEnv
attribute [local cbv_eval] coreKnotI_infer_succ coreKnotI_whnf_succ coreKnotI_whnfCore_succ
attribute [local cbv_eval] CachedTransitionComposition.infer_pis_sort
attribute [local cbv_eval] CachedBinderComposition.pis_app CachedBinderComposition.pis_fvar
attribute [local cbv_eval] mkFEnv_find? mkFEnv_env coreKnotI_defeq_succ structWalkersC_eq_plain Expr.abstractRangeC_spec Expr.abstract1C_spec
attribute [local cbv_eval] Expr.instantiateRev_spec Expr.instLevelParams_spec Expr.instantiate1LiftC_spec Expr.getAppArgsC_spec Expr.wscopedBC_spec
attribute [local cbv_eval] Expr.allLevelParamsDefinedC_spec constsResolveFC_spec constsResolveF_eq
attribute [local cbv_eval] push_mkFEnv
checked_normal_form result : Except CheckError (Unit × CState) :=
  checkPending .verified (mkFEnv NativeHelper0.before) pc0 {}
def memo := (result.toOption.map Prod.snd).getD {}
measured_theorem accepted : checkPending .verified (mkFEnv NativeHelper0.before) pc0 {} =
    .ok ((),memo) := by rw [result_eq]; rfl
measured_theorem accepted_final :
  checkPending .verified (mkFEnv EmittedEnvironment.environment) pc0 {} = .ok ((),memo) := by
  rw [CachedPendingComposition.prefix_view NativeHelper0.before pc0
    (EmittedEnvironment.environment.consts.take 11) (by cbv) (by rfl) (by rfl)]
  exact accepted
end CachedPending0
#audit_graph_module
