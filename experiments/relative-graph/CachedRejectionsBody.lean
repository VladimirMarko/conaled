import CachedInstantiationReduction
import ConLeche.Verify.Cached.DiscC5
/-! Experimental cached rejection of the actual forward record with a loose bound variable body in #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedRejectionsBody
open ConLeche ConLeche.Cached CachedFamilyInstallation
set_option acceptance.measureTreeSize false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 2000000
set_option pp.deepTerms.threshold 4
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj
attribute [local cbv_eval] whnfLoopI.eq_1 whnfLoopI.eq_2 whnfCoreLoopI.eq_1 whnfCoreLoopI.eq_2
attribute [local cbv_opaque] coreKnotI mkFEnv instListM defeqLamsI
attribute [local cbv_opaque] Std.HashMap.size
attribute [local cbv_eval] coreKnotI_infer_succ coreKnotI_whnf_succ coreKnotI_whnfCore_succ
attribute [local cbv_eval] CachedTransitionComposition.infer_pis_sort
attribute [local cbv_eval] CachedBinderComposition.pis_app CachedBinderComposition.pis_fvar
attribute [local cbv_eval] mkFEnv_find? mkFEnv_env coreKnotI_defeq_succ structWalkersC_eq_plain Expr.abstractRangeC_spec Expr.abstract1C_spec
attribute [local cbv_eval] Expr.instantiateRev_spec Expr.instLevelParams_spec Expr.instantiate1LiftC_spec Expr.getAppArgsC_spec Expr.wscopedBC_spec
attribute [local cbv_eval] Expr.allLevelParamsDefinedC_spec constsResolveFC_spec constsResolveF_eq
attribute [local cbv_eval] Expr.instantiate1C_spec Expr.instantiateListC_spec Expr.instSpineC_spec
attribute [local cbv_eval] lazyDeltaReductionI.eq_1 lazyDeltaReductionI.eq_2 lazyDeltaProjReductionI.eq_1 lazyDeltaProjReductionI.eq_2
attribute [local cbv_eval] inferLamsI.eq_def inferPisI.eq_def betaPeelI.eq_def
attribute [local cbv_eval] whnfAppI.eq_def defeqLamsI_zero defeqLamsI_succ
attribute [local cbv_eval] Std.HashMap.size_emptyWithCapacity Std.HashMap.size_empty Std.HashMap.size_insert
attribute [local cbv_eval] push_mkFEnv

def pc : PendingCheck := ⟨⟨.thm, EmittedForwardAcceptance.cv, .bvar 0⟩,12,18⟩
def decl : Declaration := .thmDecl EmittedForwardAcceptance.cv (.bvar 0)
measured_theorem installed : ∀ pend : Array PendingCheck,
  installDeclStep .verified [] (12,mkFEnv EmittedForwardAcceptance.before,pend) decl =
    .ok (13,mkFEnv EmittedForwardAcceptance.after,pend.push pc) := by
  intro pend
  cbv
measured_theorem rejected :
  checkPending .verified (mkFEnv EmittedForwardAcceptance.before) pc {} =
    .error (.invalid s!"loose bound variable in value of {EmittedForwardAcceptance.cv.name}") := by
  cbv
measured_theorem rejected_final :
  checkPending .verified (mkFEnv EmittedEnvironment.environment) pc {} =
    .error (.invalid s!"loose bound variable in value of {EmittedForwardAcceptance.cv.name}") := by
  rw [CachedPendingComposition.prefix_view EmittedForwardAcceptance.before pc
    (EmittedEnvironment.environment.consts.take 2) (by cbv) (by rfl) (by rfl)]
  exact rejected
end CachedRejectionsBody
#audit_graph_module
