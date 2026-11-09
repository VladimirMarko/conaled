import CachedAndConstructor
import AndRecursorType
import CachedAndRecursorType
import CachedAndRecursorStages
import CachedReductionEquations
import AndGeneratedType
/-! Experimental cached And generated-rule inputs for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedAndRuleInput
open ConLeche ConLeche.Cached CachedAndFormer
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 4
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj
attribute [local cbv_eval] whnfLoopI.eq_1 whnfLoopI.eq_2 whnfCoreLoopI.eq_1 whnfCoreLoopI.eq_2
attribute [local cbv_opaque] coreKnotI mkFEnv
attribute [local cbv_eval] coreKnotI_infer_succ coreKnotI_whnf_succ coreKnotI_whnfCore_succ
attribute [local cbv_eval] CachedTransitionComposition.infer_pis_sort
attribute [local cbv_eval] CachedBinderComposition.pis_app CachedBinderComposition.pis_fvar
attribute [local cbv_eval] mkFEnv_find? coreKnotI_defeq_succ
open AndInstallationTail AndRecursorStages AndGeneratedType
attribute [local cbv_eval] mkFEnv_env


checked_normal_form ruleFe : FEnv := classFeROvl q.p.toBlockShape Ms [generated] q.rd.recCls (mkFEnv ctorEnv)
checked_normal_form gen : Expr := (classGenRule g (classRecOf q.rd.recCls [generated])
    (generated.levelParams.map .param) 0 ((ctors.headD []).headD default)).getD (.bvar 0)
measured_theorem generated_rule : classGenRule g (classRecOf q.rd.recCls [generated])
    (generated.levelParams.map .param) 0 ((ctors.headD []).headD default) = some gen := by cbv
measured_theorem prefix_flush : flushC CachedAndRecursorStages.typesMemo = .ok ((),{}) := by rfl

end CachedAndRuleInput
#audit_graph_module
