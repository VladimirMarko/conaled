import CachedPending10Spine
import CachedDefeqComposition
/-! Experimental exact final Exists.intro argument conversion for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedPending10Equality
open ConLeche ConLeche.Cached CachedPending10Stages CachedPending10Spine
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
attribute [local cbv_eval] lazyDeltaReductionI.eq_1 lazyDeltaReductionI.eq_2 lazyDeltaProjReductionI.eq_1 lazyDeltaProjReductionI.eq_2
attribute [local cbv_eval] inferLamsI.eq_def inferPisI.eq_def betaPeelI.eq_def
attribute [local cbv_eval] whnfAppI.eq_def defeqLamsI_zero defeqLamsI_succ
attribute [local cbv_eval] Std.HashMap.size_emptyWithCapacity Std.HashMap.size_empty Std.HashMap.size_insert
attribute [local cbv_eval] push_mkFEnv
attribute [local cbv_eval] Expr.instantiate1C_spec Expr.instantiateListC_spec Expr.instSpineC_spec
def lhs := itype3
def rhs := dom3
def memo := imemo3
def leafCore := coreKnotI .verified fe 4611686018427387901
checked_normal_form quick : Except CheckError (Option Bool × CState) := quickDefEqI .verified leafCore 8 lhs rhs memo
checked_normal_form prop : Except CheckError (Bool × CState) := propIrrelI leafCore fe 8 lhs rhs memo
def propMemo := (prop.toOption.map Prod.snd).getD {}
checked_normal_form leftWhnf : Except CheckError (Expr × CState) := leafCore.whnfCore true 8 lhs propMemo
def leftMemo := (leftWhnf.toOption.map Prod.snd).getD {}
checked_normal_form rightWhnf : Except CheckError (Expr × CState) := leafCore.whnfCore true 8 rhs leftMemo
def rightMemo := (rightWhnf.toOption.map Prod.snd).getD {}
measured_theorem quick_ok : quickDefEqI .verified leafCore 8 lhs rhs memo = .ok (none,memo) := by rw [quick_eq]; rfl
measured_theorem prop_ok : propIrrelI leafCore fe 8 lhs rhs memo = .ok (false,propMemo) := by rw [prop_eq]; rfl
measured_theorem left_ok : leafCore.whnfCore true 8 lhs propMemo = .ok (lhs,leftMemo) := by rw [leftWhnf_eq]; rfl
measured_theorem right_ok : leafCore.whnfCore true 8 rhs leftMemo = .ok (lhs,rightMemo) := by rw [rightWhnf_eq]; rfl
measured_theorem body_ok : defeqBodyI .verified leafCore fe 8 lhs rhs memo = .ok (true,rightMemo) := by
  exact CachedDefeqComposition.beta_body .verified leafCore fe 8 lhs rhs lhs lhs
    memo memo propMemo leftMemo rightMemo rightMemo (by cbv) (by cbv)
    quick_ok prop_ok left_ok right_ok (by cbv)
def out : CState := {rightMemo with defeqC := rightMemo.defeqC.insert (lhs,rhs) true}
measured_theorem accepted : stepCore.defeq 8 lhs rhs memo = .ok (true,out) := by
  exact CachedDefeqComposition.miss .verified fe 4611686018427387901 8 lhs rhs memo rightMemo (by cbv) body_ok
end CachedPending10Equality
#audit_graph_module
