import CachedPending10Equality
import CachedLambdaComposition
/-! Experimental actual backward introduction-spine composition for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedPending10SpineJoin
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
def acc4 := acc3.push arg3
checked_normal_form result : Expr := ty4.instantiateRev acc4
def finalMemo := CachedPending10Equality.out
measured_theorem tail4 : inferSpineI stepCore fe 8 ty4 acc4 [] finalMemo = .ok (result,finalMemo) := by cbv
def rawDom3 := match ty3 with | .forallE a _ => a | _ => .bvar 0
measured_theorem tail3 : inferSpineI stepCore fe 8 ty3 acc3 (args.drop 3) s3 = .ok (result,finalMemo) := by
  change inferSpineI stepCore fe 8 (.forallE rawDom3 ty4) acc3 (arg3 :: args.drop 4) s3 = _
  apply CachedBinderComposition.spine_step stepCore fe 8 rawDom3 ty4 dom3 arg3 itype3 result acc3 (args.drop 4) s3 s3 imemo3 finalMemo finalMemo
  · cbv
  · rw [infer3_eq]; rfl
  · exact CachedPending10Equality.accepted
  · exact tail4
def rawDom2 := match ty2 with | .forallE a _ => a | _ => .bvar 0
measured_theorem tail2 : inferSpineI stepCore fe 8 ty2 acc2 (args.drop 2) s2 = .ok (result,finalMemo) := by
  change inferSpineI stepCore fe 8 (.forallE rawDom2 ty3) acc2 (arg2 :: args.drop 3) s2 = _
  apply CachedBinderComposition.spine_step stepCore fe 8 rawDom2 ty3 dom2 arg2 itype2 result acc2 (args.drop 3) s2 s2 imemo2 s3 finalMemo
  · cbv
  · rw [infer2_eq]; rfl
  · rw [equal2_eq]; rfl
  · exact tail3
def rawDom1 := match ty1 with | .forallE a _ => a | _ => .bvar 0
measured_theorem tail1 : inferSpineI stepCore fe 8 ty1 acc1 (args.drop 1) s1 = .ok (result,finalMemo) := by
  change inferSpineI stepCore fe 8 (.forallE rawDom1 ty2) acc1 (arg1 :: args.drop 2) s1 = _
  apply CachedBinderComposition.spine_step stepCore fe 8 rawDom1 ty2 dom1 arg1 itype1 result acc1 (args.drop 2) s1 s1 imemo1 s2 finalMemo
  · cbv
  · rw [infer1_eq]; rfl
  · rw [equal1_eq]; rfl
  · exact tail2
def rawDom0 := match ty0 with | .forallE a _ => a | _ => .bvar 0
measured_theorem tail0 : inferSpineI stepCore fe 8 ty0 acc0 (args.drop 0) s0 = .ok (result,finalMemo) := by
  change inferSpineI stepCore fe 8 (.forallE rawDom0 ty1) acc0 (arg0 :: args.drop 1) s0 = _
  apply CachedBinderComposition.spine_step stepCore fe 8 rawDom0 ty1 dom0 arg0 itype0 result acc0 (args.drop 1) s0 s0 imemo0 s1 finalMemo
  · cbv
  · rw [infer0_eq]; rfl
  · rw [equal0_eq]; rfl
  · exact tail1
def appFn := match CachedPending10Open.opened with | .app a _ => a | _ => .bvar 0
def appArg := match CachedPending10Open.opened with | .app _ b => b | _ => .bvar 0
measured_theorem app_body : inferBodyI stepCore fe 8 CachedPending10Open.opened CachedPending10Open.state8 = .ok (result,finalMemo) := by
  change inferBodyI stepCore fe 8 (.app appFn appArg) CachedPending10Open.state8 = _
  exact CachedBinderComposition.app_body stepCore fe 8 appFn appArg head ty0 result args
    CachedPending10Open.state8 s0 finalMemo (by cbv) (by cbv) (by rw [headRun_eq]; rfl) tail0
def leafMemo : CState := {finalMemo with inferC := finalMemo.inferC.insert CachedPending10Open.opened result}
measured_theorem leaf : CachedPending10Open.lower.infer 8 CachedPending10Open.opened CachedPending10Open.state8 = .ok (result,leafMemo) := by
  exact CachedLambdaComposition.infer_miss .verified fe 4611686018427387902 8 CachedPending10Open.opened result CachedPending10Open.state8 finalMemo (by cbv) app_body
end CachedPending10SpineJoin
#audit_graph_module
