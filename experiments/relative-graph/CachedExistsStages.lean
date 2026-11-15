import CachedAndInstaller
import ExistsPassStages
/-! Experimental cached Exists initial stages for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedExistsStages
open ConLeche ConLeche.Cached GraphEnvironment AndInstallation
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
checked_normal_form formerResult : Except CheckError ((FEnv × List ConstantVal × BlockShape) × CState) :=
  checkBlockIndsF (sharedOpsC .verified (mkFEnv andEnv)) (mkFEnv andEnv) ExistsPassStages.parts false {}
def formerMemo := (formerResult.toOption.map Prod.snd).getD {}
measured_theorem former :
    checkBlockIndsF (sharedOpsC .verified (mkFEnv andEnv)) (mkFEnv andEnv) ExistsPassStages.parts false {} =
    .ok ((mkFEnv ExistsPassStages.indsResult.1, ExistsPassStages.indsResult.2),formerMemo) := by
  rw [formerResult_eq]
  rfl
def afterFormer := formerMemo.flushed
measured_theorem former_flush : flushC formerMemo = .ok ((),afterFormer) := rfl
checked_normal_form ctorRun : Except CheckError ((List (List (ConstantVal × Nat)) × List (List (List Level))) × CState) :=
  checkBlockCtorsF (sharedOpsC .verified (mkFEnv ExistsPassStages.indsResult.1))
    (mkFEnv ExistsPassStages.indsResult.1) (mkFEnv ExistsPassStages.indsResult.1)
    ExistsPassStages.completed.toBlockShape
    (ExistsPassStages.completed.members.zip ExistsPassStages.indsResult.2.1) afterFormer
def ctorMemo := (ctorRun.toOption.map Prod.snd).getD {}
measured_theorem constructors :
  checkBlockCtorsF (sharedOpsC .verified (mkFEnv ExistsPassStages.indsResult.1))
    (mkFEnv ExistsPassStages.indsResult.1) (mkFEnv ExistsPassStages.indsResult.1)
    ExistsPassStages.completed.toBlockShape
    (ExistsPassStages.completed.members.zip ExistsPassStages.indsResult.2.1) afterFormer =
    .ok (ExistsPassStages.ctorResult,ctorMemo) := by
  rw [ctorRun_eq]
  rfl
end CachedExistsStages
#audit_graph_module
