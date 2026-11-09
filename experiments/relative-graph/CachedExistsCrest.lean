import CachedExistsStages
import ExistsRoot
/-! Experimental cached Exists positivity crest for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedExistsCrest
open ConLeche ConLeche.Cached GraphEnvironment AndInstallation
open ExistsPassStages ExistsPositivity CachedExistsStages
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
checked_normal_form inferRun : Except CheckError (Expr × CState) :=
  (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).infer 3 crest ctorMemo
def inferred := (inferRun.toOption.map Prod.fst).getD (.sort .zero)
def u : Level := match inferred with | .sort l => l | _ => .zero
def inferMemo := (inferRun.toOption.map Prod.snd).getD {}
measured_theorem infer_ok :
  (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).infer 3 crest ctorMemo =
    .ok (.sort u,inferMemo) := by rw [inferRun_eq]; rfl
checked_normal_form sortRun : Except CheckError (Level × CState) :=
  ensureSortI (coreKnotI .verified (mkFEnv indsResult.1) checkFuel) 3 (.sort u) inferMemo
def sortMemo := (sortRun.toOption.map Prod.snd).getD {}
measured_theorem sort_ok :
  ensureSortI (coreKnotI .verified (mkFEnv indsResult.1) checkFuel) 3 (.sort u) inferMemo =
    .ok (u,sortMemo) := by rw [sortRun_eq]; rfl
checked_normal_form firstRun : Except CheckError (Expr × CState) :=
  (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).whnf 3 A sortMemo
def firstMemo := (firstRun.toOption.map Prod.snd).getD {}
measured_theorem first_whnf :
  (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).whnf 3 A sortMemo =
    .ok (A,firstMemo) := by rw [firstRun_eq]; rfl
checked_normal_form secondRun : Except CheckError (Expr × CState) :=
  (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).whnf 4 second firstMemo
def fieldsMemo := (secondRun.toOption.map Prod.snd).getD {}
measured_theorem second_whnf :
  (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).whnf 4 second firstMemo =
    .ok (second,fieldsMemo) := by rw [secondRun_eq]; rfl
measured_theorem fields : ∀ err : CheckError,
  nestFields (nestPos (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1 ctx
    (whnfWalkFuel crest)) [] 3 err 2 0 crest {} sortMemo =
    .ok (([.ordinary,.ordinary],[A,second],res,{}),fieldsMemo) := by
  intro err
  rw [ExistsPositivity.walkFuel_eq]
  change nestFields (nestPos (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1 ctx 1028)
    [] 3 err 2 0 (.forallE A (.forallE (.app P (.bvar 0)) res)) {} sortMemo = _
  apply CachedPositivityComposition.fields_step (st1 := {}) (s1 := firstMemo)
    (k := .ordinary) (nb := A)
  · apply CachedPositivityComposition.ordinary
    · cbv
    · exact first_whnf
  · change nestFields (nestPos (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1 ctx 1028)
      [] 3 err 1 1 (.forallE second res) {} firstMemo = _
    apply CachedPositivityComposition.fields_step (st1 := {}) (s1 := fieldsMemo)
      (k := .ordinary) (nb := second)
    · apply CachedPositivityComposition.ordinary
      · cbv
      · exact second_whnf
    · rfl
end CachedExistsCrest
#audit_graph_module
