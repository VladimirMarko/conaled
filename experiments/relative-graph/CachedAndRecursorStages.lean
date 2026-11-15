import CachedAndConstructor
import AndRecursorType
import CachedAndRecursorType
import CachedReductionEquations
import AndGeneratedType
/-! Experimental cached And recursor-generator stages for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedAndRecursorStages
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

measured_theorem stream :
    classStreamRecs (sharedOpsC .verified (mkFEnv ctorEnv)) (mkFEnv ctorEnv) q.p.recs {} =
      .ok ([AndRecursorType.recCv],CachedAndRecursorType.finalMemo) := by
  have hrs : q.p.recs = [q.p.recs.headD default] := by cbv
  rw [hrs]
  unfold classStreamRecs
  refine CachedTransitionComposition.bind_ok _ _ {} CachedAndRecursorType.finalMemo
    CachedAndRecursorType.finalMemo () _ CachedAndRecursorType.constant ?_
  rfl

checked_normal_form nfsRun : Except CheckError (List TargetMajor × CState) :=
    classesNfs (sharedOpsC .verified (mkFEnv ctorEnv)) ctorEnv q.p.toBlockShape
      (q.cvTas.map (·.type)) q.tbl.toList q.cls CachedAndRecursorType.finalMemo
def nfsMemo := (nfsRun.toOption.getD default).2
measured_theorem nfs_ok :
    classesNfs (sharedOpsC .verified (mkFEnv ctorEnv)) ctorEnv q.p.toBlockShape
      (q.cvTas.map (·.type)) q.tbl.toList q.cls CachedAndRecursorType.finalMemo = .ok (Ms,nfsMemo) := by
  rw [nfsRun_eq]
  rfl

checked_normal_form ctorsRun : Except CheckError (List (List ClassCtor) × CState) :=
    classesCtors (sharedOpsC .verified (mkFEnv ctorEnv)) ctorEnv q.p.toBlockShape
      (q.cvTas.map (·.type)) q.rd Ms 0 Ms nfsMemo
def ctorsMemo := (ctorsRun.toOption.getD default).2
measured_theorem ctors_ok :
    classesCtors (sharedOpsC .verified (mkFEnv ctorEnv)) ctorEnv q.p.toBlockShape
      (q.cvTas.map (·.type)) q.rd Ms 0 Ms nfsMemo = .ok (ctors,ctorsMemo) := by
  rw [ctorsRun_eq]
  rfl

checked_normal_form typesRun : Except CheckError (List ConstantVal × CState) :=
    classRecTysOk (sharedOpsC .verified (mkFEnv ctorEnv)) (mkFEnv ctorEnv)
      g q.p.k q.p.recs [AndRecursorType.recCv] q.rd.recCls ctorsMemo
def typesMemo := (typesRun.toOption.getD default).2
measured_theorem types_ok :
    classRecTysOk (sharedOpsC .verified (mkFEnv ctorEnv)) (mkFEnv ctorEnv)
      g q.p.k q.p.recs [AndRecursorType.recCv] q.rd.recCls ctorsMemo = .ok ([generated],typesMemo) := by
  rw [typesRun_eq]
  rfl

end CachedAndRecursorStages
#audit_graph_module
