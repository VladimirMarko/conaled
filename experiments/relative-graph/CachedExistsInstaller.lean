import CachedExistsPass
import ConLeche.Verify.Cached.TargetRecC
import ConLeche.Verify.Cached.WalkersC
import ExistsRecursorType
import CachedReductionEquations
import ExistsRecursorAcceptance
import ExistsInstallerAcceptance
import CachedExistsTailStages
import CachedExistsGenRec
import CachedTailComposition
/-! Experimental complete cached Exists block installer for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedExistsInstaller
open ConLeche ConLeche.Cached
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
attribute [local cbv_eval] mkFEnv_find? mkFEnv_env coreKnotI_defeq_succ structWalkersC_eq_plain Expr.abstractRangeC_spec Expr.abstract1C_spec pushAll_blockRecInfosTF_mkFEnv checkStructProjTableF_pushC
open ExistsInstallationTail

def indexedPass : BlockPass FEnv :=
  ⟨mkFEnv q.env₁,q.cvTas,q.p,q.ctorsAs,q.sortsss,q.kinds,q.nfs,q.params,q.rd,q.cls,q.tbl⟩

measured_theorem pass_identity : CachedExistsPass.indexedPass = indexedPass := by
  unfold indexedPass
  rw [← q_eq]
  rfl

measured_theorem tables :
    checkBlockTablesF (m := CheckCM) structWalkersC q.p.toBlockShape
      (q.p.members.zip (q.ctorsAs.zip q.sortsss))
      (FEnv.pushAll (blockRecInfosTF (mkFEnv ctorEnv).find? q.p.toBlockShape 0 ExistsGeneratedRules.out)
        (mkFEnv ctorEnv)) CachedExistsGenRec.memo = .ok (mkFEnv GraphEnvironment.environment,CachedExistsGenRec.memo) := by
  rw [pushAll_blockRecInfosTF_mkFEnv]
  have hf : (mkFEnv ctorEnv).find? = ctorEnv.find? := by
    funext n
    exact mkFEnv_find? _ _
  rw [hf, ExistsInstallerAcceptance.recEnv_eq, structWalkersC_eq_plain]
  have hl : q.p.members.zip (q.ctorsAs.zip q.sortsss) =
      [((q.p.members.headD default),[(GraphEnvironment.existsIntroRaw.toConstantVal,2)],[[BasisDSL.u, .zero]])] := by cbv
  have hi : (q.p.members.headD default).nIdx = 0 := by cbv
  rw [hl]
  simp only [checkBlockTablesF, hi, BEq.rfl, ↓reduceIte]
  rw [checkStructProjTableF_pushC]
  cbv

measured_theorem tail :
    checkBlockTailS .verified GraphEnvironment.existsBlock indexedPass CachedExistsPass.posMemo =
      .ok (mkFEnv GraphEnvironment.environment,CachedExistsGenRec.memo) := by
  apply CachedTailComposition.tail (fe2 := mkFEnv ctorEnv) (out := ExistsGeneratedRules.out)
    (idxSorts := [[]]) (s1 := CachedExistsPass.posMemo) (s2 := CachedExistsPass.posMemo.flushed) (s3 := CachedExistsGenRec.memo)
  · exact CachedExistsTailStages.idx_sorts _ _
  · exact CachedExistsTailStages.constructor_env
  · exact CachedExistsTailStages.constructor_flush
  · exact CachedExistsGenRec.accepted
  · exact tables

measured_theorem block :
    checkBlockKS .verified (mkFEnv AndInstallation.andEnv) GraphEnvironment.existsBlock
      ExistsPassStages.parts {} = .ok (mkFEnv GraphEnvironment.environment,CachedExistsGenRec.memo) := by
  apply CachedTailComposition.block (q := indexedPass) (s1 := {}) (s2 := CachedExistsPass.posMemo)
  · decide +kernel
  · rfl
  · have hp := CachedExistsPass.pass
    rw [pass_identity] at hp
    have hr : blockRawRec ExistsPassStages.parts = false := by cbv
    rw [hr]
    exact hp
  · exact tail
measured_theorem install :
    installDeclStep .verified []
      (2, mkFEnv AndInstallation.andEnv, #[]) (.indDecl GraphEnvironment.existsBlock 2) =
      .ok (3, mkFEnv GraphEnvironment.environment, #[]) := by
  have hg : andPinOk (.indDecl GraphEnvironment.existsBlock 2) = true := by decide +kernel
  have hb : basisPinHit GraphEnvironment.existsBlock = none := by cbv
  have hn : indParamsOk 2 GraphEnvironment.existsBlock = true := by cbv
  have hp : blockParts? 2 GraphEnvironment.existsBlock = some ExistsPassStages.parts := by cbv
  have hs : checkDeclStepC .verified [] (mkFEnv AndInstallation.andEnv)
      (.indDecl GraphEnvironment.existsBlock 2) {} = .ok (mkFEnv GraphEnvironment.environment,CachedExistsGenRec.memo) := by
    simp only [checkDeclStepC, checkDeclC, hb, hn, hp, ↓reduceIte]
    exact CachedTransitionComposition.bind_ok _ _ _ _ _ _ _ rfl block
  have hi : installStepC .verified [] 2 (mkFEnv AndInstallation.andEnv)
      #[] (.indDecl GraphEnvironment.existsBlock 2) {} = .ok ((mkFEnv GraphEnvironment.environment,#[]),CachedExistsGenRec.memo) := by
    exact CachedTransitionComposition.bind_ok _ _ _ _ _ _ _ hs rfl
  simp only [installDeclStep, hg, ↓reduceIte, hi]
end CachedExistsInstaller
#audit_graph_module
