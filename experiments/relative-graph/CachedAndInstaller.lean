import CachedAndConstructor
import ConLeche.Verify.Cached.TargetRecC
import ConLeche.Verify.Cached.WalkersC
import AndRecursorType
import CachedReductionEquations
import AndRecursorAcceptance
import AndInstallerAcceptance
import CachedAndTailStages
import CachedAndGenRec
import CachedTailComposition
/-! Experimental complete cached And block installer for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedAndInstaller
open ConLeche ConLeche.Cached CachedAndFormer
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
open AndInstallationTail

def indexedPass : BlockPass FEnv :=
  ⟨mkFEnv q.env₁,q.cvTas,q.p,q.ctorsAs,q.sortsss,q.kinds,q.nfs,q.params,q.rd,q.cls,q.tbl⟩

measured_theorem pass_identity : CachedAndPass.passResult = indexedPass := by
  unfold indexedPass
  rw [← q_eq]
  rfl

measured_theorem tables :
    checkBlockTablesF (m := CheckCM) structWalkersC q.p.toBlockShape
      (q.p.members.zip (q.ctorsAs.zip q.sortsss))
      (FEnv.pushAll (blockRecInfosTF (mkFEnv ctorEnv).find? q.p.toBlockShape 0 AndGeneratedRules.out)
        (mkFEnv ctorEnv)) {} = .ok (mkFEnv AndInstallation.andEnv,{}) := by
  rw [pushAll_blockRecInfosTF_mkFEnv]
  have hf : (mkFEnv ctorEnv).find? = ctorEnv.find? := by
    funext n
    exact mkFEnv_find? _ _
  rw [hf, AndInstallerAcceptance.recEnv_eq, structWalkersC_eq_plain]
  have hl : q.p.members.zip (q.ctorsAs.zip q.sortsss) =
      [(CachedAndPassStages.ctorMember,[(andIntroRaw.toConstantVal,2)],[[.zero,.zero]])] := by cbv
  have hi : CachedAndPassStages.ctorMember.nIdx = 0 := by cbv
  rw [hl]
  simp only [checkBlockTablesF, hi, BEq.rfl, ↓reduceIte]
  rw [checkStructProjTableF_pushC]
  cbv

measured_theorem tail :
    checkBlockTailS .verified andPin indexedPass CachedAndPositivity.c5 =
      .ok (mkFEnv AndInstallation.andEnv,{}) := by
  apply CachedTailComposition.tail (fe2 := mkFEnv ctorEnv) (out := AndGeneratedRules.out)
    (idxSorts := [[]]) (s1 := CachedAndPositivity.c5) (s2 := {}) (s3 := {})
  · exact CachedAndTailStages.idx_sorts _ _
  · exact CachedAndTailStages.constructor_env
  · exact CachedAndTailStages.constructor_flush
  · exact CachedAndGenRec.accepted
  · exact tables

measured_theorem block :
    checkBlockKS .verified (mkFEnv AcceptanceStages.equalityEnvironment) andPin
      AcceptanceStages.Reference.parts {} = .ok (mkFEnv AndInstallation.andEnv,{}) := by
  apply CachedTailComposition.block (q := indexedPass) (s1 := {}) (s2 := CachedAndPositivity.c5)
  · decide +kernel
  · rfl
  · have hp := CachedAndPass.pass
    rw [pass_identity] at hp
    have hr : blockRawRec AcceptanceStages.Reference.parts = false := by cbv
    rw [hr]
    exact hp
  · exact tail
measured_theorem install :
    installDeclStep .verified []
      (1, mkFEnv AcceptanceStages.equalityEnvironment, #[]) (.indDecl andPin 2) =
      .ok (2, mkFEnv AndInstallation.andEnv, #[]) := by
  have hg : andPinOk (.indDecl andPin 2) = true := by decide +kernel
  have hb : basisPinHit andPin = none := by cbv
  have hn : indParamsOk 2 andPin = true := by cbv
  have hp : blockParts? 2 andPin = some AcceptanceStages.Reference.parts := by cbv
  have hs : checkDeclStepC .verified [] (mkFEnv AcceptanceStages.equalityEnvironment)
      (.indDecl andPin 2) {} = .ok (mkFEnv AndInstallation.andEnv,{}) := by
    simp only [checkDeclStepC, checkDeclC, hb, hn, hp, ↓reduceIte]
    exact CachedTransitionComposition.bind_ok _ _ _ _ _ _ _ rfl block
  have hi : installStepC .verified [] 1 (mkFEnv AcceptanceStages.equalityEnvironment)
      #[] (.indDecl andPin 2) {} = .ok ((mkFEnv AndInstallation.andEnv,#[]),{}) := by
    exact CachedTransitionComposition.bind_ok _ _ _ _ _ _ _ hs rfl
  simp only [installDeclStep, hg, ↓reduceIte, hi]
end CachedAndInstaller
#audit_graph_module
