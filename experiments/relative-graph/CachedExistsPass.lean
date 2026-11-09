import CachedExistsCrest
import ExistsInstallation
/-! Experimental cached Exists pass for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedExistsPass
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
open ExistsPassStages ExistsInstallation CachedExistsStages
measured_theorem context : ∀ s : CState,
  blockNestCtx (m := CheckCM) completed.toBlockShape indsResult.2.1
    (mkFEnv indsResult.1).find? s = .ok ((ctx,holes),s) := by
  intro s
  have hf : (mkFEnv indsResult.1).find? = indsResult.1.find? := by
    funext n; exact mkFEnv_find? _ _
  rw [hf]
  cbv
measured_theorem classes : ∀ s : CState,
  checkBlockClasses (sharedOpsC .verified (mkFEnv indsResult.1)) (mkFEnv indsResult.1)
    completed.toBlockShape ctx.params ctorResult.1 s = .ok (ExistsInstallation.classes,s) := by
  intro s
  cbv
open ExistsPositivity CachedExistsCrest
measured_theorem constructors_root :
    nestCtors ctx (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1
      (fun e => nestPos (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1 ctx (whnfWalkFuel e))
      [] (ctx.hiAt 0) (ctx.lps.map Level.param) ctx.params ctx.names holes
      [(existsIntroRaw.toConstantVal,2)] {} ctorMemo =
        .ok (([([.ordinary,.ordinary],crest)],ExistsRoot.post),fieldsMemo) := by
  have hi : ctx.hiAt 0 = 3 := by cbv
  rw [hi]
  have h := CachedPositivityComposition.ctors_one ctx
    (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1
    (fun e => nestPos (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1 ctx (whnfWalkFuel e))
    [] 3 (ctx.lps.map Level.param) ctx.params ctx.names holes existsIntroRaw.toConstantVal 2
    {} {} crest (.sort CachedExistsCrest.u) CachedExistsCrest.u
    [.ordinary,.ordinary] [A,second] res ctorMemo inferMemo sortMemo fieldsMemo
    (by cbv) ExistsRoot.crest_ok infer_ok sort_ok fields (by cbv) (by cbv)
  rw [ExistsRoot.close_ok] at h
  exact h
measured_theorem root :
  nestRoot (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1 ctx holes ctorResult.1 {} ctorMemo =
    .ok (ExistsRoot.rootResult,fieldsMemo) := by
  exact CachedPositivityComposition.root_one _ _ _ _ _ _ _ _ _ _ constructors_root
checked_normal_form absRun : Except CheckError (Unit × CState) :=
  checkAbsCtorSortsAll (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1 ctx
    ctorResult.1 ExistsRoot.rootResult.1 fieldsMemo
def posMemo := (absRun.toOption.map Prod.snd).getD {}
measured_theorem absSorts :
  checkAbsCtorSortsAll (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1 ctx
    ctorResult.1 ExistsRoot.rootResult.1 fieldsMemo = .ok ((),posMemo) := by
  rw [absRun_eq]; rfl
measured_theorem positivity :
  checkBlockPositivity (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1
    (mkFEnv indsResult.1).find? completed indsResult.2.1 ctorResult.1 ctorMemo =
    .ok (ExistsInstallation.posResult,posMemo) := by
  apply CachedPositivityComposition.block_positivity (ctx := ctx) (holes := holes)
    (outs := ExistsRoot.rootResult.1) (st := ExistsRoot.rootResult.2)
    (s1 := ctorMemo) (s2 := ctorMemo) (s3 := fieldsMemo)
  · exact context ctorMemo
  · cbv
  · exact root
  · exact absSorts
measured_theorem seeds : ∀ s : CState,
  nestSeeds (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1 ctx
    (classSeeds ctx holes ExistsInstallation.classes.2) ExistsInstallation.posResult.2.2 s =
    .ok (ExistsInstallation.posResult.2.2,s) := by
  intro s
  have he : classSeeds ctx holes ExistsInstallation.classes.2 = [] := by cbv
  rw [he]; rfl

def indexedPass : BlockPass FEnv :=
  ⟨mkFEnv indsResult.1,indsResult.2.1,completed,ctorResult.1,ctorResult.2,
    ExistsInstallation.posResult.1,ExistsInstallation.posResult.2.1,ctx.params,
    ExistsInstallation.classes.1,ExistsInstallation.classes.2,ExistsInstallation.posResult.2.2.ctorNfs⟩
measured_theorem pass :
  checkBlockPassS .verified (mkFEnv andEnv) parts false {} = .ok (indexedPass,posMemo) := by
  exact CachedPassComposition.pass .verified _ _ parts false indsResult.2.1 indsResult.2.2
    ctorResult.1 ctorResult.2 ctx holes ExistsInstallation.classes.1 ExistsInstallation.classes.2
    ExistsInstallation.posResult.1 ExistsInstallation.posResult.2.1
    ExistsInstallation.posResult.2.2 ExistsInstallation.posResult.2.2
    {} formerMemo afterFormer ctorMemo ctorMemo ctorMemo posMemo posMemo
    former former_flush constructors (context ctorMemo) (classes ctorMemo) positivity (seeds posMemo)
end CachedExistsPass
#audit_graph_module
