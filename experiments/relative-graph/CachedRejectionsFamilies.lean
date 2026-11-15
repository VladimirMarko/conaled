import CachedRejectionsBody
import CachedRejectionsType
import CachedRejectionsMissing
import CachedRejectionsPrefix
import ConLeche.Verify.Cached.DiscC5
/-! Experimental installation of three malformed canonical families in #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedRejectionsFamilies
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

def bodyDeclarations : List Declaration := GraphEnvironment.declarations.toList ++
  EmittedEnvironment.helpers.take 9 ++ [CachedRejectionsBody.decl, EmittedBackwardAcceptance.decl]
def bodyEnv : Env := ⟨.thmInfo EmittedBackwardAcceptance.cv :: EmittedForwardAcceptance.after.consts, EmittedForwardAcceptance.after.tables⟩
def bodyLast : PendingCheck := ⟨⟨.thm, EmittedBackwardAcceptance.cv, EmittedBackwardAcceptance.value⟩,13,19⟩
def bodyPend : Array PendingCheck := #[pc0, pc1, pc2, pc3, pc4, pc5, pc6, pc7, pc8, CachedRejectionsBody.pc, bodyLast]
measured_theorem bodyLast_installed : ∀ pend : Array PendingCheck,
  installDeclStep .verified [] (13,mkFEnv EmittedForwardAcceptance.after,pend) EmittedBackwardAcceptance.decl =
    .ok (14,mkFEnv bodyEnv,pend.push bodyLast) := by
  intro pend
  cbv
measured_theorem bodyRun : InstallRun .verified [] bodyDeclarations (0,mkFEnv Env.empty,#[])
    (14,mkFEnv bodyEnv,bodyPend) := by
  unfold bodyDeclarations
  rw [EmittedAcceptance.helper_list]
  change InstallRun .verified [] (_ :: _ :: _ :: _) _ _
  refine .cons AcceptanceStages.equalityInstall ?_
  refine .cons CachedAndInstaller.install ?_
  refine .cons CachedExistsInstaller.install ?_
  refine .cons (step0 _) ?_
  refine .cons (step1 _) ?_
  refine .cons (step2 _) ?_
  refine .cons (step3 _) ?_
  refine .cons (step4 _) ?_
  refine .cons (step5 _) ?_
  refine .cons (step6 _) ?_
  refine .cons (step7 _) ?_
  refine .cons (step8 _) ?_
  refine .cons (CachedRejectionsBody.installed _) ?_
  refine .cons (bodyLast_installed _) ?_
  exact .nil _
measured_theorem bodyNames : NodupNames bodyEnv := by
  unfold NodupNames
  decide +kernel
measured_theorem bodyRejected_final :
  checkPending .verified (mkFEnv bodyEnv) CachedRejectionsBody.pc {} =
    .error (.invalid s!"loose bound variable in value of {EmittedForwardAcceptance.cv.name}") := by
  rw [CachedRejectionsPrefix.prefix_view bodyEnv EmittedForwardAcceptance.before CachedRejectionsBody.pc
    (bodyEnv.consts.take 2) bodyNames (by cbv) (by rfl) (by rfl)]
  exact CachedRejectionsBody.rejected

def typeDeclarations : List Declaration := GraphEnvironment.declarations.toList ++
  EmittedEnvironment.helpers.take 9 ++ [CachedRejectionsType.decl, EmittedBackwardAcceptance.decl]
def typeEnv : Env := ⟨.thmInfo EmittedBackwardAcceptance.cv :: CachedRejectionsType.after.consts, CachedRejectionsType.after.tables⟩
def typeLast : PendingCheck := ⟨⟨.thm, EmittedBackwardAcceptance.cv, EmittedBackwardAcceptance.value⟩,13,19⟩
def typePend : Array PendingCheck := #[pc0, pc1, pc2, pc3, pc4, pc5, pc6, pc7, pc8, CachedRejectionsType.pc, typeLast]
measured_theorem typeLast_installed : ∀ pend : Array PendingCheck,
  installDeclStep .verified [] (13,mkFEnv CachedRejectionsType.after,pend) EmittedBackwardAcceptance.decl =
    .ok (14,mkFEnv typeEnv,pend.push typeLast) := by
  intro pend
  cbv
measured_theorem typeRun : InstallRun .verified [] typeDeclarations (0,mkFEnv Env.empty,#[])
    (14,mkFEnv typeEnv,typePend) := by
  unfold typeDeclarations
  rw [EmittedAcceptance.helper_list]
  change InstallRun .verified [] (_ :: _ :: _ :: _) _ _
  refine .cons AcceptanceStages.equalityInstall ?_
  refine .cons CachedAndInstaller.install ?_
  refine .cons CachedExistsInstaller.install ?_
  refine .cons (step0 _) ?_
  refine .cons (step1 _) ?_
  refine .cons (step2 _) ?_
  refine .cons (step3 _) ?_
  refine .cons (step4 _) ?_
  refine .cons (step5 _) ?_
  refine .cons (step6 _) ?_
  refine .cons (step7 _) ?_
  refine .cons (step8 _) ?_
  refine .cons (CachedRejectionsType.installed _) ?_
  refine .cons (typeLast_installed _) ?_
  exact .nil _
measured_theorem typeNames : NodupNames typeEnv := by
  unfold NodupNames
  decide +kernel
measured_theorem typeRejected_final :
  checkPending .verified (mkFEnv typeEnv) CachedRejectionsType.pc {} =
    .error (.invalid s!"type of theorem {CachedRejectionsType.cv.name} is not a proposition") := by
  rw [CachedRejectionsPrefix.prefix_view typeEnv EmittedForwardAcceptance.before CachedRejectionsType.pc
    (typeEnv.consts.take 2) typeNames (by cbv) (by rfl) (by rfl)]
  exact CachedRejectionsType.rejected

def missingDeclarations : List Declaration := GraphEnvironment.declarations.toList ++
  EmittedEnvironment.helpers.take 8 ++ [EmittedForwardAcceptance.decl, EmittedBackwardAcceptance.decl]
def missingEnv : Env := ⟨.thmInfo EmittedBackwardAcceptance.cv :: CachedRejectionsMissing.after.consts, CachedRejectionsMissing.after.tables⟩
def missingLast : PendingCheck := ⟨⟨.thm, EmittedBackwardAcceptance.cv, EmittedBackwardAcceptance.value⟩,12,18⟩
def missingPend : Array PendingCheck := #[pc0, pc1, pc2, pc3, pc4, pc5, pc6, pc7, CachedRejectionsMissing.pc, missingLast]
measured_theorem missingLast_installed : ∀ pend : Array PendingCheck,
  installDeclStep .verified [] (12,mkFEnv CachedRejectionsMissing.after,pend) EmittedBackwardAcceptance.decl =
    .ok (13,mkFEnv missingEnv,pend.push missingLast) := by
  intro pend
  cbv
measured_theorem missingRun : InstallRun .verified [] missingDeclarations (0,mkFEnv Env.empty,#[])
    (13,mkFEnv missingEnv,missingPend) := by
  unfold missingDeclarations
  rw [EmittedAcceptance.helper_list]
  change InstallRun .verified [] (_ :: _ :: _ :: _) _ _
  refine .cons AcceptanceStages.equalityInstall ?_
  refine .cons CachedAndInstaller.install ?_
  refine .cons CachedExistsInstaller.install ?_
  refine .cons (step0 _) ?_
  refine .cons (step1 _) ?_
  refine .cons (step2 _) ?_
  refine .cons (step3 _) ?_
  refine .cons (step4 _) ?_
  refine .cons (step5 _) ?_
  refine .cons (step6 _) ?_
  refine .cons (step7 _) ?_
  refine .cons (CachedRejectionsMissing.installed _) ?_
  refine .cons (missingLast_installed _) ?_
  exact .nil _
measured_theorem missingNames : NodupNames missingEnv := by
  unfold NodupNames
  decide +kernel
measured_theorem missingRejected_final :
  checkPending .verified (mkFEnv missingEnv) CachedRejectionsMissing.pc {} =
    .error CachedRejectionsMissing.error := by
  rw [CachedRejectionsPrefix.prefix_view missingEnv CachedRejectionsMissing.before CachedRejectionsMissing.pc
    (missingEnv.consts.take 2) missingNames (by cbv) (by rfl) (by rfl)]
  exact CachedRejectionsMissing.rejected
measured_theorem body_source : bodyDeclarations = EmittedEnvironment.declarations.set 12 CachedRejectionsBody.decl := by cbv
measured_theorem type_source : typeDeclarations = EmittedEnvironment.declarations.set 12 CachedRejectionsType.decl := by cbv
measured_theorem missing_source : missingDeclarations = EmittedEnvironment.declarations.take 11 ++ EmittedEnvironment.declarations.drop 12 := by cbv
end CachedRejectionsFamilies
#audit_graph_module
