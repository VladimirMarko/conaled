import CachedInstantiationReduction
import ConLeche.Verify.Cached.DiscC5
/-! Experimental cached rejection of the actual forward record without its Exists.elim prerequisite in #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedRejectionsMissing
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

def before : Env := NativeHelper8.before
def pc : PendingCheck := ⟨⟨.thm, EmittedForwardAcceptance.cv, EmittedForwardAcceptance.value⟩,11,17⟩
def after : Env := ⟨.thmInfo EmittedForwardAcceptance.cv :: before.consts, before.tables⟩
measured_theorem installed : ∀ pend : Array PendingCheck,
  installDeclStep .verified [] (11,mkFEnv before,pend) EmittedForwardAcceptance.decl =
    .ok (12,mkFEnv after,pend.push pc) := by
  intro pend
  cbv
def error : CheckError := unresolvedConstsErrorL (strLitSupportedF (mkFEnv before))
  s!"value of {EmittedForwardAcceptance.cv.name}" EmittedForwardAcceptance.value
measured_theorem guards_rejected : ∀ memo : CState,
  installValueGuardsC (mkFEnv before) EmittedForwardAcceptance.cv EmittedForwardAcceptance.value memo =
    .error error := by
  intro memo
  cbv
checked_normal_form typeResult : Except CheckError (Expr × CState) :=
  (coreKnotI .verified (mkFEnv before) checkFuel).infer 0 EmittedForwardAcceptance.cv.type {}
def inferredType : Expr := (typeResult.toOption.map Prod.fst).getD (.sort .zero)
def typeMemo : CState := (typeResult.toOption.map Prod.snd).getD {}
measured_theorem type_inferred :
  (coreKnotI .verified (mkFEnv before) checkFuel).infer 0 EmittedForwardAcceptance.cv.type {} =
    .ok (inferredType,typeMemo) := by rw [typeResult_eq]; rfl
checked_normal_form sortResult : Except CheckError (Level × CState) :=
  opSIxC .verified (mkFEnv before) 0 inferredType typeMemo
def sortLevel : Level := (sortResult.toOption.map Prod.fst).getD .zero
def sortMemo : CState := (sortResult.toOption.map Prod.snd).getD {}
measured_theorem sorted : opSIxC .verified (mkFEnv before) 0 inferredType typeMemo =
  .ok (sortLevel,sortMemo) := by rw [sortResult_eq]; rfl
checked_normal_form levelResult : Except CheckError (Bool × CState) :=
  (liftFueled "level comparison" (Level.isEquiv sortLevel .zero) : CheckCM Bool) sortMemo
def levelMemo : CState := (levelResult.toOption.map Prod.snd).getD {}
measured_theorem level_ok :
  (liftFueled "level comparison" (Level.isEquiv sortLevel .zero) : CheckCM Bool) sortMemo =
  .ok (true,levelMemo) := by rw [levelResult_eq]; rfl

theorem bind_error_after {α β : Type} (x : CheckCM α) (k : α → CheckCM β)
    (s s' : CState) (a : α) (e : CheckError)
    (hx : x s = .ok (a,s')) (hk : k a s' = .error e) :
    (x >>= k) s = .error e := by
  change (Except.bind (x s) fun p => k p.1 p.2) = _
  rw [hx]
  exact hk
theorem bind_error {α β : Type} (x : CheckCM α) (k : α → CheckCM β)
    (s : CState) (e : CheckError) (hx : x s = .error e) :
    (x >>= k) s = .error e := by
  change (Except.bind (x s) fun p => k p.1 p.2) = _
  rw [hx]
  rfl
measured_theorem rejected :
  checkPending .verified (mkFEnv before) pc {} = .error error := by
  unfold checkPending
  rw [show pc.vis = before.consts.length by rfl, CachedPendingComposition.restrict_self]
  refine bind_error_after _ _ {} {} _ _ rfl ?_
  refine bind_error_after _ _ {} typeMemo _ _ type_inferred ?_
  refine bind_error_after _ _ typeMemo sortMemo _ _ sorted ?_
  refine bind_error_after _ _ sortMemo levelMemo _ _ level_ok ?_
  exact bind_error _ _ levelMemo error (guards_rejected levelMemo)
end CachedRejectionsMissing
#audit_graph_module
