import CachedAndConstructor
import AndInstallation

/-! Experimental cached And pass stages for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedAndPassStages
open ConLeche ConLeche.Cached AcceptanceStages.Reference
open CachedTransitionComposition CachedConstructorComposition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 4
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj

measured_theorem former_flush : flushC CachedAndFormer.s5 = .ok ((),{}) := by rfl

checked_normal_form ctorMember : MemberShape := completed.members.headD default
measured_theorem member_ctors : ctorMember.ctors = [(andIntroRaw.toConstantVal,2)] := by cbv
measured_theorem members : completed.members.zip indsResult.2.1 = [(ctorMember,andRaw.toConstantVal)] := by cbv

measured_theorem constructor :
    checkSumCtorF (sharedOpsC .verified (mkFEnv indsResult.1))
      (mkFEnv indsResult.1) (mkFEnv indsResult.1) ctorMember.cvT.name completed.lps
      completed.nP ctorMember.nIdx completed.resSort completed.isProp completed.large
      andIntroRaw.toConstantVal 2 andRaw.toConstantVal {} =
        .ok ((andIntroRaw.toConstantVal,[.zero,.zero]),CachedAndConstructor.p11) := by
  have hn : ctorMember.cvT.name = andName := by cbv
  have hl : completed.lps = [] := by cbv
  have hp : completed.nP = 2 := by cbv
  have hi : ctorMember.nIdx = 0 := by cbv
  have hs : completed.resSort = .zero := by cbv
  have hb : completed.isProp = true := by cbv
  rw [hn,hl,hp,hi,hs,hb]
  exact CachedAndConstructor.constructor completed.large

measured_theorem constructors :
    checkBlockCtorsF (sharedOpsC .verified (mkFEnv indsResult.1))
      (mkFEnv indsResult.1) (mkFEnv indsResult.1) completed.toBlockShape
      (completed.members.zip indsResult.2.1) {} = .ok (ctorResult,CachedAndConstructor.p11) := by
  rw [members]
  exact constructors_singleton _ _ _ _ _ _ _ _ _ _ _ member_ctors constructor

measured_theorem context : ∀ s : CState,
    blockNestCtx (m := CheckCM) completed.toBlockShape indsResult.2.1
      (mkFEnv indsResult.1).find? s = .ok ((ctx,holes),s) := by
  intro s
  have he : (mkFEnv indsResult.1).find? = indsResult.1.find? := by
    funext n
    exact mkFEnv_find? _ _
  rw [he]
  cbv

measured_theorem classes : ∀ (ops : CheckerOps CheckCM) (s : CState),
    checkBlockClasses ops (mkFEnv indsResult.1) completed.toBlockShape ctx.params ctorResult.1 s =
      .ok (AndInstallation.classes,s) := by
  intro ops s
  cbv

end CachedAndPassStages
#audit_graph_module
