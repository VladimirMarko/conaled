import CachedAndAbsSorts
import CachedPassComposition

/-! Experimental complete cached And pass for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedAndPass
open ConLeche ConLeche.Cached AcceptanceStages.Reference
open CachedAndConstructor CachedAndCrest CachedAndPositivity CachedTransitionComposition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 4

measured_theorem uniform : ∀ s : CState,
    nestUniform (m := CheckCM) ctx ctorResult.1 s = .ok ((),s) := by
  intro s
  cbv

measured_theorem positivity :
    checkBlockPositivity (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1
      (mkFEnv indsResult.1).find? completed indsResult.2.1 ctorResult.1 p11 =
        .ok (AndInstallation.posResult,c5) := by
  apply CachedPositivityComposition.block_positivity (ctx := ctx) (holes := holes)
    (outs := AndPositivityStages.rootResult.1) (st := AndPositivityStages.rootResult.2)
    (s1 := p11) (s2 := p11) (s3 := c5)
  · exact CachedAndPassStages.context p11
  · exact uniform p11
  · exact CachedAndRoot.root
  · exact CachedAndAbsSorts.all_sorts

measured_theorem seeds : ∀ (ops : CheckerOps CheckCM) (s : CState),
    nestSeeds ops indsResult.1 ctx (classSeeds ctx holes AndInstallation.classes.2)
      AndInstallation.posResult.2.2 s = .ok (AndInstallation.posResult.2.2,s) := by
  intro ops s
  have he : classSeeds ctx holes AndInstallation.classes.2 = [] := by cbv
  rw [he]
  rfl

def passResult : BlockPass FEnv :=
  ⟨mkFEnv indsResult.1,indsResult.2.1,completed,ctorResult.1,ctorResult.2,
    AndInstallation.posResult.1,AndInstallation.posResult.2.1,ctx.params,
    AndInstallation.classes.1,AndInstallation.classes.2,AndInstallation.posResult.2.2.ctorNfs⟩

measured_theorem pass :
    checkBlockPassS .verified (mkFEnv AcceptanceStages.equalityEnvironment) parts false {} =
      .ok (passResult,c5) := by
  exact CachedPassComposition.pass .verified _ _ parts false indsResult.2.1 indsResult.2.2
    ctorResult.1 ctorResult.2 ctx holes AndInstallation.classes.1 AndInstallation.classes.2
    AndInstallation.posResult.1 AndInstallation.posResult.2.1
    AndInstallation.posResult.2.2 AndInstallation.posResult.2.2
    {} CachedAndFormer.s5 {} p11 p11 p11 c5 c5
    CachedAndStages.former CachedAndPassStages.former_flush CachedAndPassStages.constructors
    (CachedAndPassStages.context p11)
    (CachedAndPassStages.classes _ p11) positivity (seeds _ c5)
end CachedAndPass
#audit_graph_module
