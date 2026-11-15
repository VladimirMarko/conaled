import CachedAndPositivity

/-! Experimental cached And positivity root for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedAndRoot
open ConLeche ConLeche.Cached AcceptanceStages.Reference
open CachedAndConstructor CachedAndCrest CachedAndPositivity CachedPositivityComposition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 4

measured_theorem crest_identity : AndPositivityStages.crest = crest :=
  AndPositivityStages.crest_eq
measured_theorem fuel_identity : whnfWalkFuel crest = 1027 := by
  rw [← crest_identity]
  exact AndAcceptanceRoot.fuel_eq

measured_theorem constructors :
    nestCtors ctx (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1
      (fun e => nestPos (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1 ctx (whnfWalkFuel e))
      [] (ctx.hiAt 0) (ctx.lps.map Level.param) ctx.params ctx.names holes
      [(andIntroRaw.toConstantVal,2)] {} p11 =
        .ok (([([.ordinary,.ordinary],AndPositivityStages.crest)],AndAcceptanceRoot.post),c5) := by
  rw [AndAcceptanceRoot.hi_eq, AndAcceptanceRoot.levels_eq]
  have h := ctors_one ctx (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1
    (fun e => nestPos (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1 ctx (whnfWalkFuel e))
    [] 3 [] ctx.params ctx.names holes andIntroRaw.toConstantVal 2 {} {} crest
    (.sort resultSort) resultSort [.ordinary,.ordinary] [a,b] hole p11 c2 c3 c5
    (by rfl)
    (by rw [AndAcceptanceRoot.inst_eq, ← crest_identity]; exact AndPositivityStages.crest_ok)
    infer_fixed sort_fixed
    (by intro err; rw [fuel_identity]; exact CachedAndPositivity.fields err)
    AndPositivityStages.hguard AndPositivityStages.hres
  have hc : closeTelescope [a,b] 3 hole = AndPositivityStages.crest := AndPositivityStages.hclose
  rw [hc] at h
  exact h

measured_theorem root :
    nestRoot (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1 ctx holes
      ctorResult.1 {} p11 = .ok (AndPositivityStages.rootResult,c5) := by
  exact root_one _ _ _ _ _ _ _ _ _ _ constructors

end CachedAndRoot
#audit_graph_module
