import AcceptanceComposition
import AcceptanceMeasurement
namespace AndAcceptanceRoot
open ConLeche AcceptanceStages.Reference AndPositivityStages AcceptanceComposition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option pp.deepTerms.threshold 8

-- Small representation joins, independently checked before phase composition.
theorem hi_eq : ctx.hiAt 0 = 3 := rfl
theorem levels_eq : ctx.lps.map Level.param = [] := rfl
theorem inst_eq : andIntroRaw.toConstantVal.type.instantiateLevelParams
    andIntroRaw.toConstantVal.levelParams [] = andIntroRaw.toConstantVal.type := by
  cbv
theorem fuel_eq : whnfWalkFuel crest = 1027 := by
  rw [whnfWalkFuel, CheckerReduction.depth_eq, crest_eq]
  rfl
theorem sort_ok : (fueledOps .verified 32).ensureSort indsResult.1 3
    (.sort (.imax .zero (.imax .zero .zero))) = .ok (.imax .zero (.imax .zero .zero)) := by
  cbv

def post : NestState :=
  { ctorNfs := #[].push (nestCtorNf ctx [] 3 [] ctx.params andIntroRaw.toConstantVal
      [.fvar 0 (.sort .zero), .fvar 1 (.sort .zero)] (.fvar 2 (.sort .zero))) }

measured_theorem constructors :
    nestCtors ctx (fueledOps .verified 32) indsResult.1
      (fun crest => nestPos (fueledOps .verified 32) indsResult.1 ctx (whnfWalkFuel crest)) []
      (ctx.hiAt 0) (ctx.lps.map Level.param) ctx.params ctx.names holes
      [(andIntroRaw.toConstantVal,2)] {} = .ok ([([.ordinary,.ordinary],crest)],post) := by
  rw [hi_eq, levels_eq]
  have h := ctors_one ctx (fueledOps .verified 32) indsResult.1
    (fun crest => nestPos (fueledOps .verified 32) indsResult.1 ctx (whnfWalkFuel crest))
    [] 3 [] ctx.params ctx.names holes andIntroRaw.toConstantVal 2 {} {} crest
    (.sort (.imax .zero (.imax .zero .zero))) (.imax .zero (.imax .zero .zero))
    [.ordinary,.ordinary] [.fvar 0 (.sort .zero),.fvar 1 (.sort .zero)] (.fvar 2 (.sort .zero))
    (by rfl) (by rw [inst_eq]; exact crest_ok) inferCrest sort_ok
    (by intro err; rw [fuel_eq]; exact fieldsCrest err) hguard hres
  rw [hclose] at h
  exact h

measured_theorem root :
    nestRoot (fueledOps .verified 32) indsResult.1 ctx holes ctorResult.1 {} = .ok rootResult := by
  exact root_one (fueledOps .verified 32) indsResult.1 ctx holes
    [(andIntroRaw.toConstantVal,2)] {} post [([.ordinary,.ordinary],crest)] constructors
end AndAcceptanceRoot
#audit_graph_module
