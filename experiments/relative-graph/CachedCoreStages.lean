import CachedTransitionComposition
import AcceptanceStages
import ConLeche.Verify.Cached.KnotC

/-! Experimental #417 exact cached core transitions.
See [artifact scope](../../docs/research/relative-emitted-acceptance.md). -/
namespace CachedCoreStages
open ConLeche ConLeche.Cached
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 4

def eqFe := mkFEnv AcceptanceStages.equalityEnvironment

def sortMemo : CState := { ({} : CState) with
  inferC := ({} : CState).inferC.insert (.sort .zero) (.sort (.succ .zero)) }

measured_theorem sort_infer_succ : ∀ (env : Env) (f d : Nat),
    (coreKnotI .verified (mkFEnv env) (f + 1)).infer d (.sort .zero) {} =
      .ok (.sort (.succ .zero), sortMemo) := by
  intro env f d
  rw [coreKnotI_infer_succ]
  apply CachedTransitionComposition.memo_miss (s' := {})
  · exact Std.HashMap.getElem?_empty
  · rfl

measured_theorem sort_infer :
    (coreKnotI .verified (mkFEnv AcceptanceStages.equalityEnvironment) checkFuel).infer 0 (.sort .zero) {} =
      .ok (.sort (.succ .zero), sortMemo) := by
  exact Eq.trans
    (congrArg (fun f => (coreKnotI .verified (mkFEnv AcceptanceStages.equalityEnvironment) f).infer 0 (.sort .zero) {})
      (show checkFuel = 4611686018427387903 + 1 by unfold checkFuel; rfl))
    (sort_infer_succ AcceptanceStages.equalityEnvironment 4611686018427387903 0)

end CachedCoreStages
#audit_graph_module
