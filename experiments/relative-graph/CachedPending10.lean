import CachedPending10FinalEquality
import CachedPendingRunComposition
/-! Experimental actual cached backward pending check for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedPending10
open ConLeche ConLeche.Cached CachedFamilyInstallation CachedPending10Stages CachedPending10Value EmittedBackwardAcceptance
set_option acceptance.measureTreeSize false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
def memo := CachedPending10FinalEquality.memo
measured_theorem run : checkPending .verified (mkFEnv before) pc10 {} = .ok ((),memo) := by
  exact CachedPendingRunComposition.thm_run (mkFEnv before) fe r rfl
    cv value 13 before.consts.length (CachedPendingComposition.restrict_self before)
    _ _ _ _ _ _ _ _ header_ok sort_ok prop_ok guards
    CachedPending10Value.accepted CachedPending10FinalEquality.accepted
measured_theorem accepted : ∃ memo : CState, checkPending .verified (mkFEnv before) pc10 {} = .ok ((),memo) := ⟨memo,run⟩
measured_theorem accepted_final : ∃ memo : CState,
  checkPending .verified (mkFEnv EmittedEnvironment.environment) pc10 {} = .ok ((),memo) := by
  rw [CachedPendingComposition.prefix_view before pc10
    (EmittedEnvironment.environment.consts.take 1) (by cbv) (by rfl) (by rfl)]
  exact accepted
end CachedPending10
#audit_graph_module
