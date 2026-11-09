import CachedExistsPass
import ExistsInstallationTail

/-! Experimental cached Exists tail inputs for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedExistsTailStages
open ConLeche ConLeche.Cached ExistsPassStages
open CachedExistsPass
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 4

measured_theorem idx_sorts : ∀ (ops : CheckerOps CheckCM) (s : CState),
    checkBlockIdxSortsF ops (mkFEnv indsResult.1) completed.toBlockShape
      (completed.members.zip indsResult.2.1) s = .ok ([[]],s) := by
  intro ops s
  cbv

measured_theorem constructor_env :
    consBlockCtorsF completed.nP ctorResult.1 (mkFEnv indsResult.1) =
      mkFEnv ExistsInstallationTail.ctorEnv := by
  rw [consBlockCtorsF_mkFEnv]
  congr 1

measured_theorem constructor_flush : flushC posMemo = .ok ((),posMemo.flushed) := by rfl

end CachedExistsTailStages
#audit_graph_module
