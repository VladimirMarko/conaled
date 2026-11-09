import CachedAndPass
import AndInstallationTail

/-! Experimental cached And tail inputs for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedAndTailStages
open ConLeche ConLeche.Cached AcceptanceStages.Reference
open CachedAndPass CachedAndPositivity
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
      mkFEnv AndInstallationTail.ctorEnv := by
  rw [consBlockCtorsF_mkFEnv]
  congr 1

measured_theorem constructor_flush : flushC c5 = .ok ((),{}) := by rfl

end CachedAndTailStages
#audit_graph_module
