import CachedPendingComposition
/-! Experimental prefix transport for the malformed #417 families.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedRejectionsPrefix
open ConLeche ConLeche.Cached
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option acceptance.measureTreeSize false
measured_theorem prefix_view : ∀ (final before : Env) (pc : PendingCheck) (new : List ConstantInfo),
    NodupNames final →
    final.consts = new ++ before.consts →
    final.tables = before.tables →
    pc.vis = before.consts.length →
    checkPending .verified (mkFEnv final) pc =
      checkPending .verified (mkFEnv before) pc := by
  intro final before pc new names he ht hv
  apply CachedPendingComposition.congr
  · rw [hv, CachedPendingComposition.restrict_self]
    funext n
    rw [mkFEnv_find?]
    apply restrictTo_find?_of_extends (new := new)
    · rw [mkFEnv_env]
    · simpa only [mkFEnv_env] using names
    · simpa only [mkFEnv_env] using he
  · rw [hv, CachedPendingComposition.restrict_self]
    funext n
    rw [mkFEnv_findTable?]
    apply restrictTo_findTable?_of_extends (new := new) (newQ := [])
    · rw [mkFEnv_env]
    · simpa only [mkFEnv_env] using names
    · simpa only [mkFEnv_env] using he
    · simpa only [mkFEnv_env, List.nil_append] using ht
    · simp
end CachedRejectionsPrefix
#audit_graph_module
