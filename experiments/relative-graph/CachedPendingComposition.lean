import CachedFamilyInstallation
import ConLeche.Verify.Cached.InstalledC
import ConLeche.Verify.Cached.ParInstall
/-! Experimental exact pending-prefix transport for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedPendingComposition
open ConLeche ConLeche.Cached
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option acceptance.measureTreeSize false
measured_theorem counter : ∀ cs : List ConstantInfo, (mkFEnvGo cs).1 = cs.length := by
  intro cs; induction cs with
  | nil => rfl
  | cons c cs ih => simp only [mkFEnvGo, List.length_cons, ih]
@[cbv_eval] theorem restrict_self (env : Env) :
    (mkFEnv env).restrictTo env.consts.length = mkFEnv env := by
  unfold mkFEnv FEnv.restrictTo
  simp only [counter]
measured_theorem congr : ∀ (mode : CheckMode) (fe1 fe2 : FEnv) (pc : PendingCheck)
    (hf : (fe1.restrictTo pc.vis).find? = (fe2.restrictTo pc.vis).find?)
    (ht : (fe1.restrictTo pc.vis).findTable? = (fe2.restrictTo pc.vis).findTable?),
    checkPending mode fe1 pc = checkPending mode fe2 pc := by
  intro mode fe1 fe2 pc hf ht
  simp only [checkPending, coreKnotI_congr hf ht, opSIxC_congr hf ht,
    installValueGuardsC_congr hf]
measured_theorem names : NodupNames EmittedEnvironment.environment := by
  unfold NodupNames
  decide +kernel
measured_theorem prefix_view : ∀ (before : Env) (pc : PendingCheck) (new : List ConstantInfo),
    EmittedEnvironment.environment.consts = new ++ before.consts →
    EmittedEnvironment.environment.tables = before.tables →
    pc.vis = before.consts.length →
    checkPending .verified (mkFEnv EmittedEnvironment.environment) pc =
      checkPending .verified (mkFEnv before) pc := by
  intro before pc new he ht hv
  apply congr
  · rw [hv, restrict_self]
    funext n
    rw [mkFEnv_find?]
    apply restrictTo_find?_of_extends (new := new)
    · rw [mkFEnv_env]
    · simpa only [mkFEnv_env] using names
    · simpa only [mkFEnv_env] using he
  · rw [hv, restrict_self]
    funext n
    rw [mkFEnv_findTable?]
    apply restrictTo_findTable?_of_extends (new := new) (newQ := [])
    · rw [mkFEnv_env]
    · simpa only [mkFEnv_env] using names
    · simpa only [mkFEnv_env] using he
    · simpa only [mkFEnv_env, List.nil_append] using ht
    · simp
end CachedPendingComposition
#audit_graph_module
