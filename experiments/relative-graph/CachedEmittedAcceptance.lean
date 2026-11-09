import CachedPending0
import CachedPending1
import CachedPending2
import CachedPending3
import CachedPending4
import CachedPending5
import CachedPending6
import CachedPending7
import CachedPending8
import CachedPending9
import CachedPending10
/-! Experimental exact cached acceptance of the canonical emitted family.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedEmittedAcceptance
open ConLeche ConLeche.Cached CachedFamilyInstallation
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option acceptance.measureTreeSize false
measured_theorem groups : ∀ i, GroupChecked .verified installed i := by
  intro i
  rcases i with _ | i
  · change ∃ memo : CState, checkPending .verified (mkFEnv EmittedEnvironment.environment) pc0 {} = .ok ((),memo)
    exact ⟨CachedPending0.memo,CachedPending0.accepted_final⟩
  rcases i with _ | i
  · change ∃ memo : CState, checkPending .verified (mkFEnv EmittedEnvironment.environment) pc1 {} = .ok ((),memo)
    exact CachedPending1.accepted_final
  rcases i with _ | i
  · change ∃ memo : CState, checkPending .verified (mkFEnv EmittedEnvironment.environment) pc2 {} = .ok ((),memo)
    exact CachedPending2.accepted_final
  rcases i with _ | i
  · change ∃ memo : CState, checkPending .verified (mkFEnv EmittedEnvironment.environment) pc3 {} = .ok ((),memo)
    exact CachedPending3.accepted_final
  rcases i with _ | i
  · change ∃ memo : CState, checkPending .verified (mkFEnv EmittedEnvironment.environment) pc4 {} = .ok ((),memo)
    exact CachedPending4.accepted_final
  rcases i with _ | i
  · change ∃ memo : CState, checkPending .verified (mkFEnv EmittedEnvironment.environment) pc5 {} = .ok ((),memo)
    exact CachedPending5.accepted_final
  rcases i with _ | i
  · change ∃ memo : CState, checkPending .verified (mkFEnv EmittedEnvironment.environment) pc6 {} = .ok ((),memo)
    exact CachedPending6.accepted_final
  rcases i with _ | i
  · change ∃ memo : CState, checkPending .verified (mkFEnv EmittedEnvironment.environment) pc7 {} = .ok ((),memo)
    exact CachedPending7.accepted_final
  rcases i with _ | i
  · change ∃ memo : CState, checkPending .verified (mkFEnv EmittedEnvironment.environment) pc8 {} = .ok ((),memo)
    exact CachedPending8.accepted_final
  rcases i with _ | i
  · change ∃ memo : CState, checkPending .verified (mkFEnv EmittedEnvironment.environment) pc9 {} = .ok ((),memo)
    exact CachedPending9.accepted_final
  rcases i with _ | i
  · change ∃ memo : CState, checkPending .verified (mkFEnv EmittedEnvironment.environment) pc10 {} = .ok ((),memo)
    exact CachedPending10.accepted_final
  exact groupChecked_of_ge .verified installed (by change 11 ≤ _; omega)
def checked : FullyChecked .verified [] EmittedEnvironment.declarations := ⟨installed,groups⟩
def installedArray : InstalledEnv .verified [] EmittedEnvironment.declarations.toArray.toList :=
  ⟨mkFEnv EmittedEnvironment.environment,pend,⟨14,by simpa only [List.toList_toArray] using CachedFamilyInstallation.run⟩⟩
def checkedArray : FullyChecked .verified [] EmittedEnvironment.declarations.toArray.toList :=
  ⟨installedArray,groups⟩
measured_theorem accepted : checkDecls .verified [] EmittedEnvironment.declarations.toArray =
    .ok EmittedEnvironment.environment := by
  exact fullyChecked_checkDecls .verified checkedArray
end CachedEmittedAcceptance
#audit_graph_module
