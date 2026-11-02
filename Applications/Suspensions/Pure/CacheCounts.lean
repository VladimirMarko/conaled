import Applications.Suspensions.Pure.NoReentry
import Applications.Suspensions.CacheAccounting

/-!
# Successful cache writes in finite pure source executions

The actual nonreentry theorem discharges the raw accounting premise at every
observed body entry. Starting source configurations have no pending memoize
frames, so a finite admitted source run writes each suspension address at most
once. The count projects the existing ordered transition trace, including its
absorbing behavior after the answer is reached.

The finite execution witness, primitive compatibility, hereditary preservation
and represented pure domain remain explicit. Exceptions may cause repeated
body attempts without a successful write; different fresh addresses are
counted separately even if their code and meanings coincide.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Simulation
open Representation Memory Domain DomainState WorldDomain Compatibility

variable {Primitive : Type} {operations : Primitive → Prop}
  {rawParameters : Core.Machine.Parameters Primitive} {parameters : Machine.Parameters Primitive}
  {world : World Primitive} {raw : Core.Machine.Config Primitive} {view : Machine.Config Primitive}

/-- Fresh body entries are a consequence of actual finite pure execution.
The initial related configuration may itself have pending frames; no initial
uniqueness premise is needed for this nonreentry consequence. -/
theorem finite_fresh_entries
    {answer : Core.Machine.Answer Primitive} {count : Nat}
    (compatible : ParametersCompatible operations rawParameters parameters)
    (preserve : ParametersPreserve operations parameters)
    (worldAllowed : WorldAllowed operations world)
    (represented : ConfigRep parameters world raw view) (allowed : ConfigAllowed operations view)
    (evaluation : Progress.Evaluates (Core.Machine.step rawParameters) raw answer count) :
    Core.Machine.FreshEntries rawParameters raw := by
  intro index config reached address event pending
  obtain ⟨environment, inner, member⟩ :=
    (Core.Machine.pendingAddresses_mem_iff address config.stack).mp pending
  obtain ⟨frameIndex, active⟩ := List.mem_iff_getElem?.mp member
  exact finite_body_entry_not_active compatible preserve worldAllowed represented allowed
    evaluation reached event frameIndex environment inner active

/-- The source specialization proves both pending-frame uniqueness at the
start and freshness throughout the run; neither is assumed by the caller.
Every budget is allowed, including unfinished prefixes and extra budget after
the finite answer. -/
theorem source_cacheWrites_le_one
    {memory : Core.Machine.Memory Primitive} {rawEnvironment : Core.Env Primitive}
    {environment : Env Primitive} {expression : Core.Expr Primitive}
    {answer : Core.Machine.Answer Primitive} {count : Nat}
    (compatible : ParametersCompatible operations rawParameters parameters)
    (preserve : ParametersPreserve operations parameters)
    (worldAllowed : WorldAllowed operations world) (state : StateRep parameters world memory)
    (captured : EnvRep world rawEnvironment environment)
    (environmentAllowed : EnvAllowed operations environment) (code : CodeAllowed operations expression)
    (evaluation : Progress.Evaluates (Core.Machine.step rawParameters)
      (Core.Machine.start memory rawEnvironment expression) answer count)
    (address budget : Nat) :
    Core.Observation.cacheWrites address
      (Core.Observation.observe rawParameters budget
        (Core.Machine.start memory rawEnvironment expression)).2 ≤ 1 := by
  exact Core.Observation.cacheWrites_observe_le_one
    (Core.Machine.start_bounded state.bounded rawEnvironment expression) List.nodup_nil
    (finite_fresh_entries compatible preserve worldAllowed (ConfigRep.start state captured expression)
      (start_allowed environmentAllowed code) evaluation) address budget

/-- The same bound stated directly on the actual ordered event list. -/
theorem source_cacheWrite_count_le_one
    {memory : Core.Machine.Memory Primitive} {rawEnvironment : Core.Env Primitive}
    {environment : Env Primitive} {expression : Core.Expr Primitive}
    {answer : Core.Machine.Answer Primitive} {count : Nat}
    (compatible : ParametersCompatible operations rawParameters parameters)
    (preserve : ParametersPreserve operations parameters)
    (worldAllowed : WorldAllowed operations world) (state : StateRep parameters world memory)
    (captured : EnvRep world rawEnvironment environment)
    (environmentAllowed : EnvAllowed operations environment) (code : CodeAllowed operations expression)
    (evaluation : Progress.Evaluates (Core.Machine.step rawParameters)
      (Core.Machine.start memory rawEnvironment expression) answer count)
    (address budget : Nat) :
    (FreeAddMonoid.toList (Core.Observation.observe rawParameters budget
      (Core.Machine.start memory rawEnvironment expression)).2).count (.cacheWrite address) ≤ 1 := by
  simpa only [Core.Observation.cacheWrites_eq_count] using
    source_cacheWrites_le_one compatible preserve worldAllowed state captured
      environmentAllowed code evaluation address budget

end Suspensions.Pure.Simulation
