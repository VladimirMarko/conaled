import Applications.Suspensions.Pure.CacheCounts
import Applications.Suspensions.BodyAccounting

/-!
# Conditional body-entry counts in finite pure source executions

The existing finite source nonreentry theorem supplies freshness, and the
represented source state supplies bounded memory. The additional no-unwind
premise concerns actual unfinished prefixes at the selected physical address.
It is not implied by purity, a finite answer, or normal final return: an outer
handler can abandon a body and retry the uncached thunk.

The conclusion counts actual body-entry events in the existing ordered trace.
It includes unfinished prefixes and unused budget after completion. It does
not count the transitions inside a body or assert a unit runtime cost for it.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Simulation
open Representation Memory Domain DomainState WorldDomain Compatibility

variable {Primitive : Type} {operations : Primitive → Prop}
  {rawParameters : Core.Machine.Parameters Primitive} {parameters : Machine.Parameters Primitive}
  {world : World Primitive}

/-- Boundedness and fresh entries are derived from the admitted finite source
execution. Absence of exceptional memoize unwind remains an explicit, separate
condition on the actual execution of the selected address. -/
theorem source_bodyEntries_le_one
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
    (address : Nat)
    (noUnwind : Core.Machine.NoMemoizeUnwind rawParameters
      (Core.Machine.start memory rawEnvironment expression) address)
    (budget : Nat) :
    Core.Observation.bodyEntries address
      (Core.Observation.observe rawParameters budget
        (Core.Machine.start memory rawEnvironment expression)).2 ≤ 1 := by
  exact Core.Observation.bodyEntries_observe_le_one
    (Core.Machine.start_bounded state.bounded rawEnvironment expression)
    (finite_fresh_entries compatible preserve worldAllowed (ConfigRep.start state captured expression)
      (start_allowed environmentAllowed code) evaluation) noUnwind budget

/-- The same derived bound on the actual ordered event list. -/
theorem source_bodyEntry_count_le_one
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
    (address : Nat)
    (noUnwind : Core.Machine.NoMemoizeUnwind rawParameters
      (Core.Machine.start memory rawEnvironment expression) address)
    (budget : Nat) :
    (FreeAddMonoid.toList (Core.Observation.observe rawParameters budget
      (Core.Machine.start memory rawEnvironment expression)).2).count (.body address) ≤ 1 := by
  simpa only [Core.Observation.bodyEntries_eq_count] using
    source_bodyEntries_le_one compatible preserve worldAllowed state captured
      environmentAllowed code evaluation address noUnwind budget

end Suspensions.Pure.Simulation
