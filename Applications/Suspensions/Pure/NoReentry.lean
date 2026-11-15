import Applications.Suspensions.Pure.Execution
import Applications.Suspensions.Pure.Reentry
import Applications.Suspensions.BodyEvent

/-!
# Actual self-reentry cannot finish in the pure domain

The raw machine is unchanged: it can enter a thunk whose address already has
a pending memoize frame. The theorem proves that such an actual entry,
observed from an admitted represented source, precludes every finite raw
outcome. It does not assume nonreentry or introduce a blackhole transition.

The execution correspondence constructs the pure history at the observed
body-entry event. Its positive recurrence obstructs pure completion; the
finite correspondence then excludes raw completion. Source exceptions and
runtime faults remain among the finite outcomes ruled out.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Simulation
open Representation Memory Domain DomainState WorldDomain Compatibility

variable {Primitive : Type} {operations : Primitive → Prop}
  {rawParameters : Core.Machine.Parameters Primitive} {parameters : Machine.Parameters Primitive}
  {world : World Primitive} {raw : Core.Machine.Config Primitive} {view : Machine.Config Primitive}

/-- At a related configuration, forcing an already active address cannot
finish. The active occurrence is a hypothesis about the actual caller stack;
its impossibility in a finite execution is the conclusion. -/
theorem active_force_not_terminates
    {environment oldEnvironment : Core.Env Primitive} {inner oldInner : Core.Pattern}
    {address frameIndex : Nat}
    (compatible : ParametersCompatible operations rawParameters parameters)
    (preserve : ParametersPreserve operations parameters)
    (worldAllowed : WorldAllowed operations world)
    (represented : ConfigRep parameters world raw view) (allowed : ConfigAllowed operations view)
    (forcing : raw.control = .pattern environment (.suspended inner) (.address address))
    (active : raw.stack[frameIndex]? = some (.memoize address oldEnvironment oldInner)) :
    ¬Progress.Terminates (Core.Machine.step rawParameters) raw := by
  rintro ⟨answer, count, evaluation⟩
  obtain ⟨_, result, steps, _, _, _, _, pureRun⟩ :=
    finite_correspondence compatible preserve worldAllowed represented allowed evaluation
  exact represented.active_force_pure_not_terminates forcing active ⟨result, steps, pureRun⟩

/-- The observed prefix may lie in a nonterminating computation. The actual
event supplies the inspected thunk/address, and its same-address pending frame
forces the entire original raw configuration to have no finite result. -/
theorem active_body_entry_not_terminates
    {index address frameIndex : Nat} {config : Core.Machine.Config Primitive}
    {oldEnvironment : Core.Env Primitive} {oldInner : Core.Pattern}
    (compatible : ParametersCompatible operations rawParameters parameters)
    (preserve : ParametersPreserve operations parameters)
    (worldAllowed : WorldAllowed operations world)
    (represented : ConfigRep parameters world raw view) (allowed : ConfigAllowed operations view)
    (reached : Core.Prefix.observe rawParameters index raw = .inr config)
    (event : (Core.Machine.transition rawParameters config).2 = .body address)
    (active : config.stack[frameIndex]? = some (.memoize address oldEnvironment oldInner)) :
    ¬Progress.Terminates (Core.Machine.step rawParameters) raw := by
  obtain ⟨afterWorld, pureConfig, _, _, afterAllowed, related, codeAllowed, _⟩ :=
    body_entry_correspondence compatible preserve worldAllowed represented allowed reached event
  obtain ⟨environment, inner, body, captured, forcing, occupied⟩ :=
    (Core.Machine.body_event_iff rawParameters config address).mp event
  have unfinished := active_force_not_terminates compatible preserve afterAllowed related
    codeAllowed forcing active
  rintro ⟨answer, count, evaluation⟩
  obtain ⟨remaining, residual, _⟩ := Core.Recursive.evaluates_strip_prefix reached evaluation
  exact unfinished ⟨answer, remaining, residual⟩

/-- Every actual body entry in a finite admitted run is absent from all
pending memoize-frame occurrences. This is derived from nontermination of
self-reentry, not supplied as an invariant premise. -/
theorem finite_body_entry_not_active
    {answer : Core.Machine.Answer Primitive} {count index address : Nat}
    {config : Core.Machine.Config Primitive}
    (compatible : ParametersCompatible operations rawParameters parameters)
    (preserve : ParametersPreserve operations parameters)
    (worldAllowed : WorldAllowed operations world)
    (represented : ConfigRep parameters world raw view) (allowed : ConfigAllowed operations view)
    (evaluation : Progress.Evaluates (Core.Machine.step rawParameters) raw answer count)
    (reached : Core.Prefix.observe rawParameters index raw = .inr config)
    (event : (Core.Machine.transition rawParameters config).2 = .body address)
    (frameIndex : Nat) (environment : Core.Env Primitive) (inner : Core.Pattern) :
    config.stack[frameIndex]? ≠ some (.memoize address environment inner) := by
  intro active
  exact active_body_entry_not_terminates compatible preserve worldAllowed represented allowed
    reached event active ⟨answer, count, evaluation⟩

/-- A source-facing specialization constructs the initial configuration and
empty-history obligations from represented memory/captures and admitted code. -/
theorem source_reentry_not_terminates
    {memory : Core.Machine.Memory Primitive} {rawEnvironment : Core.Env Primitive}
    {environment : Env Primitive} {expression : Core.Expr Primitive}
    {index address frameIndex : Nat} {config : Core.Machine.Config Primitive}
    {oldEnvironment : Core.Env Primitive} {oldInner : Core.Pattern}
    (compatible : ParametersCompatible operations rawParameters parameters)
    (preserve : ParametersPreserve operations parameters)
    (worldAllowed : WorldAllowed operations world) (state : StateRep parameters world memory)
    (captured : EnvRep world rawEnvironment environment) (environmentAllowed : EnvAllowed operations environment)
    (code : CodeAllowed operations expression)
    (reached : Core.Prefix.observe rawParameters index
      (Core.Machine.start memory rawEnvironment expression) = .inr config)
    (event : (Core.Machine.transition rawParameters config).2 = .body address)
    (active : config.stack[frameIndex]? = some (.memoize address oldEnvironment oldInner)) :
    ¬Progress.Terminates (Core.Machine.step rawParameters)
      (Core.Machine.start memory rawEnvironment expression) :=
  active_body_entry_not_terminates compatible preserve worldAllowed
    (ConfigRep.start state captured expression) (start_allowed environmentAllowed code) reached event active

end Suspensions.Pure.Simulation
