import Applications.Suspensions.Pure.Forcing
import Examples.SuspensionPureSimulation

/-!
# Concrete use of the actual force/cache correspondence steps

The recursive case exercises the general uncached-entry law with an already
active address. A normal literal return writes before a deliberately failing
inner match, then a cache hit replays its two-step body certificate in three
pure steps. A raised packet discards its pending frame and leaves the thunk.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureForcing
open Suspensions Suspensions.Pure Suspensions.Pure.Representation
open Suspensions.Pure.Memory Suspensions.Pure.History Suspensions.Pure.Recurrence
open Suspensions.Pure.Simulation
open Examples.SuspensionPureMachine Examples.SuspensionPureRecurrence
open Examples.SuspensionPureMemory Examples.SuspensionPureHistory Examples.SuspensionPureSimulation

def rawParameters : Core.Machine.Parameters Empty := ⟨Empty.elim, 0, 1⟩

theorem actual_delay_keeps_cyclic_body_unrun :
    let laterMeaning : Meaning Empty := ⟨cycleBody, cycleEnvironment, none⟩
    let laterWorld := Durability.put cycleWorld 1 laterMeaning
    let laterMemory := (Suspensions.delay cycleMemory cycleBody rawEnvironment).1
    Core.Machine.transition rawParameters
        ⟨cycleMemory, .eval rawEnvironment (.delay cycleBody), []⟩ =
      (.inr ⟨laterMemory, .value (.address 1), []⟩, .allocate 1) ∧
    ConfigRep parameters laterWorld ⟨laterMemory, .value (.address 1), []⟩
      ⟨.value laterMeaning.value, []⟩ ∧
    ¬Progress.Terminates (Machine.step parameters)
      (Machine.start laterMeaning.environment laterMeaning.body) := by
  have allocated := delay_entry rawParameters cycleBody cycle_memory_represented cycle_capture
    (.nil) (ActiveHistories.empty _ _ _ _)
  exact ⟨allocated.2.1, allocated.2.2.2, cycle_body_has_no_finite_result⟩

theorem actual_cycle_entry_related : ConfigRep parameters cycleWorld rawAfter pureAfter := by
  have moved := enter_thunk rawParameters (address := 0) (meaning := cycleMeaning)
    (rawCapture := rawEnvironment) cycle_memory_represented rfl rfl cycle_capture
    pending_frames_related pending_cycle_history
  exact moved.2.2

def rejectingPattern : Core.Pattern := .atom (.integer 0)

theorem literal_return_history :
    ActiveHistories parameters literalWorld [.memoize 0 [] rejectingPattern]
      (.value (.atom (.integer 7))) [.force [] rejectingPattern] := by
  intro index address environment inner found
  cases index with
  | zero =>
      have same : (Core.Machine.Frame.memoize 0 [] rejectingPattern) =
          .memoize address environment inner := Option.some.inj found
      cases same
      exact literal_past_prefix
  | succ index => simp at found

theorem literal_return_writes_before_matching :
    Core.Machine.transition rawParameters
      ⟨literalMemory, .value (.atom (.integer 7)), [.memoize 0 [] rejectingPattern]⟩ =
      (.inr ⟨cachedMemory, .pattern [] rejectingPattern (.atom (.integer 7)), []⟩, .cacheWrite 0) ∧
    ConfigRep parameters literalWorld
      ⟨cachedMemory, .pattern [] rejectingPattern (.atom (.integer 7)), []⟩
      ⟨.pattern [] rejectingPattern (.atom (.integer 7)), []⟩ := by
  have moved := return_memoize rawParameters (address := 0) (meaning := literalMeaning)
    literal_allocated.2.1 rfl (EnvRep.nil) (.atom (.integer 7)) (.nil)
    literal_return_history
  exact ⟨moved.1, moved.2.2⟩

theorem mismatch_retains_written_cell :
    Core.Machine.transition rawParameters
      ⟨cachedMemory, .pattern [] rejectingPattern (.atom (.integer 7)), []⟩ =
      (.inr ⟨cachedMemory, .mismatch, []⟩, .core) ∧
    cachedMemory.memory 0 = some (.value (.atom (.integer 7))) := ⟨rfl, rfl⟩

theorem actual_cache_hit_replays_three_steps :
    Core.Machine.transition rawParameters
      ⟨cachedMemory, .pattern [] (.suspended rejectingPattern) (.address 0), []⟩ =
      (.inr ⟨cachedMemory, .pattern [] rejectingPattern (.atom (.integer 7)), []⟩, .hit 0) ∧
    Reaches parameters 3
      ⟨.pattern [] (.suspended rejectingPattern) literalMeaning.value, []⟩
      ⟨.pattern [] rejectingPattern (.atom (.integer 7)), []⟩ ∧
    ConfigRep parameters literalWorld
      ⟨cachedMemory, .pattern [] rejectingPattern (.atom (.integer 7)), []⟩
      ⟨.pattern [] rejectingPattern (.atom (.integer 7)), []⟩ := by
  obtain ⟨value, steps, evaluated, rawStep, replayed, related⟩ :=
    reuse_cached rawParameters (address := 0) (meaning := literalMeaning)
      (rawValue := .atom (.integer 7)) (inner := rejectingPattern)
      literal_cached rfl rfl (EnvRep.nil) (.nil) (ActiveHistories.empty _ _ _ _)
  have same := literal_body.unique evaluated
  have valueEq : value = .atom (.integer 7) := (Machine.Result.value.inj same.1).symm
  subst value
  have count : steps = 2 := same.2.symm
  subst steps
  exact ⟨rawStep, replayed, related⟩

def exceptionCapture : Env Empty := [(10, .exception 99 none)]

def rawExceptionCapture : Core.Env Empty := [(10, .exception 99 none)]

def exceptionBody : Core.Expr Empty := .raise (.variable 10)

def exceptionMeaning : Meaning Empty := ⟨exceptionBody, exceptionCapture, none⟩

def exceptionWorld : World Empty := Durability.put (fun _ => none) 0 exceptionMeaning

def exceptionMemory : Core.Machine.Memory Empty :=
  (Suspensions.delay Suspensions.empty exceptionBody rawExceptionCapture).1

theorem exception_state : StateRep parameters exceptionWorld exceptionMemory :=
  ((StateRep.empty parameters).delay (.cons (.exception .none) .nil) exceptionBody).2.1

theorem exception_history :
    ActiveHistories parameters exceptionWorld [.memoize 0 [] .wildcard]
      (.raised (.exception 99 none)) [.force [] .wildcard] := by
  intro index address environment inner found
  cases index with
  | zero =>
      have same : (Core.Machine.Frame.memoize 0 [] .wildcard) =
          .memoize address environment inner := Option.some.inj found
      cases same
      exact ⟨exceptionMeaning, 3, rfl, rfl⟩
  | succ index => simp at found

theorem exception_exit_keeps_thunk :
    Core.Machine.transition rawParameters
      ⟨exceptionMemory, .raised (.exception 99 none), [.memoize 0 [] .wildcard]⟩ =
      (.inr ⟨exceptionMemory, .raised (.exception 99 none), []⟩, .core) ∧
    ConfigRep parameters exceptionWorld ⟨exceptionMemory, .raised (.exception 99 none), []⟩
      ⟨.raised (.exception 99 none), []⟩ ∧
    exceptionMemory.memory 0 = some (.thunk exceptionBody rawExceptionCapture) := by
  have moved := raise_memoize rawParameters exception_state (.exception .none) (.nil) exception_history
  exact ⟨moved.1, moved.2.2, rfl⟩

end Examples.SuspensionPureForcing
