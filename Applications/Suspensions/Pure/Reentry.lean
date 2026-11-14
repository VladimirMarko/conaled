import Applications.Suspensions.Pure.Simulation

/-!
# Pure obstruction at a represented active forcing occurrence

An actual pending memoize-frame occurrence supplies the executed prefix of
its immutable pure body. If the represented current control forces that same
address, the history theorem excludes a finite body evaluation. The next pure
step enters that body with caller frames appended, so the current pure
configuration also has no finite result, including exceptions and faults.

This theorem needs no code-domain, primitive-compatibility, raw finite-run or
distinct-active-address premise. Its conclusion concerns the pure machine.
Transferring the obstruction to raw execution remains the separate finite
correspondence theorem's responsibility.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Simulation
open Representation Recurrence

variable {Primitive : Type}

private theorem force_control_meaning {world : World Primitive}
    {environment : Core.Env Primitive} {inner : Core.Pattern} {address : Nat}
    {view : Machine.Control Primitive}
    (represented : ControlRep world
      (.pattern environment (.suspended inner) (.address address)) view) :
    ∃ caller meaning, world address = some meaning ∧
      view = .pattern caller (.suspended inner) meaning.value := by
  cases represented with
  | pattern pattern captured value =>
      cases value with
      | address found => exact ⟨_, _, found, rfl⟩

/-- The frame index identifies an actual pending occurrence. Caller captures
and inner patterns may differ; the immutable address meaning identifies the
same body input. Every finite pure outcome is excluded. -/
theorem ConfigRep.active_force_pure_not_terminates
    {parameters : Machine.Parameters Primitive} {world : World Primitive}
    {raw : Core.Machine.Config Primitive} {view : Machine.Config Primitive}
    {environment oldEnvironment : Core.Env Primitive} {inner oldInner : Core.Pattern}
    {address index : Nat} (represented : ConfigRep parameters world raw view)
    (forcing : raw.control = .pattern environment (.suspended inner) (.address address))
    (active : raw.stack[index]? = some (.memoize address oldEnvironment oldInner)) :
    ¬Progress.Terminates (Machine.step parameters) view := by
  have control := represented.control
  rw [forcing] at control
  obtain ⟨caller, meaning, found, pureControl⟩ := force_control_meaning control
  have histories := represented.histories
  rw [pureControl] at histories
  have blocked := histories.reentry_not_terminates active found
  have entered : Reaches parameters 1 view
      (Machine.appendFrames (Machine.start meaning.environment meaning.body)
        (.force caller inner :: view.stack)) := by
    apply Reaches.one
    rcases view with ⟨current, stack⟩
    change current = .pattern caller (.suspended inner) meaning.value at pureControl
    subst current
    rfl
  exact entered.not_terminates (Machine.not_terminates_append blocked _)

end Suspensions.Pure.Simulation
