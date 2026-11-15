import Applications.Suspensions.BodyEvent

/-!
# Exact body events, cache hits and missing-address faults

Two actual allocations store identical code and captures at addresses 0 and 1.
Forcing address 1 enters its captured variable body, ignoring the caller's
shadowing binding, and does not emit a body event for address 0. The five-step
execution writes 7 at address 1 and leaves address 0 unforced. Repeating the
same suspended match observes a cache hit. A missing address faults instead.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionBodyEvent
open Suspensions Suspensions.Core Suspensions.Core.Machine

private def parameters : Parameters Unit where
  primitive := fun _ _ => .stuck .primitive
  matchException := 0
  bindException := 1

private def code : Expr Unit := .variable 9
private def captured : Env Unit := [(9, .atom (.integer 7))]
private def caller : Env Unit := [(9, .atom (.integer 99))]
private def inner : Pattern := .variable 3

private def first : Memory Unit := (Suspensions.delay Suspensions.empty code captured).1
private def memory : Memory Unit := (Suspensions.delay first code captured).1
private def entering : Config Unit := startPattern memory caller (.suspended inner) (.address 1)
private def cached : Memory Unit := Suspensions.memoize memory 1 (.atom (.integer 7))
private def hitting : Config Unit := startPattern cached caller (.suspended inner) (.address 1)
private def missing : Config Unit := startPattern memory caller (.suspended inner) (.address 4)

/-- Equal stored bodies do not identify their allocation addresses. The event
is obtained through the general iff, with the actual current thunk lookup. -/
theorem uncached_entry :
    memory.memory 0 = some (.thunk code captured) ∧
    memory.memory 1 = some (.thunk code captured) ∧
    transition parameters entering =
      proceed memory (.eval captured code) [.memoize 1 caller inner] (.body 1) ∧
    (transition parameters entering).2 = .body 1 ∧
    (transition parameters entering).2 ≠ .body 0 := by
  have found : memory.memory 1 = some (.thunk code captured) := rfl
  have observed := (body_event_iff parameters entering 1).mpr
    ⟨caller, inner, code, captured, rfl, found⟩
  exact ⟨rfl, found, body_transition parameters memory caller captured inner 1 code [] found,
    observed, fun other => Nat.one_ne_zero (body_event_address_unique observed other)⟩

/-- The same characterization applies with existing caller frames. Entering
the body pushes its memoize frame ahead of that unchanged tail. -/
theorem entry_with_caller :
    (transition parameters {entering with stack := [.constructor 8]}).2 = .body 1 ∧
    transition parameters {entering with stack := [.constructor 8]} =
      proceed memory (.eval captured code)
        [.memoize 1 caller inner, .constructor 8] (.body 1) :=
  ⟨(body_event_iff parameters _ 1).mpr ⟨caller, inner, code, captured, rfl, rfl⟩,
    body_transition parameters memory caller captured inner 1 code [.constructor 8] rfl⟩

/-- Body entry, variable evaluation, memoization, variable matching and final
delivery are five actual transitions. Only the inspected address is written. -/
theorem uncached_evaluation :
    Progress.Evaluates (step parameters) entering
      ⟨cached, .matched [(3, .atom (.integer 7))]⟩ 5 ∧
    cached.memory 1 = some (.value (.atom (.integer 7))) ∧
    cached.memory 0 = some (.thunk code captured) :=
  ⟨.next rfl (.next rfl (.next rfl (.next rfl (.done rfl)))), rfl, rfl⟩

/-- The state produced by the preceding execution gives a hit, never a new
body event, for every candidate event address. -/
theorem cached_hit :
    transition parameters hitting =
      proceed cached (.pattern caller inner (.atom (.integer 7))) [] (.hit 1) ∧
    ∀ address, (transition parameters hitting).2 ≠ .body address := by
  have hit := hit_transition parameters cached caller inner 1 (.atom (.integer 7)) [] rfl
  have hitEvent : (transition parameters hitting).2 = .hit 1 := congrArg Prod.snd hit
  refine ⟨hit, ?_⟩
  intro address event
  have impossible := hitEvent.symm.trans event
  cases impossible

/-- The exact event characterization rejects a putative uncached origin at
the cached state, rather than interpreting equal returned values as entry. -/
theorem cached_has_no_body_origin (address : Nat) :
    ¬ ∃ environment pattern body capture,
      hitting.control = .pattern environment (.suspended pattern) (.address address) ∧
        hitting.memory.memory address = some (.thunk body capture) :=
  (body_event_iff parameters hitting address).not.mp (cached_hit.2 address)

/-- A missing-address fault retains the input memory and emits the ordinary
core event. It is not a body entry or a successful cached observation. -/
theorem missing_address_fault :
    transition parameters missing = finish memory (.stuck (.missingAddress 4)) ∧
    ∀ address, (transition parameters missing).2 ≠ .body address := by
  refine ⟨rfl, ?_⟩
  intro address event
  cases event

theorem missing_has_no_body_origin (address : Nat) :
    ¬ ∃ environment pattern body capture,
      missing.control = .pattern environment (.suspended pattern) (.address address) ∧
        missing.memory.memory address = some (.thunk body capture) :=
  (body_event_iff parameters missing address).not.mp (missing_address_fault.2 address)

end Examples.SuspensionBodyEvent
