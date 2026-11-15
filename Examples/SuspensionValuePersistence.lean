import Applications.Suspensions.ValuePersistence
import Examples.SuspensionMachine

/-!
# Persistent value cells with mutable payloads

An actual assignment changes an occupied value from 7 to 8 in six transitions.
The general persistence law retains a value cell throughout that execution.
A following suspended force reaches its hit transition after an actual
15-step prefix, and observes the new payload 8.

The existing effectful reentrant program keeps its two cache writes and final
8; its completed memory supports the new future no-body conclusion. A separate
raised-body execution leaves a thunk unchanged and can repeat. Neither case
is excluded by a new typing, purity or no-reentry assumption.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionValuePersistence
open Suspensions Suspensions.Core Suspensions.Core.Machine

private def unitParameters : Parameters Unit where
  primitive := fun _ _ => .stuck .primitive
  matchException := 0
  bindException := 1

namespace Mutation

private def memory : Memory Unit :=
  (Suspensions.allocate Suspensions.empty (.value (.atom (.integer 7)))).1
private def environment : Env Unit := [(5, .address 0)]
private def assignment : Expr Unit := .assign (.variable 5) (.atom (.integer 8))
private def after : Memory Unit := Suspensions.memoize memory 0 (.atom (.integer 8))
private def initialConfig : Config Unit := start memory environment assignment

private theorem bounded : Suspensions.Bounded memory :=
  Suspensions.allocate_bounded Suspensions.bounded_empty _

private theorem present : HasValue memory 0 := ⟨.atom (.integer 7), rfl⟩

/-- The constructor persists while the payload changes. This is an actual
effectful source assignment, not merely a store-operation equation. -/
theorem assignment_overwrites :
    Progress.Evaluates (step unitParameters) initialConfig ⟨after, .value (.record [])⟩ 6 ∧
    memory.memory 0 = some (.value (.atom (.integer 7))) ∧
    after.memory 0 = some (.value (.atom (.integer 8))) ∧
    HasValue after 0 ∧ after.memory 0 ≠ memory.memory 0 := by
  have run : Progress.Evaluates (step unitParameters) initialConfig ⟨after, .value (.record [])⟩ 6 :=
    .next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.done rfl)))))
  have kept := start_evaluates_hasValue bounded present run
  refine ⟨run, rfl, rfl, kept, ?_⟩
  intro same
  have integers : (8 : Int) = 7 :=
    Atom.integer.inj (Value.atom.inj (Cell.value.inj (Option.some.inj same)))
  exact (by decide : (8 : Int) ≠ 7) integers

/-- Every actual unfinished observation carries the old invariant and the
new value-cell property; no later transition enters this address as a body. -/
theorem assignment_prefixes (budget : Nat) (next : Config Unit)
    (observed : Prefix.observe unitParameters budget initialConfig = .inr next) :
    ConfigBounded next ∧ HasValue next.memory 0 ∧
      (transition unitParameters next).2 ≠ .body 0 := by
  have valid : ConfigBounded initialConfig := start_bounded bounded environment assignment
  exact ⟨observe_unfinished_bounded valid observed,
    observe_unfinished_hasValue valid present observed, observe_no_body valid present observed⟩

private def forceAfterAssignment : Expr Unit :=
  .bind .wildcard assignment (force (.variable 5))

private def aboutToHit : Config Unit :=
  ⟨after, .pattern environment (.suspended (.variable 0)) (.address 0),
    [.clause environment (.variable 0) [] (.address 0), .applicationResult]⟩

/-- Nine transitions complete assignment/binding; six more reach the cached
force's suspended pattern. The public prefix law supplies the actual hit. -/
theorem later_force_hits_new_payload :
    Prefix.observe unitParameters 15 (start memory environment forceAfterAssignment) = .inr aboutToHit ∧
    transition unitParameters aboutToHit =
      proceed after (.pattern environment (.variable 0) (.atom (.integer 8)))
        aboutToHit.stack (.hit 0) ∧
    (transition unitParameters aboutToHit).2 ≠ .body 0 := by
  have reached : Prefix.observe unitParameters 15 (start memory environment forceAfterAssignment) =
      .inr aboutToHit := rfl
  have valid := start_bounded bounded environment forceAfterAssignment
  obtain ⟨value, found, hit⟩ := observe_force_hit valid present reached rfl
  have expected : aboutToHit.memory.memory 0 = some (.value (.atom (.integer 8))) := rfl
  have same := Cell.value.inj (Option.some.inj (found.symm.trans expected))
  subst value
  exact ⟨reached, hit, observe_no_body valid present reached⟩

end Mutation

namespace Reentrant
open Examples.SuspensionMachine

/-- The original actual source run still writes the same cache twice. Value
persistence is compatible with this effectful overwrite; after completion,
every later observed force state retains a value and cannot emit body 1. -/
theorem two_writes_remain :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters) (start initial [] reentrantOverwrite, [])
        (answer, events) steps ∧
      answer.result = .value (.atom (.integer 8)) ∧
      answer.memory.memory 1 = some (.value (.atom (.integer 8))) ∧
      events.count (.body 1) = 2 ∧ events.count (.cacheWrite 1) = 2 ∧ events.count (.hit 1) = 1 ∧
      HasValue answer.memory 1 ∧
      ∀ budget next,
        Prefix.observe parameters budget (startPattern answer.memory [] (.suspended .wildcard) (.address 1)) =
          .inr next → (transition parameters next).2 ≠ .body 1 := by
  obtain ⟨answer, events, steps, run, result, cached, _, bodies, writes, hits⟩ := reentrant_overwrite
  have value : HasValue answer.memory 1 := ⟨.atom (.integer 8), cached⟩
  have initialBounded : Suspensions.Bounded initial := Suspensions.bounded_empty
  have afterBounded := start_evaluates_bounded initialBounded (traced_evaluates_erases run)
  refine ⟨answer, events, steps, run, result, cached, bodies, writes, hits, value, ?_⟩
  intro budget next observed
  exact observe_no_body (startPattern_bounded afterBounded [] (.suspended .wildcard) (.address 1))
    value observed

end Reentrant

namespace Exceptions

private def packet : Value Unit := .exception 11 none
private def capture : Env Unit := [(9, packet)]
private def code : Expr Unit := .raise (.variable 9)
private def memory : Memory Unit := (Suspensions.delay Suspensions.empty code capture).1
private def forcing : Config Unit := startPattern memory [] (.suspended .wildcard) (.address 0)

/-- Raising the body packet skips its pending memoize frame. The unchanged
thunk supports another identical actual six-step run and another body event. -/
theorem raised_body_can_repeat :
    Suspensions.Bounded memory ∧
    Progress.Evaluates (step unitParameters) forcing ⟨memory, .raised packet⟩ 6 ∧
    Progress.Evaluates (step unitParameters)
      (startPattern memory [] (.suspended .wildcard) (.address 0)) ⟨memory, .raised packet⟩ 6 ∧
    memory.memory 0 = some (.thunk code capture) ∧
    ¬ HasValue memory 0 ∧ (transition unitParameters forcing).2 = .body 0 := by
  have run : Progress.Evaluates (step unitParameters) forcing ⟨memory, .raised packet⟩ 6 :=
    .next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.done rfl)))))
  have thunk : memory.memory 0 = some (.thunk code capture) := rfl
  refine ⟨Suspensions.delay_bounded Suspensions.bounded_empty code capture, run, run, thunk, ?_, ?_⟩
  · rintro ⟨value, found⟩
    rw [thunk] at found
    cases found
  · exact (body_event_iff unitParameters forcing 0).mpr ⟨[], .wildcard, code, capture, rfl, thunk⟩

end Exceptions
end Examples.SuspensionValuePersistence
