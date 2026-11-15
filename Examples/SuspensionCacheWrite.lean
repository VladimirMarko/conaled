import Applications.Suspensions.CacheWrite
import Examples.SuspensionPending
import Examples.SuspensionMachine

/-!
# Successful writes, pending callers and later effects

The first literal force takes five actual transitions. Its third transition
writes 7 and removes the only memoize frame, so every later unfinished
observation is settled at that address. The two delivery transitions and any
absorbing observation suffix retain the value-cell fact.

The later cases distinguish an older pending write, reference assignment of
an arbitrary payload, and an outer exception retaining an inner cache. Their
expected behavior follows the actual continuation order, not a purity or
single-write assumption.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionCacheWrite
open Suspensions Suspensions.Core Suspensions.Core.Machine

namespace FirstForce
open Examples.SuspensionPending

private def returning : Config Unit :=
  ⟨memory, .value (.atom (.integer 7)), [.memoize 0 [] .wildcard]⟩

private def afterWrite : Config Unit :=
  ⟨Suspensions.memoize memory 0 (.atom (.integer 7)),
    .pattern [] .wildcard (.atom (.integer 7)), []⟩

/-- The actual first body entry supplies the unique pending frame. Returning
through it gives the general settled conclusion before inner matching. -/
theorem first_force_settles :
    Prefix.observe parameters 2 firstForce = .inr returning ∧
    (transition parameters returning).2 = .cacheWrite 0 ∧
    step parameters returning = .inr afterWrite ∧
    Settled 0 afterWrite ∧ ConfigBounded afterWrite := by
  have reached : Prefix.observe parameters 2 firstForce = .inr returning := rfl
  have write : (transition parameters returning).2 = .cacheWrite 0 :=
    (cacheWrite_event_iff parameters returning 0).mpr
      ⟨.atom (.integer 7), [], .wildcard, [], rfl, rfl⟩
  have distinct : (pendingAddresses returning.stack).Nodup := first_body_is_unique
  have moved : step parameters returning = .inr afterWrite := rfl
  obtain ⟨next, actual, settled⟩ := cacheWrite_settles distinct write
  have same : next = afterWrite := Sum.inr.inj (actual.symm.trans moved)
  subst next
  have valid : ConfigBounded firstForce :=
    startPattern_bounded (Suspensions.delay_bounded Suspensions.bounded_empty body [])
      [] (.suspended .wildcard) (.address 0)
  have nextBounded := step_bounded (parameters := parameters)
    (observe_unfinished_bounded valid reached)
  rw [moved] at nextBounded
  exact ⟨reached, write, moved, settled, nextBounded⟩

theorem later_unfinished_has_no_write (budget : Nat) (next : Config Unit)
    (observed : Prefix.observe parameters budget afterWrite = .inr next) :
    Settled 0 next ∧ (transition parameters next).2 ≠ .cacheWrite 0 := by
  obtain ⟨_, _, _, settled, valid⟩ := first_force_settles
  exact ⟨observe_unfinished_settled valid settled observed,
    observe_no_cacheWrite valid settled observed⟩

theorem first_force_completes :
    Progress.Evaluates (step parameters) firstForce
      ⟨afterWrite.memory, .matched []⟩ 5 :=
  .next rfl (.next rfl (.next rfl (.next rfl (.done rfl))))

/-- The remaining two transitions deliver the match answer. A larger observer
budget absorbs that answer; it does not assert additional machine work. -/
theorem finished_observation_keeps_value (extra : Nat) :
    Prefix.observe parameters (2 + extra) afterWrite =
      .inl ⟨afterWrite.memory, .matched []⟩ ∧ HasValue afterWrite.memory 0 := by
  obtain ⟨_, _, _, settled, valid⟩ := first_force_settles
  have finished : Prefix.observe parameters 2 afterWrite =
      .inl ⟨afterWrite.memory, .matched []⟩ := rfl
  have observed := Prefix.stays_finished parameters 2 extra afterWrite _ finished
  have kept := observe_settled (parameters := parameters) valid settled (2 + extra)
  rw [observed] at kept
  exact ⟨observed, kept⟩

end FirstForce

namespace PendingOlder
open Examples.SuspensionPending

private def returning : Config Unit :=
  ⟨memory, .value (.atom (.integer 7)),
    [.memoize 0 [] .wildcard, .bindMatch [] (.atom (.integer 8)),
      .memoize 0 [] .wildcard]⟩

private def afterInner : Config Unit :=
  ⟨Suspensions.memoize memory 0 (.atom (.integer 7)),
    .pattern [] .wildcard (.atom (.integer 7)),
    [.bindMatch [] (.atom (.integer 8)), .memoize 0 [] .wildcard]⟩

private def outerReturning : Config Unit :=
  ⟨afterInner.memory, .value (.atom (.integer 8)), [.memoize 0 [] .wildcard]⟩

private def afterOuter : Config Unit :=
  ⟨Suspensions.memoize afterInner.memory 0 (.atom (.integer 8)),
    .pattern [] .wildcard (.atom (.integer 8)), []⟩

/-- This raw return has two pending occurrences. The inner successful write
retains the older occurrence, so a value cell alone does not make it settled. -/
theorem inner_write_retains_older_frame :
    (transition parameters returning).2 = .cacheWrite 0 ∧
    step parameters returning = .inr afterInner ∧
    HasValue afterInner.memory 0 ∧ ¬ Settled 0 afterInner ∧
    ¬ (pendingAddresses returning.stack).Nodup := by
  have write : (transition parameters returning).2 = .cacheWrite 0 :=
    (cacheWrite_event_iff parameters returning 0).mpr
      ⟨.atom (.integer 7), [], .wildcard,
        [.bindMatch [] (.atom (.integer 8)), .memoize 0 [] .wildcard], rfl, rfl⟩
  refine ⟨write, rfl, ⟨.atom (.integer 7), rfl⟩, ?_, by decide⟩
  intro settled
  exact settled.2 (by simp [afterInner, pendingAddresses, Frame.memoizeAddress])

/-- Inner wildcard matching, binding return and literal evaluation take
three transitions. The older frame then writes 8; only this final write
removes the last pending occurrence and supplies the settled conclusion. -/
theorem old_frame_allows_overwrite :
    Prefix.observe parameters 3 afterInner = .inr outerReturning ∧
    step parameters outerReturning = .inr afterOuter ∧
    (transition parameters outerReturning).2 = .cacheWrite 0 ∧
    Settled 0 afterOuter ∧
    afterInner.memory.memory 0 = some (.value (.atom (.integer 7))) ∧
    afterOuter.memory.memory 0 = some (.value (.atom (.integer 8))) := by
  have write : (transition parameters outerReturning).2 = .cacheWrite 0 :=
    (cacheWrite_event_iff parameters outerReturning 0).mpr
      ⟨.atom (.integer 8), [], .wildcard, [], rfl, rfl⟩
  have distinct : (pendingAddresses outerReturning.stack).Nodup := by decide
  have moved : step parameters outerReturning = .inr afterOuter := rfl
  obtain ⟨next, actual, settled⟩ := cacheWrite_settles distinct write
  have same : next = afterOuter := Sum.inr.inj (actual.symm.trans moved)
  subst next
  exact ⟨rfl, moved, write, settled, rfl, rfl⟩

/-- The raw continuation containing both occurrences has an actual finite
completion. This statement makes no claim that a pure fresh source reaches it. -/
theorem old_frame_execution :
    Progress.Evaluates (step parameters) returning
      ⟨afterOuter.memory, .matched []⟩ 7 :=
  .next inner_write_retains_older_frame.2.1
    (.next rfl (.next rfl (.next rfl
      (.next old_frame_allows_overwrite.2.1 (.next rfl (.done rfl))))))

end PendingOlder

namespace Assignment
open Examples.SuspensionPending

private def environment (replacement : Value Unit) : Env Unit :=
  [(5, .address 0), (6, replacement)]

private def expression : Expr Unit := .assign (.variable 5) (.variable 6)

private def initial (replacement : Value Unit) : Config Unit :=
  start FirstForce.afterWrite.memory (environment replacement) expression

private def beforeWrite (replacement : Value Unit) : Config Unit :=
  ⟨FirstForce.afterWrite.memory, .value replacement, [.assignValue (.address 0)]⟩

private def afterWrite (replacement : Value Unit) : Memory Unit :=
  Suspensions.memoize FirstForce.afterWrite.memory 0 replacement

private theorem initial_bounded (replacement : Value Unit) :
    ConfigBounded (initial replacement) := by
  obtain ⟨_, _, _, _, valid⟩ := FirstForce.first_force_settles
  exact start_bounded valid.1 (environment replacement) expression

private theorem initial_settled (replacement : Value Unit) :
    Settled 0 (initial replacement) := by
  obtain ⟨_, _, _, settled, _⟩ := FirstForce.first_force_settles
  exact ⟨settled.1, List.not_mem_nil⟩

/-- Assignment evaluates both variables, writes the arbitrary replacement,
and returns source unit in six transitions. The write is a reference event;
the settled invariant prohibits a cache-write event at the same transition. -/
theorem assignment_returns_any_payload (replacement : Value Unit) :
    Progress.Evaluates (step parameters) (initial replacement)
      ⟨afterWrite replacement, .value (.record [])⟩ 6 ∧
    (afterWrite replacement).memory 0 = some (.value replacement) ∧
    HasValue (afterWrite replacement) 0 ∧
    (transition parameters (beforeWrite replacement)).2 = .referenceWrite 0 ∧
    (transition parameters (beforeWrite replacement)).2 ≠ .cacheWrite 0 := by
  have run : Progress.Evaluates (step parameters) (initial replacement)
      ⟨afterWrite replacement, .value (.record [])⟩ 6 :=
    .next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.done rfl)))))
  have reached : Prefix.observe parameters 4 (initial replacement) =
      .inr (beforeWrite replacement) := rfl
  have settled := observe_unfinished_settled (initial_bounded replacement)
    (initial_settled replacement) reached
  have completed : Prefix.observe parameters 6 (initial replacement) =
      .inl ⟨afterWrite replacement, .value (.record [])⟩ :=
    (Prefix.finished_iff parameters 6 (initial replacement) _).mpr
      ⟨6, Nat.le_refl 6, run⟩
  have kept := observe_settled (parameters := parameters) (initial_bounded replacement)
    (initial_settled replacement) 6
  rw [completed] at kept
  exact ⟨run, Suspensions.memoize_lookup _ 0 replacement, kept, rfl, settled.no_cacheWrite⟩

/-- Every unfinished prefix, including the post-assignment value control,
retains the settled property with its current payload. -/
theorem assignment_prefixes_settled (replacement : Value Unit) (budget : Nat) (next : Config Unit)
    (observed : Prefix.observe parameters budget (initial replacement) = .inr next) :
    Settled 0 next ∧ (transition parameters next).2 ≠ .cacheWrite 0 :=
  ⟨observe_unfinished_settled (initial_bounded replacement) (initial_settled replacement) observed,
    observe_no_cacheWrite (initial_bounded replacement) (initial_settled replacement) observed⟩

theorem seven_to_eight :
    (afterWrite (.atom (.integer 8))).memory 0 ≠ FirstForce.afterWrite.memory.memory 0 ∧
    HasValue (afterWrite (.atom (.integer 8))) 0 := by
  refine ⟨?_, (assignment_returns_any_payload (.atom (.integer 8))).2.2.1⟩
  intro same
  have integers : (8 : Int) = 7 :=
    Atom.integer.inj (Value.atom.inj (Cell.value.inj (Option.some.inj same)))
  exact (by decide : (8 : Int) ≠ 7) integers

end Assignment

namespace Exceptions
open Examples.SuspensionMachine

/-- The existing effectful source enters the same body twice, caches the
inner 7, then raises from the outer body. Its actual completed memory supplies
a settled later force, whose transition hits that retained cache. -/
theorem outer_exception_keeps_a_settled_cache :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters)
        (start initial [] (reentrantRaises (force (.variable 2))), []) (answer, events) steps ∧
      answer.result = .raised (.exception 2 none) ∧
      answer.memory.memory 1 = some (.value (.atom (.integer 7))) ∧
      events.count (.body 1) = 2 ∧ events.count (.cacheWrite 1) = 1 ∧
      Settled 1 (startPattern answer.memory [] (.suspended .wildcard) (.address 1)) ∧
      transition parameters (startPattern answer.memory [] (.suspended .wildcard) (.address 1)) =
        proceed answer.memory (.pattern [] .wildcard (.atom (.integer 7))) [] (.hit 1) ∧
      ∀ budget next,
        Prefix.observe parameters budget
          (startPattern answer.memory [] (.suspended .wildcard) (.address 1)) = .inr next →
        Settled 1 next ∧ (transition parameters next).2 ≠ .cacheWrite 1 := by
  obtain ⟨answer, events, steps, run, raised, cached, bodies, writes⟩ :=
    outer_exception_preserves_inner
  have initialBounded : Suspensions.Bounded initial := Suspensions.bounded_empty
  have bounded := start_evaluates_bounded initialBounded (traced_evaluates_erases run)
  have settled : Settled 1
      (startPattern answer.memory [] (.suspended .wildcard) (.address 1)) :=
    ⟨⟨.atom (.integer 7), cached⟩, List.not_mem_nil⟩
  refine ⟨answer, events, steps, run, raised, cached, bodies, writes, settled,
    hit_transition parameters answer.memory [] .wildcard 1 (.atom (.integer 7)) [] cached, ?_⟩
  intro budget next observed
  have valid := startPattern_bounded bounded [] (.suspended .wildcard) (.address 1)
  exact ⟨observe_unfinished_settled valid settled observed,
    observe_no_cacheWrite valid settled observed⟩

end Exceptions
end Examples.SuspensionCacheWrite
