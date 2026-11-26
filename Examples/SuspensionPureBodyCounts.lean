import Applications.Suspensions.Pure.BodyCounts
import Examples.SuspensionPureCacheCounts
import Mathlib.Tactic.IntervalCases

/-!
# Actual source bodies with retained and abandoned memoization

The successful repeated-force and distinct-allocation programs are the existing
source examples. Their finite executions discharge freshness through the pure
source theorem, while their actual prefixes establish the separate no-unwind
condition. A handler inside a delayed body can catch an exception before the
memoize frame is exposed. Moving the handler outside permits uncached retry:
the existing finite pure example still enters its body twice and writes zero
times, and therefore fails the new condition.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureBodyCounts
open Suspensions Suspensions.Pure
open Suspensions.Pure.Representation Suspensions.Pure.Domain
open Suspensions.Pure.DomainState Suspensions.Pure.WorldDomain
open Suspensions.Pure.Compatibility Suspensions.Pure.Simulation

abbrev rawParameters := Examples.SuspensionPureCachedClosure.rawParameters
private abbrev pureParameters := Examples.SuspensionPureMachine.parameters
private def Operations : Empty → Prop := fun _ => False

private theorem compatible : ParametersCompatible Operations rawParameters pureParameters where
  primitive impossible := nomatch impossible
  matchException := rfl
  bindException := rfl

private theorem preserve : ParametersPreserve Operations pureParameters := by
  intro impossible
  cases impossible

private theorem empty_source_bound {program : Core.Expr Empty}
    {answer : Core.Machine.Answer Empty} {steps : Nat}
    (code : CodeAllowed Operations program)
    (run : Progress.Evaluates (Core.Machine.step rawParameters)
      (Core.Machine.start Suspensions.empty [] program) answer steps)
    (address : Nat)
    (safe : Core.Machine.NoMemoizeUnwind rawParameters
      (Core.Machine.start Suspensions.empty [] program) address)
    (budget : Nat) :
    Core.Observation.bodyEntries address
      (Core.Observation.observe rawParameters budget
        (Core.Machine.start Suspensions.empty [] program)).2 ≤ 1 :=
  source_bodyEntries_le_one compatible preserve WorldAllowed.empty
    (Memory.StateRep.empty pureParameters) EnvRep.nil EnvAllowed.nil code run address safe budget

namespace Repeated

abbrev program := Examples.SuspensionPureCacheCounts.Repeated.program

private theorem allowed : CodeAllowed Operations program := by
  apply (CodeAllowed.bind_iff _ _ _).mpr
  refine ⟨.variable 0, (CodeAllowed.delay_iff _).mpr (CodeAllowed.atom (.integer 7)), ?_⟩
  apply (CodeAllowed.bind_iff _ _ _).mpr
  refine ⟨.suspended .wildcard, CodeAllowed.variable 0, ?_⟩
  apply (CodeAllowed.bind_iff _ _ _).mpr
  exact ⟨.suspended .wildcard, CodeAllowed.variable 0, CodeAllowed.atom (.integer 9)⟩

private theorem execution :
    ∃ answer, Progress.Evaluates (Core.Machine.step rawParameters)
      (Core.Machine.start Suspensions.empty [] program) answer 21 ∧
      answer.result = .value (.atom (.integer 9)) := by
  refine ⟨_, Progress.search_sound (fuel := 21) (by rfl), ?_⟩
  rfl

/-- Every actual pre-completion control in this program is non-raised. The
finite-prefix proof covers arbitrary addresses; absorbing suffixes add none. -/
theorem no_unwind (address : Nat) :
    Core.Machine.NoMemoizeUnwind rawParameters
      (Core.Machine.start Suspensions.empty [] program) address := by
  obtain ⟨answer, finished⟩ : ∃ answer, Core.Prefix.observe rawParameters 21
      (Core.Machine.start Suspensions.empty [] program) = .inl answer := ⟨_, rfl⟩
  apply Core.Machine.NoMemoizeUnwind.of_finished finished
  intro index before next reached
  interval_cases index
  all_goals
    have same := Sum.inr.inj reached
    subst next
    rintro ⟨packet, environment, inner, rest, control, _⟩
    cases control

/-- The actual source theorem supplies the bound for every budget, rather
than using the independently computed completed trace as an assumed bound. -/
theorem all_budgets (address budget : Nat) :
    Core.Observation.bodyEntries address
      (Core.Observation.observe rawParameters budget
        (Core.Machine.start Suspensions.empty [] program)).2 ≤ 1 := by
  obtain ⟨answer, run, _⟩ := execution
  exact empty_source_bound allowed run address (no_unwind address) budget

theorem all_counts (address budget : Nat) :
    (FreeAddMonoid.toList (Core.Observation.observe rawParameters budget
      (Core.Machine.start Suspensions.empty [] program)).2).count (.body address) ≤ 1 := by
  simpa only [Core.Observation.bodyEntries_eq_count] using all_budgets address budget

/-- The first body event precedes its write. The universal bound already
applies to this unfinished observation with its actual pending frame. -/
theorem first_force_pending :
    ∃ config, Core.Prefix.observe rawParameters 9
      (Core.Machine.start Suspensions.empty [] program) = .inr config ∧
      0 ∈ Core.Machine.pendingAddresses config.stack ∧
      Core.Observation.bodyEntries 0 (Core.Observation.observe rawParameters 9
        (Core.Machine.start Suspensions.empty [] program)).2 = 1 ∧
      Core.Observation.cacheWrites 0 (Core.Observation.observe rawParameters 9
        (Core.Machine.start Suspensions.empty [] program)).2 = 0 ∧
      Core.Observation.bodyEntries 0 (Core.Observation.observe rawParameters 9
        (Core.Machine.start Suspensions.empty [] program)).2 ≤ 1 := by
  refine ⟨_, rfl, ?_, ?_, rfl, all_budgets 0 9⟩
  · change 0 ∈ [0]
    exact List.mem_cons_self
  · rw [Core.Observation.bodyEntries_eq_count]
    rfl

/-- The unchanged source observation independently attains the derived bound
and then hits the cache on its second force. -/
theorem one_attempt_then_hit :
    let events := FreeAddMonoid.toList (Core.Observation.observe rawParameters 21
      (Core.Machine.start Suspensions.empty [] program)).2
    events.count (.body 0) = 1 ∧ events.count (.cacheWrite 0) = 1 ∧ events.count (.hit 0) = 1 :=
  Examples.SuspensionPureCacheCounts.Repeated.one_write_then_hit

end Repeated

namespace Distinct

abbrev program := Examples.SuspensionPureCacheCounts.Distinct.program

private theorem allowed : CodeAllowed Operations program := by
  apply (CodeAllowed.bind_iff _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · change PatternAllowed (.record [(0, .variable 1), (1, .variable 2)])
    repeat' constructor
  · apply (CodeAllowed.record_iff _).mpr
    apply (NamedCodeAllowed.cons_iff _ _ _).mpr
    refine ⟨(CodeAllowed.delay_iff _).mpr (CodeAllowed.atom (.integer 7)), ?_⟩
    apply (NamedCodeAllowed.cons_iff _ _ []).mpr
    exact ⟨(CodeAllowed.delay_iff _).mpr (CodeAllowed.atom (.integer 7)), NamedCodeAllowed.nil⟩
  · apply (CodeAllowed.bind_iff _ _ _).mpr
    refine ⟨.suspended .wildcard, CodeAllowed.variable 1, ?_⟩
    apply (CodeAllowed.bind_iff _ _ _).mpr
    exact ⟨.suspended .wildcard, CodeAllowed.variable 2, CodeAllowed.atom (.integer 9)⟩

private theorem execution :
    ∃ answer, Progress.Evaluates (Core.Machine.step rawParameters)
      (Core.Machine.start Suspensions.empty [] program) answer 34 ∧
      answer.result = .value (.atom (.integer 9)) ∧ answer.memory.next = 2 := by
  refine ⟨_, Progress.search_sound (fuel := 34) (by rfl), ?_, ?_⟩ <;> rfl

theorem no_unwind (address : Nat) :
    Core.Machine.NoMemoizeUnwind rawParameters
      (Core.Machine.start Suspensions.empty [] program) address := by
  obtain ⟨answer, finished⟩ : ∃ answer, Core.Prefix.observe rawParameters 34
      (Core.Machine.start Suspensions.empty [] program) = .inl answer := ⟨_, rfl⟩
  apply Core.Machine.NoMemoizeUnwind.of_finished finished
  intro index before next reached
  interval_cases index
  all_goals
    have same := Sum.inr.inj reached
    subst next
    rintro ⟨packet, environment, inner, rest, control, _⟩
    cases control

theorem all_budgets (address budget : Nat) :
    Core.Observation.bodyEntries address
      (Core.Observation.observe rawParameters budget
        (Core.Machine.start Suspensions.empty [] program)).2 ≤ 1 := by
  obtain ⟨answer, run, _, _⟩ := execution
  exact empty_source_bound allowed run address (no_unwind address) budget

theorem all_counts (address budget : Nat) :
    (FreeAddMonoid.toList (Core.Observation.observe rawParameters budget
      (Core.Machine.start Suspensions.empty [] program)).2).count (.body address) ≤ 1 := by
  simpa only [Core.Observation.bodyEntries_eq_count] using all_budgets address budget

/-- The two existing delay allocations have equal code and empty captures,
but their actual body events still name two different physical addresses. -/
theorem identical_thunks_separate_entries :
    (∃ config, Core.Prefix.observe rawParameters 6
      (Core.Machine.start Suspensions.empty [] program) = .inr config ∧
      config.memory.memory 0 = some (.thunk (.atom (.integer 7)) []) ∧
      config.memory.memory 1 = some (.thunk (.atom (.integer 7)) []) ∧ config.memory.next = 2) ∧
    (let events := FreeAddMonoid.toList (Core.Observation.observe rawParameters 34
      (Core.Machine.start Suspensions.empty [] program)).2;
      events.count (.body 0) = 1 ∧ events.count (.body 1) = 1) := by
  constructor
  · exact Examples.SuspensionPureCacheCounts.Distinct.identical_thunks_at_distinct_addresses
  · exact ⟨rfl, rfl⟩

end Distinct

namespace InternalHandler

def rawCapture : Core.Env Empty := [(3, .exception 17 none)]
private def capture : Env Empty := [(3, .exception 17 none)]
def body : Core.Expr Empty :=
  .handle (.raise (.variable 3)) [(.exception 3 none, .atom (.integer 7))]
def program : Core.Expr Empty :=
  .bind (.variable 1) (.delay body)
    (.bind (.suspended .wildcard) (.variable 1)
      (.bind (.suspended .wildcard) (.variable 1) (.atom (.integer 9))))

private theorem body_allowed : CodeAllowed Operations body := by
  apply (CodeAllowed.handle_iff _ _).mpr
  refine ⟨(CodeAllowed.raise_iff _).mpr (CodeAllowed.variable 3), ?_⟩
  apply (ClausesCodeAllowed.cons_iff _ _ []).mpr
  exact ⟨.exception 3, CodeAllowed.atom (.integer 7), ClausesCodeAllowed.nil⟩

private theorem allowed : CodeAllowed Operations program := by
  apply (CodeAllowed.bind_iff _ _ _).mpr
  refine ⟨.variable 1, (CodeAllowed.delay_iff _).mpr body_allowed, ?_⟩
  apply (CodeAllowed.bind_iff _ _ _).mpr
  refine ⟨.suspended .wildcard, CodeAllowed.variable 1, ?_⟩
  apply (CodeAllowed.bind_iff _ _ _).mpr
  exact ⟨.suspended .wildcard, CodeAllowed.variable 1, CodeAllowed.atom (.integer 9)⟩

private theorem execution :
    ∃ answer, Progress.Evaluates (Core.Machine.step rawParameters)
      (Core.Machine.start Suspensions.empty rawCapture program) answer 30 ∧
      answer.result = .value (.atom (.integer 9)) := by
  refine ⟨_, Progress.search_sound (fuel := 30) (by rfl), ?_⟩
  rfl

/-- Raised control occurs, but its top frame is the body's own handler; the
pending outer memoize frame remains below it. Thus exceptions are permitted. -/
theorem caught_before_memoize :
    ∃ config, Core.Prefix.observe rawParameters 13
      (Core.Machine.start Suspensions.empty rawCapture program) = .inr config ∧
      config.control = .raised (.exception 17 none) ∧
      0 ∈ Core.Machine.pendingAddresses config.stack ∧
      ¬ Core.Machine.UnwindsMemoize 0 config := by
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · change 0 ∈ [0]
    exact List.mem_cons_self
  · rintro ⟨packet, environment, inner, rest, _, stack⟩
    cases stack

/-- The complete finite-prefix check permits the actual raised/handler state.
It rules out only a raised control with the selected memoize frame on top. -/
theorem no_unwind (address : Nat) :
    Core.Machine.NoMemoizeUnwind rawParameters
      (Core.Machine.start Suspensions.empty rawCapture program) address := by
  obtain ⟨answer, finished⟩ : ∃ answer, Core.Prefix.observe rawParameters 30
      (Core.Machine.start Suspensions.empty rawCapture program) = .inl answer := ⟨_, rfl⟩
  apply Core.Machine.NoMemoizeUnwind.of_finished finished
  intro index before next reached
  interval_cases index
  all_goals
    have same := Sum.inr.inj reached
    subst next
    rintro ⟨packet, environment, inner, rest, control, stack⟩
    cases control
  all_goals cases stack

theorem all_budgets (address budget : Nat) :
    Core.Observation.bodyEntries address
      (Core.Observation.observe rawParameters budget
        (Core.Machine.start Suspensions.empty rawCapture program)).2 ≤ 1 := by
  obtain ⟨answer, run, _⟩ := execution
  have captured : EnvRep (fun _ => none) rawCapture capture := .cons (.exception .none) .nil
  have captureAllowed : EnvAllowed Operations capture := .cons (.exception .none) .nil
  exact source_bodyEntries_le_one compatible preserve WorldAllowed.empty
    (Memory.StateRep.empty pureParameters) captured captureAllowed allowed run
    address (no_unwind address) budget

theorem all_counts (address budget : Nat) :
    (FreeAddMonoid.toList (Core.Observation.observe rawParameters budget
      (Core.Machine.start Suspensions.empty rawCapture program)).2).count (.body address) ≤ 1 := by
  simpa only [Core.Observation.bodyEntries_eq_count] using all_budgets address budget

theorem one_attempt_then_hit :
    let events := FreeAddMonoid.toList (Core.Observation.observe rawParameters 30
      (Core.Machine.start Suspensions.empty rawCapture program)).2
    events.count (.body 0) = 1 ∧ events.count (.cacheWrite 0) = 1 ∧ events.count (.hit 0) = 1 := by
  exact ⟨rfl, rfl, rfl⟩

end InternalHandler

namespace ExternalHandler

def rawCapture : Core.Env Empty := [(3, .exception 17 none)]
private def capture : Env Empty := [(3, .exception 17 none)]
abbrev program := Examples.SuspensionPureCacheCounts.Exceptions.program

private def handler (result : Core.Expr Empty) : Core.Expr Empty :=
  .handle (Core.force (.variable 1)) [(.exception 3 none, result)]

private theorem handler_allowed {result : Core.Expr Empty} (code : CodeAllowed Operations result) :
    CodeAllowed Operations (handler result) := by
  apply (CodeAllowed.handle_iff _ _).mpr
  refine ⟨(CodeAllowed.variable 1).force, ?_⟩
  apply (ClausesCodeAllowed.cons_iff _ _ []).mpr
  exact ⟨.exception 3, code, ClausesCodeAllowed.nil⟩

private theorem allowed : CodeAllowed Operations program := by
  apply (CodeAllowed.bind_iff _ _ _).mpr
  refine ⟨.variable 1, (CodeAllowed.delay_iff _).mpr
    ((CodeAllowed.raise_iff _).mpr (CodeAllowed.variable 3)), ?_⟩
  apply (CodeAllowed.bind_iff _ _ _).mpr
  exact ⟨.wildcard, handler_allowed ((CodeAllowed.record_iff []).mpr NamedCodeAllowed.nil),
    handler_allowed (CodeAllowed.atom (.integer 5))⟩

private theorem execution :
    ∃ answer, Progress.Evaluates (Core.Machine.step rawParameters)
      (Core.Machine.start Suspensions.empty rawCapture program) answer 50 ∧
      answer.result = .value (.atom (.integer 5)) := by
  refine ⟨_, Progress.search_sound (fuel := 50) (by rfl), ?_⟩
  rfl

/-- This is the original finite pure source observation, with unchanged
program, capture, budget and independent two-attempt/zero-write expectation. -/
theorem two_attempts_without_write :
    let events := FreeAddMonoid.toList (Core.Observation.observe rawParameters 50
      (Core.Machine.start Suspensions.empty rawCapture program)).2
    events.count (.body 0) = 2 ∧ events.count (.cacheWrite 0) = 0 ∧ events.count (.hit 0) = 0 :=
  Examples.SuspensionPureCacheCounts.Exceptions.two_attempts_without_write

/-- Purity and finite normal return still hold. The actual repeated entries
contradict the body-count consequence if no-unwind is added, identifying the
extra premise that this source execution cannot satisfy. -/
theorem no_unwind_fails :
    ¬ Core.Machine.NoMemoizeUnwind rawParameters
      (Core.Machine.start Suspensions.empty rawCapture program) 0 := by
  intro safe
  obtain ⟨answer, run, _⟩ := execution
  have captured : EnvRep (fun _ => none) rawCapture capture := .cons (.exception .none) .nil
  have captureAllowed : EnvAllowed Operations capture := .cons (.exception .none) .nil
  have bound := source_bodyEntry_count_le_one compatible preserve WorldAllowed.empty
    (Memory.StateRep.empty pureParameters) captured captureAllowed allowed run 0 safe 50
  have counted : (FreeAddMonoid.toList (Core.Observation.observe rawParameters 50
      (Core.Machine.start Suspensions.empty rawCapture program)).2).count (.body 0) = 2 :=
    two_attempts_without_write.1
  rw [counted] at bound
  omega

end ExternalHandler

end Examples.SuspensionPureBodyCounts
