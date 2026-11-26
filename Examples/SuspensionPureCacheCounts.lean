import Applications.Suspensions.Pure.CacheCounts
import Applications.Suspensions.TraceObservation
import Examples.SuspensionPureCachedClosure
import Examples.SuspensionMachine

/-!
# Source programs connected to the finite pure write bound

Repeated forcing and the existing recursive closure use the general source
theorem at every observation budget and address. Two record fields allocate
identical delayed code under the same empty capture, yet write separate cells.
A handled fixed exception enters its body twice and never caches a value.
An unforced delayed literal has no write. The existing effectful reentrant
source still has two writes to one cell and lies outside the pure conclusion.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureCacheCounts
open Suspensions Suspensions.Pure
open Suspensions.Pure.Representation Suspensions.Pure.Domain
open Suspensions.Pure.DomainState Suspensions.Pure.WorldDomain
open Suspensions.Pure.Compatibility Suspensions.Pure.Simulation

private def rawParameters := Examples.SuspensionPureCachedClosure.rawParameters
private def pureParameters := Examples.SuspensionPureMachine.parameters
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
    (address budget : Nat) :
    Core.Observation.cacheWrites address
      (Core.Observation.observe rawParameters budget
        (Core.Machine.start Suspensions.empty [] program)).2 ≤ 1 :=
  source_cacheWrites_le_one compatible preserve WorldAllowed.empty
    (Memory.StateRep.empty pureParameters) EnvRep.nil EnvAllowed.nil code run address budget

private def literal : Core.Expr Empty := .atom (.integer 7)

namespace Repeated

def program : Core.Expr Empty :=
  .bind (.variable 0) (.delay literal)
    (.bind (.suspended .wildcard) (.variable 0)
      (.bind (.suspended .wildcard) (.variable 0) (.atom (.integer 9))))

private def allocated : Core.Machine.Memory Empty := (Suspensions.delay Suspensions.empty literal []).1
private def finalMemory := Suspensions.memoize allocated 0 (.atom (.integer 7))
private def answer : Core.Machine.Answer Empty := ⟨finalMemory, .value (.atom (.integer 9))⟩

private theorem allowed : CodeAllowed Operations program := by
  apply (CodeAllowed.bind_iff _ _ _).mpr
  refine ⟨.variable 0, (CodeAllowed.delay_iff _).mpr (CodeAllowed.atom (.integer 7)), ?_⟩
  apply (CodeAllowed.bind_iff _ _ _).mpr
  refine ⟨.suspended .wildcard, CodeAllowed.variable 0, ?_⟩
  apply (CodeAllowed.bind_iff _ _ _).mpr
  exact ⟨.suspended .wildcard, CodeAllowed.variable 0, CodeAllowed.atom (.integer 9)⟩

private theorem execution : Progress.Evaluates (Core.Machine.step rawParameters)
    (Core.Machine.start Suspensions.empty [] program) answer 21 :=
  Progress.search_sound (fuel := 21) rfl

/-- All prefixes and all absorbing suffix budgets inherit the proved source
bound; the exact completed trace below independently exhibits its one write. -/
theorem all_budgets (address budget : Nat) :
    (FreeAddMonoid.toList (Core.Observation.observe rawParameters budget
      (Core.Machine.start Suspensions.empty [] program)).2).count (.cacheWrite address) ≤ 1 :=
  source_cacheWrite_count_le_one compatible preserve WorldAllowed.empty
    (Memory.StateRep.empty pureParameters) EnvRep.nil EnvAllowed.nil allowed execution address budget

theorem one_write_then_hit :
    let events := FreeAddMonoid.toList (Core.Observation.observe rawParameters 21
      (Core.Machine.start Suspensions.empty [] program)).2
    events.count (.body 0) = 1 ∧ events.count (.cacheWrite 0) = 1 ∧ events.count (.hit 0) = 1 := by
  exact ⟨rfl, rfl, rfl⟩

end Repeated

/-- This is the existing 53-step raw recursive-closure source execution. Its
successful return justifies the all-budget theorem, rather than assuming a
nonreentry invariant or counting only a chosen test prefix. -/
theorem recursive_closure_all_budgets (address budget : Nat) :
    Core.Observation.cacheWrites address
      (Core.Observation.observe rawParameters budget
        (Core.Machine.start Suspensions.empty [] Examples.SuspensionPureMachine.returningClosure)).2 ≤ 1 :=
  empty_source_bound Examples.SuspensionPureDomainState.Returned.program_code
    Examples.SuspensionPureCachedClosure.raw_source_execution address budget

namespace Distinct

def fields : List (Nat × Core.Expr Empty) := [(0, .delay literal), (1, .delay literal)]
def pattern : Core.Pattern := .record [(0, .variable 1), (1, .variable 2)]
def program : Core.Expr Empty :=
  .bind pattern (.record fields)
    (.bind (.suspended .wildcard) (.variable 1)
      (.bind (.suspended .wildcard) (.variable 2) (.atom (.integer 9))))

private theorem allowed : CodeAllowed Operations program := by
  apply (CodeAllowed.bind_iff _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · unfold pattern
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

theorem all_budgets (address budget : Nat) :
    Core.Observation.cacheWrites address
      (Core.Observation.observe rawParameters budget
        (Core.Machine.start Suspensions.empty [] program)).2 ≤ 1 := by
  obtain ⟨answer, run, _, _⟩ := execution
  exact empty_source_bound allowed run address budget

/-- Both delays are evaluated as record fields under the same empty capture.
Equal body and capture do not merge their distinct allocation addresses. -/
theorem identical_thunks_at_distinct_addresses :
    ∃ config, Core.Prefix.observe rawParameters 6
      (Core.Machine.start Suspensions.empty [] program) = .inr config ∧
      config.memory.memory 0 = some (.thunk literal []) ∧
      config.memory.memory 1 = some (.thunk literal []) ∧ config.memory.next = 2 := by
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem two_separate_writes :
    let events := FreeAddMonoid.toList (Core.Observation.observe rawParameters 34
      (Core.Machine.start Suspensions.empty [] program)).2
    events.count (.allocate 0) = 1 ∧ events.count (.allocate 1) = 1 ∧
      events.count (.cacheWrite 0) = 1 ∧ events.count (.cacheWrite 1) = 1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Distinct

namespace Exceptions

private def rawCapture : Core.Env Empty := [(3, .exception 17 none)]
private def capture : Env Empty := [(3, .exception 17 none)]
private def body : Core.Expr Empty := .raise (.variable 3)
private def handler (result : Core.Expr Empty) : Core.Expr Empty :=
  .handle (Core.force (.variable 1)) [(.exception 3 none, result)]
def program : Core.Expr Empty :=
  .bind (.variable 1) (.delay body)
    (.bind .wildcard (handler (.record [])) (handler (.atom (.integer 5))))

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

/-- The fixed exception value is admitted and represented explicitly; the
example performs no generative exception-name or reference operation. -/
theorem all_budgets (address budget : Nat) :
    Core.Observation.cacheWrites address
      (Core.Observation.observe rawParameters budget
        (Core.Machine.start Suspensions.empty rawCapture program)).2 ≤ 1 := by
  obtain ⟨answer, run, _⟩ := execution
  have captured : EnvRep (fun _ => none) rawCapture capture := .cons (.exception .none) .nil
  have captureAllowed : EnvAllowed Operations capture := .cons (.exception .none) .nil
  exact source_cacheWrites_le_one compatible preserve WorldAllowed.empty
    (Memory.StateRep.empty pureParameters) captured captureAllowed allowed run address budget

/-- Both handled attempts enter the same thunk. Neither successful-write
event occurs, so at-most-one write does not mean at-most-one body attempt. -/
theorem two_attempts_without_write :
    let events := FreeAddMonoid.toList (Core.Observation.observe rawParameters 50
      (Core.Machine.start Suspensions.empty rawCapture program)).2
    events.count (.body 0) = 2 ∧ events.count (.cacheWrite 0) = 0 ∧ events.count (.hit 0) = 0 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Actual zero-write completion and the structural observer laws retain
zero writes at every earlier or later budget, for every address. -/
theorem no_writes_all_budgets (address budget : Nat) :
    Core.Observation.cacheWrites address
      (Core.Observation.observe rawParameters budget
        (Core.Machine.start Suspensions.empty rawCapture program)).2 = 0 := by
  obtain ⟨answer, finished⟩ : ∃ answer, Core.Prefix.observe rawParameters 50
      (Core.Machine.start Suspensions.empty rawCapture program) = .inl answer := ⟨_, rfl⟩
  exact Core.Observation.cacheWrites_observe_zero_of_finished finished (by rfl) budget

end Exceptions

theorem unforced_delay :
    (∀ address budget, Core.Observation.cacheWrites address
      (Core.Observation.observe rawParameters budget
        (Core.Machine.start Suspensions.empty [] (.delay literal))).2 ≤ 1) ∧
    (∀ address budget, Core.Observation.cacheWrites address
      (Core.Observation.observe rawParameters budget
        (Core.Machine.start Suspensions.empty [] (.delay literal))).2 = 0) := by
  constructor
  · intro address budget
    apply empty_source_bound ((CodeAllowed.delay_iff _).mpr (CodeAllowed.atom (.integer 7)))
    exact Progress.search_sound (fuel := 2) rfl
  · intro address budget
    have finished : Core.Prefix.observe rawParameters 2
        (Core.Machine.start Suspensions.empty [] (.delay literal)) =
        .inl ⟨(Suspensions.delay Suspensions.empty literal []).1, .value (.address 0)⟩ := rfl
    exact Core.Observation.cacheWrites_observe_zero_of_finished finished (by rfl) budget

/-- The unchanged unrestricted machine still permits two cache writes to
address1 in the existing effectful source program. -/
theorem unrestricted_two_writes :
    Core.Observation.cacheWrites 1
      (Core.Observation.observe Examples.SuspensionMachine.parameters 300
        (Core.Machine.start Examples.SuspensionMachine.initial []
          Examples.SuspensionMachine.reentrantOverwrite)).2 = 2 := by
  let initialConfig := Core.Machine.start Examples.SuspensionMachine.initial []
    Examples.SuspensionMachine.reentrantOverwrite
  obtain ⟨answer, events, steps, run, _, _, _, _, writes, _⟩ :=
    Examples.SuspensionMachine.reentrant_overwrite
  obtain ⟨finished, recorded⟩ := Core.Observation.traced_evaluates_observe_nil run
  have completed : Core.Prefix.observe Examples.SuspensionMachine.parameters steps initialConfig =
      .inl answer :=
    (Core.Observation.observe_erases Examples.SuspensionMachine.parameters steps initialConfig).symm.trans
      finished
  obtain ⟨boundedAnswer, boundedCompletion⟩ : ∃ answer,
      Core.Prefix.observe Examples.SuspensionMachine.parameters 76 initialConfig =
        .inl answer := ⟨_, rfl⟩
  obtain ⟨boundedSteps, bound, evaluated⟩ :=
    (Core.Prefix.finished_iff Examples.SuspensionMachine.parameters 76 initialConfig boundedAnswer).mp
      boundedCompletion
  have sameSteps : steps = boundedSteps :=
    ((Core.Machine.traced_evaluates_erases run).unique evaluated).2
  have within : steps ≤ 300 := by omega
  obtain ⟨extra, fullBudget⟩ := Nat.exists_eq_add_of_le within
  change Core.Observation.cacheWrites 1
    (Core.Observation.observe Examples.SuspensionMachine.parameters 300 initialConfig).2 = 2
  rw [fullBudget, Core.Observation.cacheWrites_observe_after_finished completed extra 1,
    Core.Observation.cacheWrites_eq_count, recorded]
  exact writes

end Examples.SuspensionPureCacheCounts
