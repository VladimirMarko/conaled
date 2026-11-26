import Applications.Suspensions.Pure.Execution

/-!
# Recover a cache certificate from a completed source program

The source program returns its delayed value after forcing it once. Its raw
and pure runs each take fifteen transitions. The finite-correspondence theorem
constructs the final represented memory; inversion of its returned address
recovers the original empty capture and immutable suspension meaning.

A later force uses that recovered state and the stored body certificate.
Its raw cache hit completes in three transitions, while the pure replay takes
five. The matching caller contains the returned binding, but the body capture
remains empty. The complete raw cached memory is retained by the later run.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureCachedProgram
open Suspensions Suspensions.Pure
open Suspensions.Pure.Representation Suspensions.Pure.Memory
open Suspensions.Pure.History Suspensions.Pure.Recurrence
open Suspensions.Pure.Domain Suspensions.Pure.DomainState Suspensions.Pure.WorldDomain
open Suspensions.Pure.Compatibility Suspensions.Pure.Simulation

def rawParameters : Core.Machine.Parameters Empty where
  primitive := fun impossible _ => nomatch impossible
  matchException := 20
  bindException := 21

def parameters : Machine.Parameters Empty where
  primitive := fun impossible _ => nomatch impossible
  matchException := 20
  bindException := 21

def Operations : Empty → Prop := fun _ => False

private theorem compatible : ParametersCompatible Operations rawParameters parameters where
  primitive impossible := nomatch impossible
  matchException := rfl
  bindException := rfl

private theorem preserve : ParametersPreserve Operations parameters := by
  intro impossible
  cases impossible

def literal : Core.Expr Empty := .atom (.integer 7)
def program : Core.Expr Empty :=
  .bind (.variable 0) (.delay literal)
    (.bind (.suspended .wildcard) (.variable 0) (.variable 0))

def allocated : Core.Machine.Memory Empty := (Suspensions.delay Suspensions.empty literal []).1
def finalMemory : Core.Machine.Memory Empty := Suspensions.memoize allocated 0 (.atom (.integer 7))
def sourceAnswer : Core.Machine.Answer Empty := ⟨finalMemory, .value (.address 0)⟩
def meaning : Meaning Empty := ⟨literal, [], none⟩
def returnedSuspension : Value Empty := .suspension literal [] none

theorem program_allowed : CodeAllowed Operations program := by
  apply (CodeAllowed.bind_iff _ _ _).mpr
  refine ⟨.variable 0, (CodeAllowed.delay_iff _).mpr (CodeAllowed.atom (.integer 7)), ?_⟩
  apply (CodeAllowed.bind_iff _ _ _).mpr
  exact ⟨.suspended .wildcard, CodeAllowed.variable 0, CodeAllowed.variable 0⟩

theorem raw_source_execution : Progress.Evaluates (Core.Machine.step rawParameters)
    (Core.Machine.start Suspensions.empty [] program) sourceAnswer 15 :=
  Progress.search_sound (fuel := 15) rfl

theorem pure_source_execution : Progress.Evaluates (Machine.step parameters)
    (Machine.start [] program) (.value returnedSuspension) 15 :=
  Progress.search_sound (fuel := 15) rfl

private theorem address_lookup {world : World Empty} {address : Nat} {value : Value Empty}
    (represented : ValueRep world (.address address) value) :
    ∃ entry, world address = some entry ∧ value = entry.value := by
  cases represented with
  | address found => exact ⟨_, found, rfl⟩

/-- The final world and cached-state representation are recovered from the
actual source execution. The returned address identifies its exact original
meaning, including the capture made before binding variable0. -/
theorem source_recovers_cached_suspension :
    ∃ world,
      Durability.Extends (fun _ => none) world ∧ WorldAllowed Operations world ∧
      StateRep parameters world finalMemory ∧ world 0 = some meaning ∧
      ResultRep world sourceAnswer.result (.value returnedSuspension) ∧
      Progress.Evaluates (Core.Machine.step rawParameters)
        (Core.Machine.start Suspensions.empty [] program) sourceAnswer 15 ∧
      Progress.Evaluates (Machine.step parameters)
        (Machine.start [] program) (.value returnedSuspension) 15 := by
  obtain ⟨world, result, steps, extension, allowed, state, resultRep, evaluation⟩ :=
    finite_correspondence compatible preserve WorldAllowed.empty
      (ConfigRep.start (StateRep.empty parameters) EnvRep.nil program)
      (start_allowed EnvAllowed.nil program_allowed) raw_source_execution
  obtain ⟨resultEqual, countEqual⟩ := evaluation.unique pure_source_execution
  subst result
  subst steps
  have valueRep : ValueRep world (.address 0) returnedSuspension := by
    cases resultRep with
    | value represented => exact represented
  obtain ⟨entry, found, sameValue⟩ := address_lookup valueRep
  have entryEqual : entry = meaning := by
    rcases entry with ⟨body, captured, recursive⟩
    change Value.suspension literal [] none = .suspension body captured recursive at sameValue
    obtain ⟨rfl, rfl, rfl⟩ := Value.suspension.inj sameValue
    rfl
  subst entry
  exact ⟨world, extension, allowed, state, found, resultRep, raw_source_execution, evaluation⟩

def rawCaller : Core.Env Empty := [(0, .address 0)]
def caller : Env Empty := [(0, returnedSuspension)]
def laterRaw : Core.Machine.Config Empty :=
  Core.Machine.startPattern finalMemory rawCaller (.suspended .wildcard) (.address 0)
def laterPure : Machine.Config Empty :=
  Machine.startPattern caller (.suspended .wildcard) returnedSuspension

private theorem expected_body : Progress.Evaluates (Machine.step parameters)
    (Machine.start meaning.environment meaning.body) (.value (.atom (.integer 7))) 2 :=
  .next rfl (.done rfl)

/-- The successful source program supplies the later cache-hit witness.
The raw run retains exactly finalMemory; the pure run replays the inferred
two-transition body certificate before the common matching continuation. -/
theorem recovered_cache_replays_certified_body :
    ∃ world,
      StateRep parameters world finalMemory ∧ world 0 = some meaning ∧
      Progress.Evaluates (Machine.step parameters)
        (Machine.start meaning.environment meaning.body) (.value (.atom (.integer 7))) 2 ∧
      Core.Machine.transition rawParameters laterRaw =
        (.inr ⟨finalMemory, .pattern rawCaller .wildcard (.atom (.integer 7)), []⟩, .hit 0) ∧
      Reaches parameters 3 laterPure ⟨.pattern caller .wildcard (.atom (.integer 7)), []⟩ ∧
      ConfigRep parameters world
        ⟨finalMemory, .pattern rawCaller .wildcard (.atom (.integer 7)), []⟩
        ⟨.pattern caller .wildcard (.atom (.integer 7)), []⟩ ∧
      Progress.Evaluates (Core.Machine.step rawParameters) laterRaw ⟨finalMemory, .matched []⟩ 3 ∧
      Progress.Evaluates (Machine.step parameters) laterPure (.matched []) 5 ∧
      finalMemory.memory 0 = some (.value (.atom (.integer 7))) ∧ finalMemory.next = 1 := by
  obtain ⟨world, _extension, _allowed, state, found, _result, _rawRun, _pureRun⟩ :=
    source_recovers_cached_suspension
  have captured : EnvRep world rawCaller caller := .cons (.address found) .nil
  obtain ⟨value, steps, bodyRun, rawHit, replayed, related⟩ :=
    reuse_cached rawParameters (address := 0) (meaning := meaning) (inner := .wildcard)
      (rawValue := .atom (.integer 7)) (rawStack := []) (pureStack := [])
      state found rfl captured .nil (ActiveHistories.empty _ _ _ _)
  have same := expected_body.unique bodyRun
  have valueEqual : value = .atom (.integer 7) := (Machine.Result.value.inj same.1).symm
  subst value
  have stepsEqual : steps = 2 := same.2.symm
  subst steps
  have rawTail : Progress.Evaluates (Core.Machine.step rawParameters)
      ⟨finalMemory, .pattern rawCaller .wildcard (.atom (.integer 7)), []⟩
      ⟨finalMemory, .matched []⟩ 2 := .next rfl (.done rfl)
  have pureTail : Progress.Evaluates (Machine.step parameters)
      ⟨.pattern caller .wildcard (.atom (.integer 7)), []⟩ (.matched []) 2 :=
    .next rfl (.done rfl)
  exact ⟨world, state, found, bodyRun, rawHit, replayed, related,
    .next (congrArg Prod.fst rawHit) rawTail, replayed.evaluates pureTail, rfl, rfl⟩

end Examples.SuspensionPureCachedProgram
