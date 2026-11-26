import Applications.Suspensions.Pure.Execution
import Examples.SuspensionPureDomainState

/-!
# An actually cached closure retains its suspension back reference

The existing returningClosure source first caches a function capturing s, then
applies that function at false. Its back reference hits the completed cache and
the returned function is applied at true. Recursive creation exposes the
immutable meaning; finite correspondence of the remaining source run supplies
the actual final cache certificate.

A later application of that cached closure again follows its back reference.
The actual raw hit and certified pure replay are composed under the concrete
caller continuation. The full raw memory remains unchanged.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureCachedClosure
open Suspensions Suspensions.Pure
open Suspensions.Pure.Representation Suspensions.Pure.Memory
open Suspensions.Pure.History Suspensions.Pure.Recurrence
open Suspensions.Pure.Domain Suspensions.Pure.DomainState Suspensions.Pure.WorldDomain
open Suspensions.Pure.Compatibility Suspensions.Pure.Simulation
open Examples.SuspensionPureMachine

def rawParameters : Core.Machine.Parameters Empty where
  primitive := fun impossible _ => nomatch impossible
  matchException := 0
  bindException := 1

def Operations : Empty → Prop := fun _ => False

private theorem compatible : ParametersCompatible Operations rawParameters parameters where
  primitive impossible := nomatch impossible
  matchException := rfl
  bindException := rfl

private theorem preserve : ParametersPreserve Operations parameters := by
  intro impossible
  cases impossible

def suspendedBody : Core.Expr Empty := .function returningClauses
def selfMeaning : Meaning Empty := ⟨suspendedBody, [], some returningGroup⟩
def rawSelf : Core.Env Empty := [(1, .address 0)]
def pureSelf : Env Empty := bodyEnvironment [] (some returningGroup)
def rawCached : Core.Value Empty := .closure returningClauses rawSelf []
def pureCached : Value Empty := .closure returningClauses pureSelf none
def sourceBody : Core.Expr Empty := .apply (Core.force (.variable 1)) (boolean false)
def allocated : Core.Machine.Memory Empty := (Suspensions.delay Suspensions.empty suspendedBody []).1
def closed : Core.Machine.Memory Empty := Core.Recursive.closeMemory allocated rawSelf
def finalMemory : Core.Machine.Memory Empty := Suspensions.memoize closed 0 rawCached
def sourceAnswer : Core.Machine.Answer Empty := ⟨finalMemory, .value (.atom (.integer 7))⟩
def rawAfterCreation : Core.Machine.Config Empty := Core.Machine.start closed rawSelf sourceBody
def pureAfterCreation : Machine.Config Empty := Machine.start pureSelf sourceBody

theorem raw_source_trace :
    ∃ events,
      Progress.Evaluates (Core.Machine.tracedStep rawParameters)
        (Core.Machine.start Suspensions.empty [] returningClosure, []) (sourceAnswer, events) 53 ∧
      events.count (.allocate 0) = 1 ∧ events.count (.body 0) = 1 ∧
      events.count (.cacheWrite 0) = 1 ∧ events.count (.hit 0) = 1 := by
  refine ⟨_, Progress.search_sound (step := Core.Machine.tracedStep rawParameters)
    (fuel := 53) (by rfl), ?_, ?_, ?_, ?_⟩ <;> rfl

theorem raw_source_execution : Progress.Evaluates (Core.Machine.step rawParameters)
    (Core.Machine.start Suspensions.empty [] returningClosure) sourceAnswer 53 := by
  obtain ⟨events, run, _⟩ := raw_source_trace
  exact Core.Machine.traced_evaluates_erases run

theorem pure_source_execution : Progress.Evaluates (Machine.step parameters)
    (Machine.start [] returningClosure) (.value (.atom (.integer 7))) 51 := by
  obtain ⟨events, run, _⟩ := recursive_closure_forcing_after_return
  exact Machine.traced_evaluates_erases run

theorem raw_creation_prefix : Core.Prefix.observe rawParameters 5
    (Core.Machine.start Suspensions.empty [] returningClosure) = .inr rawAfterCreation := rfl

theorem pure_creation_prefix : Reaches parameters 1
    (Machine.start [] returningClosure) pureAfterCreation := rfl

private theorem address_lookup {world : World Empty} {address : Nat} {value : Value Empty}
    (represented : ValueRep world (.address address) value) :
    ∃ entry, world address = some entry ∧ value = entry.value := by
  cases represented with
  | address found => exact ⟨_, found, rfl⟩

private theorem meaning_injective {first second : Meaning Empty}
    (same : first.value = second.value) : first = second := by
  rcases first with ⟨body, captured, recursive⟩
  rcases second with ⟨body', captured', recursive'⟩
  obtain ⟨rfl, rfl, rfl⟩ := Value.suspension.inj same
  rfl

/-- The actual creation prefix, rather than an assumed semantic map, supplies
the self-address meaning needed by the remainder of the source run. -/
theorem creation_recovers_self_meaning :
    ∃ world,
      Durability.Extends (fun _ => none) world ∧ WorldAllowed Operations world ∧
      ConfigRep parameters world rawAfterCreation pureAfterCreation ∧ world 0 = some selfMeaning := by
  obtain ⟨world, rawNext, pureNext, extension, allowed, rawPrefix, purePrefix, represented, _events⟩ :=
    recursive_entry rawParameters (StateRep.empty parameters) WorldAllowed.empty EnvRep.nil
      EnvAllowed.nil Examples.SuspensionPureDomainState.Returned.program_code
      (.nil) (ActiveHistories.empty _ _ _ _)
  have rawSame : rawNext = rawAfterCreation := Sum.inr.inj (rawPrefix.symm.trans raw_creation_prefix)
  have pureSame : pureNext = pureAfterCreation := Sum.inr.inj (purePrefix.symm.trans pure_creation_prefix)
  subst rawNext
  subst pureNext
  have captured : EnvRep world rawSelf pureSelf := by
    cases represented.control with
    | eval expression captured => exact captured
  have lookup := captured.lookup 1
  change OptionalRep world (some (.address 0)) (some selfMeaning.value) at lookup
  have valueRep : ValueRep world (.address 0) selfMeaning.value := by
    cases lookup with
    | some value => exact value
  obtain ⟨entry, found, same⟩ := address_lookup valueRep
  have sameEntry : entry = selfMeaning := (meaning_injective same).symm
  subst entry
  exact ⟨world, extension, allowed, represented, found⟩

private theorem raw_body_execution : Progress.Evaluates (Core.Machine.step rawParameters)
    rawAfterCreation sourceAnswer 48 := by
  obtain ⟨steps, run, count⟩ := Core.Recursive.evaluates_strip_prefix raw_creation_prefix raw_source_execution
  have same : steps = 48 := by omega
  subst steps
  exact run

private theorem pure_body_execution : Progress.Evaluates (Machine.step parameters)
    pureAfterCreation (.value (.atom (.integer 7))) 50 := by
  obtain ⟨steps, run, count⟩ := pure_creation_prefix.remaining pure_source_execution
  have same : steps = 50 := by omega
  subst steps
  exact run

private theorem expected_cached_body : Progress.Evaluates (Machine.step parameters)
    (Machine.start selfMeaning.environment selfMeaning.body) (.value pureCached) 2 :=
  .next rfl (.done rfl)

/-- The cache containing the self-referential closure is justified by the
actual completed source run. Its capture relation is recovered from that
cached value's representation, not separately postulated. -/
theorem source_recovers_cached_recursive_closure :
    ∃ world,
      Durability.Extends (fun _ => none) world ∧ WorldAllowed Operations world ∧
      StateRep parameters world finalMemory ∧ world 0 = some selfMeaning ∧
      ValueRep world rawCached pureCached ∧ EnvRep world rawSelf pureSelf ∧
      Core.Env.lookup rawSelf 1 = some (.address 0) ∧
      Env.lookup pureSelf 1 = some selfMeaning.value ∧
      Progress.Evaluates (Machine.step parameters)
        (Machine.start selfMeaning.environment selfMeaning.body) (.value pureCached) 2 ∧
      Progress.Evaluates (Core.Machine.step rawParameters)
        (Core.Machine.start Suspensions.empty [] returningClosure) sourceAnswer 53 ∧
      Progress.Evaluates (Machine.step parameters)
        (Machine.start [] returningClosure) (.value (.atom (.integer 7))) 51 := by
  obtain ⟨initialWorld, extension, worldAllowed, represented, initialFound⟩ := creation_recovers_self_meaning
  have initialCode := start_allowed (EnvAllowed.nil (operations := Operations))
    Examples.SuspensionPureDomainState.Returned.program_code
  have bodyCode := reaches_preserves preserve initialCode pure_creation_prefix
  obtain ⟨world, result, steps, finalExtension, allowed, state, _resultRep, pureRun⟩ :=
    finite_correspondence compatible preserve worldAllowed represented bodyCode raw_body_execution
  obtain ⟨resultEqual, countEqual⟩ := pureRun.unique pure_body_execution
  subst result
  subst steps
  have found := finalExtension 0 selfMeaning initialFound
  obtain ⟨value, count, cachedRep, bodyRun, _valueAllowed⟩ :=
    cached_lookup_allowed preserve allowed state found
      (show finalMemory.memory 0 = some (.value rawCached) from rfl)
  have same := expected_cached_body.unique bodyRun
  have valueEqual : value = pureCached := (Machine.Result.value.inj same.1).symm
  subst value
  have countEqual : count = 2 := same.2.symm
  subst count
  have captureRep : EnvRep world rawSelf pureSelf := by
    cases cachedRep with
    | closure captured => exact captured
  exact ⟨world, extension.trans finalExtension, allowed, state, found, cachedRep, captureRep,
    rfl, rfl, bodyRun, raw_source_execution, pure_creation_prefix.evaluates pureRun⟩

def laterExpression : Core.Expr Empty := .apply (.variable 3) (boolean false)
def laterRaw : Core.Machine.Config Empty := Core.Machine.start finalMemory [(3, rawCached)] laterExpression
def laterPure : Machine.Config Empty := Machine.start [(3, pureCached)] laterExpression
def rawFalse : Core.Env Empty := Core.Env.extend rawSelf [(2, .atom (.boolean false))]
def pureFalse : Env Empty := Env.extend pureSelf [(2, .atom (.boolean false))]
def rawHitStack : List (Core.Machine.Frame Empty) :=
  [.clause rawFalse (.variable 0) [] (.address 0), .applicationResult,
    .function rawFalse (boolean true), .applicationResult]
def pureHitStack : List (Machine.Frame Empty) :=
  [.clause pureFalse (.variable 0) [] selfMeaning.value, .applicationResult,
    .function pureFalse (boolean true), .applicationResult]
def rawBeforeHit : Core.Machine.Config Empty :=
  ⟨finalMemory, .pattern rawFalse (.suspended (.variable 0)) (.address 0), rawHitStack⟩
def pureBeforeHit : Machine.Config Empty :=
  ⟨.pattern pureFalse (.suspended (.variable 0)) selfMeaning.value, pureHitStack⟩
def rawAfterHit : Core.Machine.Config Empty :=
  ⟨finalMemory, .pattern rawFalse (.variable 0) rawCached, rawHitStack⟩
def pureAfterHit : Machine.Config Empty :=
  ⟨.pattern pureFalse (.variable 0) pureCached, pureHitStack⟩

theorem later_raw_reaches_back_reference :
    Core.Prefix.observe rawParameters 18 laterRaw = .inr rawBeforeHit := rfl

theorem later_pure_reaches_back_reference : Reaches parameters 18 laterPure pureBeforeHit := rfl

private theorem no_pending_at_hit (world : World Empty) : ActiveHistories parameters world
    rawHitStack pureBeforeHit.control pureHitStack := by
  intro index address environment inner found
  have member := List.mem_of_getElem? found
  simp [rawHitStack] at member

private theorem raw_matching_tail : Progress.Evaluates (Core.Machine.step rawParameters)
    rawAfterHit sourceAnswer 17 := Progress.search_sound (fuel := 17) rfl

private theorem pure_matching_tail : Progress.Evaluates (Machine.step parameters)
    pureAfterHit (.value (.atom (.integer 7))) 17 := Progress.search_sound (fuel := 17) rfl

/-- Applying the actually recovered cached closure to false follows its
captured self-address, hits that same completed cell, and applies the returned
closure to true. Pure replay takes two more transitions, with the exact same
17-transition matching/application suffix. -/
theorem cached_closure_back_reference_hits :
    ∃ world,
      StateRep parameters world finalMemory ∧ world 0 = some selfMeaning ∧
      ValueRep world rawCached pureCached ∧ EnvRep world rawSelf pureSelf ∧
      Core.Prefix.observe rawParameters 18 laterRaw = .inr rawBeforeHit ∧
      Core.Machine.transition rawParameters rawBeforeHit = (.inr rawAfterHit, .hit 0) ∧
      Reaches parameters 3 pureBeforeHit pureAfterHit ∧
      ConfigRep parameters world rawAfterHit pureAfterHit ∧
      Progress.Evaluates (Core.Machine.step rawParameters) laterRaw sourceAnswer 36 ∧
      Progress.Evaluates (Machine.step parameters) laterPure (.value (.atom (.integer 7))) 38 ∧
      finalMemory.memory 0 = some (.value rawCached) := by
  obtain ⟨world, _extension, _allowed, state, found, cachedRep, captureRep, _rawLookup,
      _pureLookup, _bodyRun, _rawRun, _pureRun⟩ := source_recovers_cached_recursive_closure
  have captured : EnvRep world rawFalse pureFalse :=
    captureRep.extend (.cons (.atom (.boolean false)) .nil)
  have frames : FramesRep world rawHitStack pureHitStack :=
    .cons (.clause _ _ captured (.address found))
      (.cons .applicationResult (.cons (.function _ captured) (.cons .applicationResult .nil)))
  obtain ⟨value, steps, bodyRun, rawHit, replayed, related⟩ :=
    reuse_cached rawParameters (address := 0) (meaning := selfMeaning) (inner := .variable 0)
      (rawValue := rawCached) state found rfl captured frames (no_pending_at_hit world)
  have same := expected_cached_body.unique bodyRun
  have valueEqual : value = pureCached := (Machine.Result.value.inj same.1).symm
  subst value
  have countEqual : steps = 2 := same.2.symm
  subst steps
  have rawRest : Progress.Evaluates (Core.Machine.step rawParameters) rawBeforeHit sourceAnswer 18 :=
    .next (congrArg Prod.fst rawHit) raw_matching_tail
  have rawWhole : Progress.Evaluates (Core.Machine.step rawParameters) laterRaw sourceAnswer 36 := by
    repeat' first | exact rawRest | refine Progress.Evaluates.next rfl ?_
  exact ⟨world, state, found, cachedRep, captureRep, later_raw_reaches_back_reference,
    rawHit, replayed, related, rawWhole,
    (later_pure_reaches_back_reference.trans replayed).evaluates pure_matching_tail, rfl⟩

end Examples.SuspensionPureCachedClosure
