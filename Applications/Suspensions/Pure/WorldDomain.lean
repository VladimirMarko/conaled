import Applications.Suspensions.Pure.Creation
import Applications.Suspensions.Pure.DomainState

/-!
# Hereditary admissibility of immutable suspension meanings

World admissibility is a code-domain property, separate from raw memory
validity and immutable-world extension. In particular, `put` preserves this
property even when overwriting a world entry; freshness is still required by
the separate extension law.

Actual recursive creation supplies the pending template used below. Its
unrolled, represented members recover the allowed meaning of every new
effective address without a second template induction. New thunk bodies need
no evaluation witness. A cached cell already has a finite pure witness; runtime
domain preservation derives admissibility of that witness's returned value.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.WorldDomain
open Representation Domain

variable {Primitive : Type} {operations : Primitive → Prop}

def WorldAllowed (operations : Primitive → Prop) (world : World Primitive) : Prop :=
  ∀ address meaning, world address = some meaning → ValueAllowed operations meaning.value

theorem meaning_code {meaning : Meaning Primitive}
    (allowed : ValueAllowed operations meaning.value) : CodeAllowed operations meaning.body :=
  ((ValueAllowed.suspension_iff _ _ _).mp allowed).1

theorem meaning_environment {meaning : Meaning Primitive}
    (allowed : ValueAllowed operations meaning.value) : EnvAllowed operations meaning.environment := by
  have parts := (ValueAllowed.suspension_iff _ _ _).mp allowed
  exact bodyEnvironment_allowed parts.2.1 parts.2.2

theorem WorldAllowed.empty : WorldAllowed operations (fun _ => none) := by
  intro _ _ impossible
  cases impossible

/-- This is code preservation only. It deliberately has no freshness premise
and does not conclude immutable-world extension. -/
theorem WorldAllowed.put {world : World Primitive} (allowed : WorldAllowed operations world)
    (address : Nat) (meaning : Meaning Primitive) (newMeaning : ValueAllowed operations meaning.value) :
    WorldAllowed operations (Durability.put world address meaning) := by
  intro other entry found
  by_cases same : other = address
  · subst other
    have equal : meaning = entry := by simpa [Durability.put] using found
    subst entry
    exact newMeaning
  · exact allowed other entry (by simpa [Durability.put, same] using found)

private theorem address_meaning_eq {world : World Primitive} {address : Nat}
    {view : Value Primitive} {meaning : Meaning Primitive}
    (represented : ValueRep world (.address address) view)
    (found : world address = some meaning) : view = meaning.value := by
  cases represented with
  | address observed =>
      have same := Option.some.inj (observed.symm.trans found)
      cases same
      rfl

/-- Effective template lookup identifies each new meaning with an allowed
unrolled group member. Only old entries and the new target set are inspected. -/
theorem pending_allowed {beforeWorld afterWorld : World Primitive}
    {before preclose : Core.Machine.Memory Primitive} {rawOuter created : Core.Env Primitive}
    {group : Suspensions.Pure.Group Primitive}
    (pending : Creation.PendingGroup beforeWorld afterWorld before preclose rawOuter group created)
    (old : WorldAllowed operations beforeWorld) (groupAllowed : GroupAllowed operations group) :
    WorldAllowed operations afterWorld := by
  intro address meaning found
  rcases pending.entries address meaning found with previous | ⟨_, _, _, target⟩
  · exact old address meaning previous
  · obtain ⟨name, rawLookup⟩ := (Core.Machine.mem_addressRange _ address).mp target
    have represented := pending.members.unroll.lookup name
    rw [rawLookup] at represented
    cases pureLookup : Env.lookup group.members name with
    | none =>
        rw [pureLookup] at represented
        cases represented
    | some value =>
        rw [pureLookup] at represented
        cases represented with
        | some valueRep =>
            have allowed := groupAllowed.members.lookup pureLookup
            rw [address_meaning_eq valueRep found] at allowed
            exact allowed

/-- Keep the actual creation receipt and pending certificate available while
composing closed-state, closed-environment and code-domain preservation.
Distinct names come from the allowed descriptor, not an extra premise. -/
theorem create_closed_allowed {parameters : Machine.Parameters Primitive}
    {beforeWorld : World Primitive} {before : Core.Machine.Memory Primitive}
    {rawOuter : Core.Env Primitive} {pureOuter : Env Primitive}
    {definitions : List (Nat × Rhs Primitive)}
    (valid : Memory.StateRep parameters beforeWorld before)
    (allowed : WorldAllowed operations beforeWorld) (captured : EnvRep beforeWorld rawOuter pureOuter)
    (groupAllowed : GroupAllowed operations (.mk definitions pureOuter)) :
    ∃ (reached : Core.Machine.Memory Primitive) (collected : Core.Env Primitive) (world : World Primitive),
      Core.Recursive.create before rawOuter (Rhs.toBindings definitions) [] =
        .ok (reached, collected) ∧
      Creation.PendingGroup beforeWorld world before reached rawOuter
        (.mk definitions pureOuter) collected ∧
      Memory.StateRep parameters world (Core.Recursive.closeMemory reached collected) ∧
      WorldAllowed operations world ∧
      EnvRep world (Core.Recursive.closeEnvironment rawOuter collected)
        (bodyEnvironment pureOuter (some (.mk definitions pureOuter))) := by
  obtain ⟨⟨reached, collected⟩, made⟩ := Core.Recursive.create_exists before rawOuter
    (Rhs.toBindings definitions) [] (Rhs.toBindings_permitted definitions)
  obtain ⟨world, pending⟩ := Creation.create_pending valid.bounded valid.world_below
    captured groupAllowed.distinct made
  exact ⟨reached, collected, world, made, pending, pending.closed_state valid captured made,
    pending_allowed pending allowed groupAllowed, pending.closed_environment captured⟩

/-- Compose actual fresh delay allocation with the independent code-domain
property. Freshness and raw-cell validity come from the existing StateRep law. -/
theorem WorldAllowed.delay {parameters : Machine.Parameters Primitive} {world : World Primitive}
    {memory : Core.Machine.Memory Primitive} {rawCapture : Core.Env Primitive}
    {capture : Env Primitive} {body : Core.Expr Primitive}
    (allowed : WorldAllowed operations world) (valid : Memory.StateRep parameters world memory)
    (represented : EnvRep world rawCapture capture) (captured : EnvAllowed operations capture)
    (code : CodeAllowed operations body) :
    let meaning : Meaning Primitive := ⟨body, capture, none⟩
    let afterWorld := Durability.put world memory.next meaning
    Durability.Extends world afterWorld ∧
      Memory.StateRep parameters afterWorld (Suspensions.delay memory body rawCapture).1 ∧
      WorldAllowed operations afterWorld ∧
      ValueRep afterWorld (.address memory.next) meaning.value := by
  obtain ⟨extension, state, value⟩ := valid.delay represented body
  exact ⟨extension, state,
    allowed.put memory.next ⟨body, capture, none⟩ (.suspension code captured .none), value⟩

/-- Retain the cached constructor's exact view, count and pure evaluation.
The additional conclusion follows from runtime domain preservation. -/
theorem cached_result_allowed {parameters : Machine.Parameters Primitive} {world : World Primitive}
    {meaning : Meaning Primitive} {raw : Core.Value Primitive}
    (preserve : ParametersPreserve operations parameters)
    (allowed : ValueAllowed operations meaning.value)
    (cached : Memory.CellRep parameters world meaning (.value raw)) :
    ∃ view steps, ValueRep world raw view ∧
      Progress.Evaluates (Machine.step parameters)
        (Machine.start meaning.environment meaning.body) (.value view) steps ∧
      ValueAllowed operations view := by
  cases cached with
  | cached represented evaluation =>
      have initial := DomainState.start_allowed (meaning_environment allowed) (meaning_code allowed)
      have result := DomainState.evaluates_preserves preserve initial evaluation
      exact ⟨_, _, represented, evaluation, result⟩

theorem cached_lookup_allowed {parameters : Machine.Parameters Primitive} {world : World Primitive}
    {memory : Core.Machine.Memory Primitive} {address : Nat} {meaning : Meaning Primitive}
    {raw : Core.Value Primitive} (preserve : ParametersPreserve operations parameters)
    (allowed : WorldAllowed operations world) (valid : Memory.StateRep parameters world memory)
    (found : world address = some meaning) (cached : memory.memory address = some (.value raw)) :
    ∃ view steps, ValueRep world raw view ∧
      Progress.Evaluates (Machine.step parameters)
        (Machine.start meaning.environment meaning.body) (.value view) steps ∧
      ValueAllowed operations view :=
  cached_result_allowed preserve (allowed address meaning found) (valid.lookup found cached)

end Suspensions.Pure.WorldDomain
