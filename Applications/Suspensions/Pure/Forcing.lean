import Applications.Suspensions.Pure.Simulation

/-!
# Actual force and cache steps with past-execution certificates

Uncached entry starts a new body history while advancing every older active
occurrence. Cache hits replay an already justified pure body. Normal return
derives its cache witness from the completed past prefix before proving the
actual write; exceptional return performs no write. None of these local laws
assumes that active addresses are distinct or that every thunk terminates.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Simulation
open Representation Memory History Recurrence

variable {Primitive : Type} {parameters : Machine.Parameters Primitive}
  {world : World Primitive} {memory : Core.Machine.Memory Primitive}
  {rawCaller : Core.Env Primitive} {caller : Env Primitive}
  {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
  {address : Nat} {meaning : Meaning Primitive} {inner : Core.Pattern}

/-- Delay performs one actual allocation and adds the corresponding immutable
meaning. The body is stored, without a body-evaluation premise or transition. -/
theorem delay_entry (rawParameters : Core.Machine.Parameters Primitive)
    (body : Core.Expr Primitive) (state : StateRep parameters world memory)
    (captured : EnvRep world rawCaller caller) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack (.eval caller (.delay body)) pureStack) :
    let meaning : Meaning Primitive := ⟨body, caller, none⟩
    let afterWorld := Durability.put world memory.next meaning
    let afterMemory := (Suspensions.delay memory body rawCaller).1
    Durability.Extends world afterWorld ∧
    Core.Machine.transition rawParameters ⟨memory, .eval rawCaller (.delay body), rawStack⟩ =
      (.inr ⟨afterMemory, .value (.address memory.next), rawStack⟩, .allocate memory.next) ∧
    Reaches parameters 1 ⟨.eval caller (.delay body), pureStack⟩
      ⟨.value meaning.value, pureStack⟩ ∧
    ConfigRep parameters afterWorld ⟨afterMemory, .value (.address memory.next), rawStack⟩
      ⟨.value meaning.value, pureStack⟩ := by
  have allocated := state.delay captured body
  exact ⟨allocated.1, rfl, Reaches.one rfl, allocated.2.1, .value allocated.2.2,
    frames.mono allocated.1,
    (histories.mono allocated.1).keep (fun _ => Reaches.one rfl)⟩

/-- This is the original unrestricted body-entry transition, including when
the same address is already present among the pending memoize frames. -/
theorem enter_thunk (rawParameters : Core.Machine.Parameters Primitive)
    {rawCapture : Core.Env Primitive}
    (state : StateRep parameters world memory) (found : world address = some meaning)
    (occupied : memory.memory address = some (.thunk meaning.body rawCapture))
    (captured : EnvRep world rawCaller caller) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack
      (.pattern caller (.suspended inner) meaning.value) pureStack) :
    Core.Machine.transition rawParameters
        ⟨memory, .pattern rawCaller (.suspended inner) (.address address), rawStack⟩ =
      (.inr ⟨memory, .eval rawCapture meaning.body, .memoize address rawCaller inner :: rawStack⟩,
        .body address) ∧
    Reaches parameters 1 ⟨.pattern caller (.suspended inner) meaning.value, pureStack⟩
      ⟨.eval meaning.environment meaning.body, .force caller inner :: pureStack⟩ ∧
    ConfigRep parameters world
      ⟨memory, .eval rawCapture meaning.body, .memoize address rawCaller inner :: rawStack⟩
      ⟨.eval meaning.environment meaning.body, .force caller inner :: pureStack⟩ := by
  have cell := state.lookup found occupied
  cases cell with
  | thunk bodyCapture =>
      refine ⟨?_, Reaches.one rfl, state, .eval _ bodyCapture,
        .cons (.memoize inner found captured) frames, ?_⟩
      · simp [Core.Machine.transition, Core.Machine.proceed, occupied]
      · apply histories.push (steps := 1)
        · intro actual environment pattern same
          cases same
          exact ⟨meaning, 0, found, rfl⟩
        · intro tail
          exact Reaches.one rfl

/-- A cache hit performs one raw transition. The pure expansion takes n+1
steps, using the previously stored body witness without assuming the inner
pattern succeeds. Earlier active histories advance by that whole expansion. -/
theorem reuse_cached (rawParameters : Core.Machine.Parameters Primitive)
    {rawValue : Core.Value Primitive}
    (state : StateRep parameters world memory) (found : world address = some meaning)
    (occupied : memory.memory address = some (.value rawValue))
    (captured : EnvRep world rawCaller caller) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack
      (.pattern caller (.suspended inner) meaning.value) pureStack) :
    ∃ value steps,
      Progress.Evaluates (Machine.step parameters)
        (Machine.start meaning.environment meaning.body) (.value value) steps ∧
      Core.Machine.transition rawParameters
          ⟨memory, .pattern rawCaller (.suspended inner) (.address address), rawStack⟩ =
        (.inr ⟨memory, .pattern rawCaller inner rawValue, rawStack⟩, .hit address) ∧
      Reaches parameters (steps + 1) ⟨.pattern caller (.suspended inner) meaning.value, pureStack⟩
        ⟨.pattern caller inner value, pureStack⟩ ∧
      ConfigRep parameters world ⟨memory, .pattern rawCaller inner rawValue, rawStack⟩
        ⟨.pattern caller inner value, pureStack⟩ := by
  have cell := state.lookup found occupied
  cases cell with
  | cached represented evaluation =>
      refine ⟨_, _, evaluation, ?_, force_prefix_of_certificate evaluation _ _ _, state,
        .pattern inner captured represented, frames, ?_⟩
      · simp [Core.Machine.transition, Core.Machine.proceed, occupied]
      · exact histories.keep (fun tail => force_prefix_of_certificate evaluation _ _ tail)

/-- The top history supplies the finite pure-body certificate before the
actual cache write is justified. No current-thunk or first-write premise is
required, so successful overwrite is not ruled out by the invariant itself. -/
theorem return_memoize (rawParameters : Core.Machine.Parameters Primitive)
    {rawValue : Core.Value Primitive} {value : Value Primitive}
    (state : StateRep parameters world memory) (found : world address = some meaning)
    (captured : EnvRep world rawCaller caller) (represented : ValueRep world rawValue value)
    (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world (.memoize address rawCaller inner :: rawStack)
      (.value value) (.force caller inner :: pureStack)) :
    Core.Machine.transition rawParameters
        ⟨memory, .value rawValue, .memoize address rawCaller inner :: rawStack⟩ =
      (.inr ⟨Suspensions.memoize memory address rawValue,
        .pattern rawCaller inner rawValue, rawStack⟩, .cacheWrite address) ∧
    Reaches parameters 1 ⟨.value value, .force caller inner :: pureStack⟩
      ⟨.pattern caller inner value, pureStack⟩ ∧
    ConfigRep parameters world
      ⟨Suspensions.memoize memory address rawValue, .pattern rawCaller inner rawValue, rawStack⟩
      ⟨.pattern caller inner value, pureStack⟩ := by
  have past := histories 0 address rawCaller inner rfl
  obtain ⟨steps, evaluation⟩ := past.completed found
  exact ⟨rfl, Reaches.one rfl, state.memoize found represented evaluation,
    .pattern inner captured represented, frames,
    histories.pop (fun _ => Reaches.one rfl)⟩

/-- Exceptional exit discards the pending memoize frame without its own cache
write. Other effects already represented in the reached memory are retained. -/
theorem raise_memoize (rawParameters : Core.Machine.Parameters Primitive)
    {rawPacket : Core.Value Primitive} {packet : Value Primitive}
    (state : StateRep parameters world memory) (represented : ValueRep world rawPacket packet)
    (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world (.memoize address rawCaller inner :: rawStack)
      (.raised packet) (.force caller inner :: pureStack)) :
    Core.Machine.transition rawParameters
        ⟨memory, .raised rawPacket, .memoize address rawCaller inner :: rawStack⟩ =
      (.inr ⟨memory, .raised rawPacket, rawStack⟩, .core) ∧
    Reaches parameters 1 ⟨.raised packet, .force caller inner :: pureStack⟩
      ⟨.raised packet, pureStack⟩ ∧
    ConfigRep parameters world ⟨memory, .raised rawPacket, rawStack⟩ ⟨.raised packet, pureStack⟩ :=
  ⟨rfl, Reaches.one rfl, state, .raised represented, frames,
    histories.pop (fun _ => Reaches.one rfl)⟩

end Suspensions.Pure.Simulation
