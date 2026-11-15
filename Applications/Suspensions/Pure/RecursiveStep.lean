import Applications.Suspensions.Pure.WorldDomain
import Applications.Suspensions.Pure.Simulation

/-!
# Recursive creation inside a represented execution

The raw machine's finite creation/closing prefix corresponds to one pure
recursive-declaration step. The existing caller frames survive literally;
their individual past-body histories advance by that pure step under the
immutable world extension. No newly allocated body is evaluated, and no
suspension-body event occurs strictly inside the raw creation prefix.

This is a local execution law, not yet the correspondence for every finite
raw run. Primitive behavior is irrelevant to this prefix, so no primitive
compatibility or preservation law is required here.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Simulation
open Representation Memory History Recurrence Domain WorldDomain

variable {Primitive : Type} {operations : Primitive → Prop}
  {parameters : Machine.Parameters Primitive} {world : World Primitive}
  {memory : Core.Machine.Memory Primitive}
  {rawOuter : Core.Env Primitive} {outer : Env Primitive}
  {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}

/-- A complete admissible source declaration supplies its own permitted-RHS
and distinct-name evidence. The raw count includes creation and SRec closing;
the pure count records its single descriptor-construction step. -/
theorem recursive_entry (rawParameters : Core.Machine.Parameters Primitive)
    {bindings : List (Nat × Core.Expr Primitive)} {body : Core.Expr Primitive}
    (state : StateRep parameters world memory) (worldAllowed : WorldAllowed operations world)
    (captured : EnvRep world rawOuter outer) (outerAllowed : EnvAllowed operations outer)
    (code : CodeAllowed operations (.recursive bindings body))
    (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack
      (.eval outer (.recursive bindings body)) pureStack) :
    ∃ afterWorld rawAfter pureAfter,
      Durability.Extends world afterWorld ∧ WorldAllowed operations afterWorld ∧
      Core.Prefix.observe rawParameters (3 * bindings.length + 2)
        ⟨memory, .eval rawOuter (.recursive bindings body), rawStack⟩ = .inr rawAfter ∧
      Reaches parameters 1 ⟨.eval outer (.recursive bindings body), pureStack⟩ pureAfter ∧
      ConfigRep parameters afterWorld rawAfter pureAfter ∧
      (∀ index config, index < 3 * bindings.length + 2 →
        Core.Prefix.observe rawParameters index
          ⟨memory, .eval rawOuter (.recursive bindings body), rawStack⟩ = .inr config →
        ∀ address, (Core.Machine.transition rawParameters config).2 ≠ .body address) := by
  obtain ⟨definitionsCode, _, permitted, distinct⟩ :=
    (CodeAllowed.recursive_iff bindings body).mp code
  obtain ⟨definitions, decoded, source⟩ := decode_permitted permitted
  have groupAllowed := GroupAllowed.of_decoded definitionsCode distinct decoded outerAllowed
  obtain ⟨reached, created, afterWorld, made, pending, valid, allowed, environment⟩ :=
    create_closed_allowed state worldAllowed captured groupAllowed
  have entered : ∀ tail, Reaches parameters 1
      ⟨.eval outer (.recursive bindings body), tail⟩
      ⟨.eval (bodyEnvironment outer (some (.mk definitions outer))) body, tail⟩ := by
    intro tail
    apply Reaches.one
    rw [← source]
    exact congrArg Prod.fst (Machine.recursive_transition parameters outer definitions body tail)
  have receipt : Core.Recursive.create memory rawOuter bindings [] = .ok (reached, created) := by
    simpa only [source] using made
  refine ⟨afterWorld,
    ⟨Core.Recursive.closeMemory reached created,
      .eval (Core.Recursive.closeEnvironment rawOuter created) body, rawStack⟩,
    ⟨.eval (bodyEnvironment outer (some (.mk definitions outer))) body, pureStack⟩,
    pending.extension, allowed,
    Core.Recursive.enter_body_prefix_with_stack permitted receipt body rawStack,
    entered pureStack, ?_, ?_⟩
  · exact ⟨valid, .eval body environment, frames.mono pending.extension,
      (histories.mono pending.extension).keep entered⟩
  · intro index config inside observed address
    exact Core.Recursive.enter_body_prefix_no_body permitted receipt body rawStack
      inside observed address

end Suspensions.Pure.Simulation
