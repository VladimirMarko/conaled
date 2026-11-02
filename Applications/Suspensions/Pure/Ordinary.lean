import Applications.Suspensions.Pure.Simulation
import Applications.Suspensions.Pure.Compatibility
import Applications.Suspensions.Pure.DomainState

/-!
# Ordinary transitions preserve the pure interpretation

An ordinary source transition takes one actual step in each existing machine.
It retains the raw memory and immutable world. Pending force histories advance
through the same step, including when their addresses are repeated.

Allocation, recursive creation, suspended address lookup and memoize return
belong to their separate correspondence laws. Wrong operands and invalid
continuations remain actual terminal faults. This relation does not assert
output code-domain preservation or a complete finite-run simulation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Simulation
open Representation Memory History Recurrence Compatibility Domain DomainState

variable {Primitive : Type}

inductive OrdinaryStepRep (parameters : Machine.Parameters Primitive) (world : World Primitive)
    (initialMemory : Core.Machine.Memory Primitive) :
    Core.Machine.Answer Primitive ⊕ Core.Machine.Config Primitive →
      Machine.Result Primitive ⊕ Machine.Config Primitive → Prop
  | next {raw : Core.Machine.Config Primitive} {view : Machine.Config Primitive}
      (memory : raw.memory = initialMemory) (represented : ConfigRep parameters world raw view) :
      OrdinaryStepRep parameters world initialMemory (.inr raw) (.inr view)
  | done {raw : Core.Machine.Answer Primitive} {view : Machine.Result Primitive}
      (memory : raw.memory = initialMemory) (represented : ResultRep world raw.result view) :
      OrdinaryStepRep parameters world initialMemory (.inl raw) (.inl view)

/-- The stable-state cases with separate heap/creation proofs. Wrong operands
remain ordinary; this predicate is not a type or well-formedness judgment. -/
def IsOrdinary (config : Core.Machine.Config Primitive) : Prop :=
  match config.control, config.stack with
  | .eval _ (.delay _), _ | .eval _ (.recursive _ _), _ => False
  | .pattern _ (.suspended _) (.address _), _ => False
  | .value _, .memoize _ _ _ :: _ | .raised _, .memoize _ _ _ :: _ => False
  | _, _ => True

private abbrev StepAt (rawParameters : Core.Machine.Parameters Primitive)
    (parameters : Machine.Parameters Primitive) (world : World Primitive)
    (memory : Core.Machine.Memory Primitive) (rawControl : Core.Machine.Control Primitive)
    (control : Machine.Control Primitive) (rawStack : List (Core.Machine.Frame Primitive))
    (pureStack : List (Machine.Frame Primitive)) : Prop :=
  OrdinaryStepRep parameters world memory
    (Core.Machine.step rawParameters ⟨memory, rawControl, rawStack⟩)
    (Machine.step parameters ⟨control, pureStack⟩)

variable {parameters : Machine.Parameters Primitive} {world : World Primitive}
  {memory : Core.Machine.Memory Primitive}

private theorem keep_step {first last : Machine.Control Primitive}
    {rawLast : Core.Machine.Control Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (state : StateRep parameters world memory) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack first pureStack)
    (represented : ControlRep world rawLast last)
    (moved : ∀ tail, Machine.step parameters ⟨first, tail⟩ = .inr ⟨last, tail⟩) :
    OrdinaryStepRep parameters world memory
      (.inr ⟨memory, rawLast, rawStack⟩) (.inr ⟨last, pureStack⟩) :=
  .next rfl ⟨state, represented, frames, histories.keep (fun tail => Reaches.one (moved tail))⟩

private theorem push_step {first last : Machine.Control Primitive}
    {rawLast : Core.Machine.Control Primitive}
    {rawFrame : Core.Machine.Frame Primitive} {pureFrame : Machine.Frame Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (state : StateRep parameters world memory) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack first pureStack)
    (represented : ControlRep world rawLast last) (frame : FrameRep world rawFrame pureFrame)
    (ordinary : ∀ address environment inner, rawFrame ≠ .memoize address environment inner)
    (moved : ∀ tail, Machine.step parameters ⟨first, tail⟩ = .inr ⟨last, pureFrame :: tail⟩) :
    OrdinaryStepRep parameters world memory
      (.inr ⟨memory, rawLast, rawFrame :: rawStack⟩) (.inr ⟨last, pureFrame :: pureStack⟩) :=
  .next rfl ⟨state, represented, .cons frame frames,
    histories.push (fun address environment inner same =>
      False.elim (ordinary address environment inner same)) (fun tail => Reaches.one (moved tail))⟩

private theorem pop_step {first last : Machine.Control Primitive}
    {rawLast : Core.Machine.Control Primitive}
    {rawFrame : Core.Machine.Frame Primitive} {pureFrame : Machine.Frame Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (state : StateRep parameters world memory) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world (rawFrame :: rawStack) first (pureFrame :: pureStack))
    (represented : ControlRep world rawLast last)
    (moved : ∀ tail, Machine.step parameters ⟨first, pureFrame :: tail⟩ = .inr ⟨last, tail⟩) :
    OrdinaryStepRep parameters world memory
      (.inr ⟨memory, rawLast, rawStack⟩) (.inr ⟨last, pureStack⟩) :=
  .next rfl ⟨state, represented, frames, histories.pop (fun tail => Reaches.one (moved tail))⟩

private theorem replace_step {first last : Machine.Control Primitive}
    {rawLast : Core.Machine.Control Primitive}
    {oldRaw newRaw : Core.Machine.Frame Primitive} {oldPure newPure : Machine.Frame Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (state : StateRep parameters world memory) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world (oldRaw :: rawStack) first (oldPure :: pureStack))
    (represented : ControlRep world rawLast last) (frame : FrameRep world newRaw newPure)
    (ordinary : ∀ address environment inner, newRaw ≠ .memoize address environment inner)
    (moved : ∀ tail, Machine.step parameters ⟨first, oldPure :: tail⟩ = .inr ⟨last, newPure :: tail⟩) :
    OrdinaryStepRep parameters world memory
      (.inr ⟨memory, rawLast, newRaw :: rawStack⟩) (.inr ⟨last, newPure :: pureStack⟩) :=
  .next rfl ⟨state, represented, .cons frame frames,
    histories.replace (fun address environment inner same =>
      False.elim (ordinary address environment inner same)) (fun tail => Reaches.one (moved tail))⟩

private theorem finish_step {raw : Core.Machine.Result Primitive} {view : Machine.Result Primitive}
    (represented : ResultRep world raw view) :
    OrdinaryStepRep parameters world memory (.inl ⟨memory, raw⟩) (.inl view) := .done rfl represented

end Suspensions.Pure.Simulation
