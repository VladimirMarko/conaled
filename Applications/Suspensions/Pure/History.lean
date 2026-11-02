import Applications.Suspensions.Pure.Recurrence
import Applications.Suspensions.Pure.Representation
import Applications.Suspensions.Machine

/-!
# Executed pure prefixes for individual pending forces

Each raw memoize-frame occurrence has its own past execution prefix. Repeated
addresses are permitted: the invariant records what has happened, without
assuming that the pending bodies terminate or that active forces are distinct.

A normal body return closes such a prefix into an actual evaluation. Reentering
an already pending address instead produces a positive recurrence at its same
immutable meaning. That recurrence excludes every finite pure continuation.
The raw-to-pure transition correspondence remains a separate obligation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.History
open Representation Recurrence

variable {Primitive : Type}

def BodyHistory (parameters : Machine.Parameters Primitive) (world : World Primitive)
    (address : Nat) (control : Machine.Control Primitive) (inside : List (Machine.Frame Primitive)) : Prop :=
  ∃ meaning steps, world address = some meaning ∧
    Reaches parameters steps (Machine.start meaning.environment meaning.body) ⟨control, inside⟩

/-- The index identifies an occurrence, not an address. The pure stack before
that occurrence is precisely the part still executing inside its body. -/
def ActiveHistories (parameters : Machine.Parameters Primitive) (world : World Primitive)
    (rawStack : List (Core.Machine.Frame Primitive)) (control : Machine.Control Primitive)
    (pureStack : List (Machine.Frame Primitive)) : Prop :=
  ∀ index address environment inner,
    rawStack[index]? = some (.memoize address environment inner) →
      BodyHistory parameters world address control (pureStack.take index)

variable {parameters : Machine.Parameters Primitive} {world : World Primitive}

theorem BodyHistory.mono {before after : World Primitive} {address : Nat}
    {control : Machine.Control Primitive} {inside : List (Machine.Frame Primitive)}
    (extension : Durability.Extends before after)
    (history : BodyHistory parameters before address control inside) :
    BodyHistory parameters after address control inside := by
  obtain ⟨meaning, steps, found, executed⟩ := history
  exact ⟨meaning, steps, extension _ _ found, executed⟩

theorem BodyHistory.advance {address : Nat} {first last : Machine.Control Primitive}
    {before after : List (Machine.Frame Primitive)} {steps : Nat}
    (history : BodyHistory parameters world address first before)
    (executed : Reaches parameters steps ⟨first, before⟩ ⟨last, after⟩) :
    BodyHistory parameters world address last after := by
  obtain ⟨meaning, earlier, found, past⟩ := history
  exact ⟨meaning, earlier + steps, found, past.trans executed⟩

/-- The only new step is the actual isolated value delivery. This builds the
finite cache certificate from an already executed prefix. -/
theorem BodyHistory.completed {address : Nat} {meaning : Meaning Primitive} {value : Value Primitive}
    (history : BodyHistory parameters world address (.value value) [])
    (found : world address = some meaning) :
    ∃ steps, Progress.Evaluates (Machine.step parameters)
      (Machine.start meaning.environment meaning.body) (.value value) (steps + 1) := by
  obtain ⟨original, steps, known, executed⟩ := history
  have same := Option.some.inj (known.symm.trans found)
  subst original
  exact ⟨steps, executed.evaluates (.done rfl)⟩

theorem ActiveHistories.empty (parameters : Machine.Parameters Primitive) (world : World Primitive)
    (control : Machine.Control Primitive) (pureStack : List (Machine.Frame Primitive)) :
    ActiveHistories parameters world [] control pureStack := by
  intro index address environment inner found
  simp at found

theorem ActiveHistories.mono {before after : World Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {control : Machine.Control Primitive}
    {pureStack : List (Machine.Frame Primitive)}
    (extension : Durability.Extends before after)
    (histories : ActiveHistories parameters before rawStack control pureStack) :
    ActiveHistories parameters after rawStack control pureStack :=
  fun index address environment inner found =>
    (histories index address environment inner found).mono extension

/-- A local pure block that leaves the caller tail intact advances every
pending occurrence, including duplicate addresses. -/
theorem ActiveHistories.keep {rawStack : List (Core.Machine.Frame Primitive)}
    {first last : Machine.Control Primitive} {pureStack : List (Machine.Frame Primitive)}
    {steps : Nat} (histories : ActiveHistories parameters world rawStack first pureStack)
    (block : ∀ tail, Reaches parameters steps ⟨first, tail⟩ ⟨last, tail⟩) :
    ActiveHistories parameters world rawStack last pureStack :=
  fun index address environment inner found =>
    (histories index address environment inner found).advance (block _)

/-- New ordinary frames have a vacuous head obligation. A new memoize frame
supplies its own body-start prefix; old occurrences advance independently. -/
theorem ActiveHistories.push {rawStack : List (Core.Machine.Frame Primitive)}
    {rawFrame : Core.Machine.Frame Primitive} {pureFrame : Machine.Frame Primitive}
    {first last : Machine.Control Primitive} {pureStack : List (Machine.Frame Primitive)}
    {steps : Nat} (histories : ActiveHistories parameters world rawStack first pureStack)
    (head : ∀ address environment inner, rawFrame = .memoize address environment inner →
      BodyHistory parameters world address last [])
    (block : ∀ tail, Reaches parameters steps ⟨first, tail⟩ ⟨last, pureFrame :: tail⟩) :
    ActiveHistories parameters world (rawFrame :: rawStack) last (pureFrame :: pureStack) := by
  intro index address environment inner found
  cases index with
  | zero =>
      change some rawFrame = some (.memoize address environment inner) at found
      exact head address environment inner (Option.some.inj found)
  | succ index =>
      change rawStack[index]? = some (.memoize address environment inner) at found
      exact (histories index address environment inner found).advance (block _)

theorem ActiveHistories.pop {rawStack : List (Core.Machine.Frame Primitive)}
    {rawFrame : Core.Machine.Frame Primitive} {pureFrame : Machine.Frame Primitive}
    {first last : Machine.Control Primitive} {pureStack : List (Machine.Frame Primitive)}
    {steps : Nat}
    (histories : ActiveHistories parameters world (rawFrame :: rawStack) first (pureFrame :: pureStack))
    (block : ∀ tail, Reaches parameters steps ⟨first, pureFrame :: tail⟩ ⟨last, tail⟩) :
    ActiveHistories parameters world rawStack last pureStack := by
  intro index address environment inner found
  have past := histories (index + 1) address environment inner found
  exact past.advance (block _)

theorem ActiveHistories.replace {rawStack : List (Core.Machine.Frame Primitive)}
    {oldRaw newRaw : Core.Machine.Frame Primitive} {oldPure newPure : Machine.Frame Primitive}
    {first last : Machine.Control Primitive} {pureStack : List (Machine.Frame Primitive)}
    {steps : Nat}
    (histories : ActiveHistories parameters world (oldRaw :: rawStack) first (oldPure :: pureStack))
    (head : ∀ address environment inner, newRaw = .memoize address environment inner →
      BodyHistory parameters world address last [])
    (block : ∀ tail, Reaches parameters steps ⟨first, oldPure :: tail⟩ ⟨last, newPure :: tail⟩) :
    ActiveHistories parameters world (newRaw :: rawStack) last (newPure :: pureStack) := by
  intro index address environment inner found
  cases index with
  | zero =>
      change some newRaw = some (.memoize address environment inner) at found
      exact head address environment inner (Option.some.inj found)
  | succ index =>
      change rawStack[index]? = some (.memoize address environment inner) at found
      have past := histories (index + 1) address environment inner found
      exact past.advance (block _)

/-- Taking the next actual pure body-entry step makes the old prefix strictly
positive. Equality of the world entry identifies the complete body input. -/
theorem BodyHistory.reentry_not_terminates {address : Nat} {meaning : Meaning Primitive}
    {environment : Env Primitive} {inner : Core.Pattern} {inside : List (Machine.Frame Primitive)}
    (history : BodyHistory parameters world address
      (.pattern environment (.suspended inner) meaning.value) inside)
    (found : world address = some meaning) :
    ¬Progress.Terminates (Machine.step parameters)
      (Machine.start meaning.environment meaning.body) := by
  obtain ⟨original, steps, known, past⟩ := history
  have same := Option.some.inj (known.symm.trans found)
  subst original
  have entry : Reaches parameters 1
      ⟨.pattern environment (.suspended inner) meaning.value, inside⟩
      (Machine.appendFrames (Machine.start meaning.environment meaning.body)
        (.force environment inner :: inside)) := Reaches.one rfl
  exact recurring_prefix_not_terminates (by omega) (past.trans entry)

theorem ActiveHistories.reentry_not_terminates
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    {address index : Nat} {rawEnvironment : Core.Env Primitive} {rawInner : Core.Pattern}
    {meaning : Meaning Primitive} {environment : Env Primitive} {inner : Core.Pattern}
    (histories : ActiveHistories parameters world rawStack
      (.pattern environment (.suspended inner) meaning.value) pureStack)
    (active : rawStack[index]? = some (.memoize address rawEnvironment rawInner))
    (found : world address = some meaning) :
    ¬Progress.Terminates (Machine.step parameters)
      (Machine.start meaning.environment meaning.body) :=
  (histories index address rawEnvironment rawInner active).reentry_not_terminates found

end Suspensions.Pure.History
