import Applications.Interaction.Obligation
import Applications.Interaction.Snapshot

/-! Connected cases for the finite-event interface experiment. All effects
here are mathematical transitions, not executions against a filesystem. -/
namespace Examples.InteractionInterfaces
open Interaction
namespace O
open Obligation

def accepted : State Nat := ⟨some 7, some 7, 0, 0, false⟩
def leased : State Nat := ⟨some 7, some 7, 1, 0, false⟩
def unknown : State Nat := ⟨some 7, some 7, 1, 1, false⟩

theorem ready_empty : Ready (empty : State Nat) := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem acceptance_admitted : ∃ t, tryAccept 7 empty = some t ∧ Accepted 7 t :=
  admission_complete 7 ready_empty

theorem receipt_forgery : ¬ Accepted 7 (⟨some 8, some 7, 0, 0, false⟩ : State Nat) := by
  simp [Accepted]

theorem attempted_forgery : ¬ Accepted 7 (⟨some 7, some 7, 1, 0, false⟩ : State Nat) := by
  simp [Accepted]

theorem collision_rejected : tryAccept 8 accepted = none := rfl

theorem initial_script_runs : Events.interpret handler [.accept 7, .lease] empty leased :=
  ⟨accepted, rfl, leased, rfl, rfl⟩

/-- Same independent contract as the direct relation, through interpreter lifting. -/
theorem initial_script_contract : Leased 7 leased :=
  event_contract 7 ready_empty initial_script_runs

theorem lost_reply_run :
    Events.interpret handler [.accept 7, .lease, .effect, .observation false] empty unknown := by
  change Events.interpret handler
    ([.accept 7, .lease] ++ [.effect, .observation false]) empty unknown
  rw [Events.interpret_append]
  exact ⟨leased, initial_script_runs, execute leased, rfl, unknown, rfl, rfl⟩

/-- Generic primitive simulation transfers this concrete history to the
independent event contracts, including the retained unknown effect. -/
theorem lost_reply_meaning :
    Events.interpret meaning [.accept 7, .lease, .effect, .observation false] empty unknown := by
  obtain ⟨t, ht, eq⟩ := Events.interpret_simulation handler meaning Eq
    (fun e s t a h step => by subst a; exact ⟨t, handler_sound e s t step, rfl⟩)
    [.accept 7, .lease, .effect, .observation false] rfl lost_reply_run
  subst t
  exact ht

theorem lost_reply_retains_effect : unknown.effects = 1 ∧ unknown.settled = false ∧
    (observe true unknown).settled = true := ⟨rfl, rfl, rfl⟩

theorem lost_reply_identity : Bound 7 unknown :=
  script_bound 7 [.effect, .observation false]
    (show Bound 7 leased from ⟨rfl, rfl⟩)
    ⟨execute leased, rfl, unknown, rfl, rfl⟩

theorem retry_after_lost_reply :
    (execute (lease unknown)).effects = 2 ∧ (execute (lease unknown)).attempts = 2 :=
  ⟨rfl, rfl⟩

theorem delayed_old_attempt :
    (execute (lease (execute leased))).effects = 2 ∧
    (execute (lease (execute leased))).attempts = 2 :=
  delayed_attempt leased

/-- Negative design result: event syntax does not enforce authority ordering.
The unrestricted handler can execute without a receipt, intent or lease. -/
theorem script_is_not_authority :
    Events.interpret handler [.effect] (empty : State Nat) (execute empty) ∧
    (execute (empty : State Nat)).intent = none ∧
    (execute (empty : State Nat)).attempts = 0 ∧
    (execute (empty : State Nat)).effects = 1 :=
  ⟨⟨execute empty, rfl, rfl⟩, rfl, rfl, rfl⟩
end O

namespace Captured
open Snapshot

inductive Event where
  | capture
  | compile

def meaning {I : Type} (inputs : I) : Event → State I → State I → Prop
  | .capture => Seal inputs
  | .compile => CompileCaptured

def handler {I : Type} (inputs : I) : Event → State I → State I → Prop
  | .capture, s, t => t = ⟨s.live, inputs, none⟩
  | .compile, s, t => t = ⟨s.live, s.captured, some s.captured⟩

theorem handler_sound {I : Type} (inputs : I) (e : Event) (s t : State I)
    (h : handler inputs e s t) : meaning inputs e s t := by
  cases e with
  | capture => subst t; exact ⟨rfl, rfl, rfl⟩
  | compile => subst t; exact ⟨rfl, rfl⟩

/-- A second domain consumes the same interpretation theorem and its existing
independent compilation contract; no receipt/lease fields are imposed on it. -/
theorem event_contract {I : Type} (inputs : I) :
    Safe (fun _ => True) (Events.interpret (handler inputs) [.capture, .compile])
      (fun t => t.compiled = some inputs) := by
  refine Events.interpret_safe (handler_sound inputs) ?_
  rintro s t _ ⟨a, sealed, b, compile, eq⟩
  subst b
  exact compile_sealed inputs trivial
    ⟨a, sealed, a, Relation.ReflTransGen.refl, compile⟩

theorem mixed_compiled :
    (⟨(true, true), mixed, some mixed⟩ : State (Bool × Bool)).compiled = some mixed := by
  apply event_contract mixed (s := ⟨(true, true), (false, false), none⟩) trivial
  exact ⟨⟨(true, true), mixed, none⟩, rfl,
    ⟨(true, true), mixed, some mixed⟩, rfl, rfl⟩
end Captured
end Examples.InteractionInterfaces
