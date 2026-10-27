import SquareKit.InteractionContracts
import Applications.Optimization.Relations

/-!
# Publication, missing acknowledgements and interrupted recovery

A bounded benchmark/evidence model. `effects` counts append-like external
operations, `published` records visible evidence, and `acknowledged` records
knowledge retained by the supervisor. Publication is not claimed durable.
The transitions are a model, not contracts established for an OS adapter.
-/
namespace Interaction.Evidence

structure State where
  effects : Nat
  published : Bool
  acknowledged : Bool
  deriving DecidableEq, Repr

/-- Acknowledged evidence must have been published. -/
def Consistent (s : State) : Prop := s.acknowledged = true → s.published = true

def initial : State := ⟨0, false, false⟩
def effect (s : State) : State := { s with effects := s.effects + 1 }
def publish (s : State) : State := { s with published := true }
def loseAcknowledgement (s : State) : State := { s with acknowledged := false }

/-- A reply carries the observed effect count; silence does not decide it. -/
def observe (s : State) : Option Nat :=
  if s.acknowledged then some s.effects else none

/-- Recovery may lose its acknowledgement again, or successfully observe
published evidence. It does not repeat the external effect. -/
def Recover (s t : State) : Prop :=
  t = loseAcknowledgement s ∨
    (s.published = true ∧ t = { s with acknowledged := true })

theorem recover_consistent : Stable Recover Consistent := by
  intro s t hs h
  rcases h with rfl | ⟨hp, rfl⟩
  · simp [Consistent, loseAcknowledgement]
  · simpa [Consistent] using hp

theorem recover_published : Stable Recover (fun s => s.published = true) := by
  intro s t hs h
  rcases h with rfl | ⟨_, rfl⟩ <;> exact hs

theorem recover_effects (n : Nat) : Stable Recover (fun s => s.effects = n) := by
  intro s t hs h
  rcases h with rfl | ⟨_, rfl⟩ <;> exact hs

/-- Explicit observation succeeds only if the evidence is available. -/
def Acknowledge (s t : State) : Prop :=
  s.published = true ∧ t = { s with acknowledged := true }

theorem publication_then_recovery_then_ack :
    Safe (fun _ => True)
      (Relation.Comp (fun s t => t = publish s)
        (Relation.Comp (Relation.ReflTransGen Recover) Acknowledge))
      (fun t => t.acknowledged = true) := by
  refine safe_interference_seq (S := State)
    (P := fun _ => True) (Q := fun s => s.published = true)
    (U := fun t => t.acknowledged = true)
    (C := fun s t => t = publish s) (R := Recover) (D := Acknowledge) ?_ ?_ ?_
  · intro s t _ h
    subst t
    rfl
  · exact recover_published
  · rintro s t _ ⟨_, rfl⟩
    rfl

/-- The child has taken effect and published, but retained observation is absent. -/
def unknownEffect : State := loseAcknowledgement (publish (effect initial))

/-- A bounded attempt may stop before starting, or take effect and lose its reply.
Other process behaviors belong to richer models, not this two-outcome example. -/
def Attempt (s t : State) : Prop :=
  t = s ∨ t = loseAcknowledgement (publish (effect s))

theorem ambiguous_worlds_admissible : Attempt initial initial ∧ Attempt initial unknownEffect :=
  ⟨Or.inl rfl, Or.inr rfl⟩

theorem unknown_observation : observe unknownEffect = observe initial := rfl

theorem unknown_effect_differs : unknownEffect.effects ≠ initial.effects := by decide

/-- No decision from this observation alone classifies whether an effect occurred
on both admissible worlds. -/
theorem no_effect_decision :
    ¬ ∃ decideEffect : Option Nat → Bool,
      decideEffect (observe initial) = false ∧
      decideEffect (observe unknownEffect) = true := by
  rintro ⟨d, h0, h1⟩
  rw [unknown_observation, h0] at h1
  cases h1

theorem retry_duplicates : (effect unknownEffect).effects = 2 ∧
    (effect unknownEffect).effects ≠ unknownEffect.effects := by decide

/-- Recovery interrupted at every attempt is an infinite permitted run. -/
def interrupted : Nat → State := fun _ => unknownEffect

theorem interrupted_run : Run Recover interrupted := by
  intro n
  exact Or.inl rfl

theorem interrupted_consistent : ∀ n, Consistent (interrupted n) :=
  interrupted_run.invariant (by simp [interrupted, unknownEffect, Consistent,
    loseAcknowledgement]) recover_consistent

theorem interrupted_no_ack : ¬ ∃ n, (interrupted n).acknowledged = true := by
  simp [interrupted, unknownEffect, loseAcknowledgement]

theorem interrupted_no_reexecution : ∀ n, (interrupted n).effects = 1 :=
  interrupted_run.invariant (P := fun s => s.effects = 1) rfl (recover_effects 1)

/-- A concrete successful recovery also exists; the model does not force failure. -/
theorem recovery_can_finish : Recover unknownEffect ⟨1, true, true⟩ :=
  Or.inr ⟨rfl, rfl⟩

/-- Source and target worlds can have matching effect counts while differing
on whether evidence was published. This deliberately coarse relation loses it. -/
def countObservation (s t : State) : Prop := s.effects = t.effects

def recorded : State := ⟨1, true, true⟩
def unrecorded : State := ⟨1, false, false⟩

theorem coarse_refinement :
    Refines countObservation {recorded} {unrecorded} := by
  intro t ht
  have ht : t = unrecorded := ht
  subst t
  exact ⟨recorded, rfl, rfl⟩

theorem coarse_preserves_count : ∀ t ∈ ({unrecorded} : Set State), t.effects = 1 := by
  refine coarse_refinement.property (P := fun s => s.effects = 1)
    (Q := fun t => t.effects = 1) ?_ ?_
  · intro s hs
    have hs : s = recorded := hs
    subst s
    rfl
  · intro s t h hp
    exact h.symm.trans hp

theorem coarse_loses_publication :
    (∀ s ∈ ({recorded} : Set State), s.published = true) ∧
    ¬ (∀ t ∈ ({unrecorded} : Set State), t.published = true) := by
  constructor
  · intro s hs
    have hs : s = recorded := hs
    subst s
    rfl
  · intro h
    have impossible := h unrecorded rfl
    cases impossible

/-- Reuse the repository's observation square for set-valued knowledge.
This forgets world detail without choosing a representative world. -/
def observationSquare := Optimization.observationSquare (I := Unit) observe

theorem ambiguous_observation_allowed :
    (observationSquare.impl ((), unknownEffect)).2 ∈
      (observationSquare.spec ((), ({initial, unknownEffect} : Set State))).2 := by
  have h := observationSquare.preserves
    (r := ((), unknownEffect)) (s := ((), ({initial, unknownEffect} : Set State)))
    (show (Optimization.membershipRep (I := Unit) (id : State → State)).Rel
      ((), unknownEffect) ((), ({initial, unknownEffect} : Set State)) from
      ⟨rfl, by simp⟩)
  exact h.2
end Interaction.Evidence
