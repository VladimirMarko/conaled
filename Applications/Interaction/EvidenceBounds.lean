import Applications.Interaction.Evidence
import SquareKit.PreservationBounds

/-! Finite recovery prefixes preserve effect counts across a tuple encoding.
Probe scheduling and capped retries remain separate (#196); no physical
durability or eventual acknowledgment is inferred from these safety results. -/
namespace Interaction.Evidence

abbrev Encoded := Nat × (Bool × Bool)
def encode (s : State) : Encoded := (s.effects,(s.published,s.acknowledged))
def decode (t : Encoded) : State := ⟨t.1,t.2.1,t.2.2⟩
def Encoding (s : State) (t : Encoded) : Prop := encode s = t
def reachable : Set State := {s | Relation.ReflTransGen Recover unknownEffect s}
def encodedReachable : Set Encoded := encode '' reachable

theorem encoding_coverage : Refines Encoding reachable encodedReachable := by
  rintro t ⟨s,hs,rfl⟩
  exact ⟨s,hs,rfl⟩

theorem reachable_effects (s : State) (hs : s ∈ reachable) : s.effects = 1 :=
  (recover_effects 1).closure rfl hs

/-- The shared ordered transport theorem preserves an external-effect bound.
The FRP client uses the same theorem for retained cells, a different observation. -/
theorem encoded_effects_bound : ∀ t ∈ encodedReachable, t.1 ≤ 1 :=
  encoding_coverage.bound State.effects Prod.fst id (fun _ _ h => h)
    (fun _ _ h => by cases h; exact Nat.le_refl _)
    1 (fun s hs => (reachable_effects s hs).le)

theorem uniform_prefix_effects (states : Nat → State)
    (start : states 0 = unknownEffect) (steps : Run Recover states) :
    ∀ n, (encode (states n)).1 ≤ 1 := by
  intro n
  apply encoded_effects_bound
  refine ⟨states n,?_,rfl⟩
  change Relation.ReflTransGen Recover unknownEffect (states n)
  induction n with
  | zero => rw [start]
  | succ n ih => exact ih.tail (steps n)

/-- Recovery and acknowledgment compose at an actually reached intermediate
state. This constructs an endpoint and does not require a scheduler to choose it. -/
theorem recovery_then_ack_exists : ∃ t,
    Relation.Comp (Relation.ReflTransGen Recover) Acknowledge unknownEffect t ∧
      t.acknowledged = true ∧ t.effects = 1 := by
  refine ⟨recorded,⟨unknownEffect,.refl,?_,rfl⟩,rfl,rfl⟩
  rfl

/-- Quantitative and publication safety survive finite interruption, but the
existing infinite interruption execution has no acknowledgment. -/
theorem safe_without_progress :
    (∀ n, (encode (interrupted n)).1 ≤ 1) ∧
      ¬ ∃ n, (interrupted n).acknowledged = true :=
  ⟨uniform_prefix_effects interrupted rfl interrupted_run,interrupted_no_ack⟩

end Interaction.Evidence
