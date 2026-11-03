import Applications.Interaction.Evidence
import Applications.Interaction.Snapshot

/-! Checked specializations of the #194 observation contracts. These are
mathematical examples, not execution tests of filesystem or process adapters. -/
namespace Examples.ExternalInteraction
open Interaction

/-- A successful nonempty pipeline witnesses that the partial-correctness rule
is usable, while the interrupted run below witnesses that it gives no progress. -/
theorem published_attempt_acknowledged : Evidence.recorded.acknowledged = true := by
  apply Evidence.publication_then_recovery_then_ack (s := Evidence.effect Evidence.initial)
    trivial
  refine ⟨Evidence.unknownEffect, rfl, Evidence.recorded, ?_, ?_⟩
  · exact Relation.ReflTransGen.single Evidence.recovery_can_finish
  · exact ⟨rfl, rfl⟩

/-- The same recovery permits success and infinite interruption; both preserve
its safety invariant. -/
theorem recovery_safety_without_progress :
    Evidence.Recover Evidence.unknownEffect Evidence.recorded ∧
    Run Evidence.Recover Evidence.interrupted ∧
    (∀ n, Evidence.Consistent (Evidence.interrupted n)) ∧
    ¬ (∃ n, (Evidence.interrupted n).acknowledged = true) :=
  ⟨Evidence.recovery_can_finish, Evidence.interrupted_run,
    Evidence.interrupted_consistent, Evidence.interrupted_no_ack⟩

/-- A further count-only observer composes with the coarse relation, but this
chain does not restore publication information lost at the first stage. -/
theorem count_observer_composes :
    Refines (Relation.Comp Evidence.countObservation
      (fun s : Evidence.State => fun n : Nat => n = s.effects))
      {Evidence.recorded} {1} := by
  refine Evidence.coarse_refinement.trans ?_
  intro n hn
  have hn : n = 1 := hn
  subst n
  exact ⟨Evidence.unrecorded, rfl, rfl⟩

def beforeSeal : Snapshot.State (Bool × Bool) :=
  ⟨(true, true), (false, false), none⟩
def sealed : Snapshot.State (Bool × Bool) :=
  ⟨(true, true), Snapshot.mixed, none⟩
def externallyChanged : Snapshot.State (Bool × Bool) :=
  ⟨(false, false), Snapshot.mixed, none⟩
def compiled : Snapshot.State (Bool × Bool) :=
  ⟨(false, false), Snapshot.mixed, some Snapshot.mixed⟩

/-- Captured-input integrity can hold for a collection that never coexisted in
the live history. The compilation theorem must not be called snapshot coherence. -/
theorem compiled_collection_not_coherent :
    compiled.compiled = some Snapshot.mixed ∧ Snapshot.mixed ∉ Snapshot.history := by
  constructor
  · apply Snapshot.compile_sealed Snapshot.mixed (s := beforeSeal) trivial
    refine ⟨sealed, ⟨rfl, rfl, rfl⟩, externallyChanged, ?_, ?_⟩
    · exact Relation.ReflTransGen.single ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact Snapshot.never_coexisted

/-- There is no decidability or finite representation hypothesis on inputs. -/
theorem arbitrary_collections {I : Type} (inputs : I) (s t : Snapshot.State I)
    (sealed : Snapshot.Seal inputs s t) :
    ∃ u, Snapshot.CompileCaptured t u ∧ u.compiled = some inputs := by
  let u : Snapshot.State I := ⟨t.live, t.captured, some t.captured⟩
  refine ⟨u, ⟨rfl, rfl⟩, ?_⟩
  exact Snapshot.compile_sealed inputs trivial
    ⟨t, sealed, t, Relation.ReflTransGen.refl, ⟨rfl, rfl⟩⟩
end Examples.ExternalInteraction
