import Examples.ExternalInteraction
import Examples.InteractionInterfaces
import Applications.Optimization.Basic

/-! Checked uses of relational images and backward requirements for #196.
The observation fibers below contain only admissible attempted worlds. Safety,
admissible observations, execution witnesses and progress remain separate. -/
namespace Examples.InteractionTransport
universe u
open Interaction
open SquareKit.RelationTransport

/-- Order-sensitive specialization: increment, then double, sends 3 to 8. -/
theorem possible_eight :
    image (Relation.Comp (fun x y : Nat => x + 1 = y)
      (fun y z => y * 2 = z)) {3} = {8} := by
  rw [image_comp, image_graph, image_graph]
  simp

/-- Cost bounds pulled through a deterministic interpretation use the existing
optimization objective, with no enumeration or computability assumption. -/
theorem objective_requirement {P Q K : Type*} [LE K] (C : P → Q) (J : Q → K) (b : K) :
    requirement (fun p q => C p = q) {q | J q ≤ b} =
      {p | Optimization.pullback C J p ≤ b} := by
  rw [requirement_graph]
  rfl

/-- The indexed optimization observation square computes the existential image
specialization, not a universal fact about every world with that observation. -/
theorem observation_image {I P Q : Type u} (o : P → Q) (i : I) (A : Set P) :
    (Optimization.observationSquare (I := I) o).spec (i, A) =
      (i, image (fun p q => o p = q) A) := by
  rw [image_graph]
  rfl

namespace LostAcknowledgment
open Evidence

def attempted : Set State := {s | Attempt initial s}
def observer (s : attempted) : Option Nat := observe s.val

/-- The known model admits silence, including a world where an effect occurred. -/
theorem silence_admissible : none ∈ observer '' (Set.univ : Set attempted) :=
  ⟨⟨unknownEffect, ambiguous_worlds_admissible.2⟩, trivial, rfl⟩

/-- A universal absence requirement is false at that same admissible silence.
Use the restricted-converse theorem to connect relational and fiber semantics. -/
theorem silence_not_absence :
    none ∉ requirement (fun o s => s ∈ attempted ∧ observe s = o)
      {s | s.effects = 0} := by
  rw [requirement_restricted_converse]
  intro h
  have bad : unknownEffect.effects = 0 :=
    h (x := ⟨unknownEffect, ambiguous_worlds_admissible.2⟩) rfl
  exact (by decide : unknownEffect.effects ≠ 0) bad

/-- Every world in this bounded attempt model observes silence. -/
theorem observer_none (s : attempted) : observer s = none := by
  rcases s.property with h | h
  · change observe s.val = none
    rw [h]
    rfl
  · change observe s.val = none
    rw [h]
    rfl

/-- An impossible observation satisfies even the empty universal predicate.
Its lack of an admissible witness prevents interpreting this as knowledge. -/
theorem impossible_observation :
    some 2 ∈ Set.kernImage observer ∅ ∧
    some 2 ∉ observer '' (Set.univ : Set attempted) := by
  have absent : ∀ s, observer s ≠ some 2 := by
    intro s
    rw [observer_none]
    simp
  constructor
  · intro s h
    exact False.elim (absent s h)
  · rintro ⟨s, _, h⟩
    exact absent s h

end LostAcknowledgment

/-- Recovery preserves the effect count through any finite number of permitted
steps, including acknowledgment. Composition exposes the intermediate
requirement; it supplies no scheduler or existence assertion. -/
theorem recovery_requirement (n : Nat) :
    {s : Evidence.State | s.effects = n} ⊆
      requirement (Relation.Comp (Relation.ReflTransGen Evidence.Recover)
        Evidence.Acknowledge) {s | s.effects = n ∧ s.acknowledged = true} := by
  rw [requirement_comp]
  intro s hs t recovery u ack
  have effects := (Evidence.recover_effects n).closure hs recovery
  rcases ack with ⟨_, rfl⟩
  exact ⟨effects, rfl⟩

/-- Publication supplies an enabled finishing step after every permitted finite
recovery, without asserting that a scheduler eventually takes that step. -/
theorem recovery_enabled :
    {s : Evidence.State | s.published = true} ⊆
      requirement (Relation.ReflTransGen Evidence.Recover)
        {t | ∃ u, Evidence.Acknowledge t u} := by
  intro s hs t recovery
  exact ⟨{t with acknowledged := true},
    Evidence.recover_published.closure hs recovery, rfl⟩

/-- Separate coverage: a permitted recovery followed by acknowledgment exists.
The universal requirement above proves the result for this concrete execution. -/
theorem recovery_witness :
    ∃ t, Relation.Comp (Relation.ReflTransGen Evidence.Recover) Evidence.Acknowledge
      Evidence.unknownEffect t ∧ t.effects = 1 ∧ t.acknowledged = true := by
  have recovered := Relation.ReflTransGen.single Evidence.recovery_can_finish
  obtain ⟨t, ack⟩ := recovery_enabled
    (show Evidence.unknownEffect.published = true from rfl) Evidence.recorded recovered
  have run : Relation.Comp (Relation.ReflTransGen Evidence.Recover) Evidence.Acknowledge
      Evidence.unknownEffect t := ⟨Evidence.recorded, recovered, ack⟩
  exact ⟨t, run, recovery_requirement 1 (show Evidence.unknownEffect.effects = 1 from rfl)
    _ run⟩

/-- Capture and permitted interference leave exactly the assertion needed by
compilation. The arbitrary collection type has no finiteness/decidability bound. -/
theorem captured_requirement {I : Type*} (inputs : I) :
    (Set.univ : Set (Snapshot.State I)) ⊆
      requirement (Relation.Comp (Snapshot.Seal inputs)
        (Relation.Comp (Relation.ReflTransGen Snapshot.Environment) Snapshot.CompileCaptured))
        {s | s.compiled = some inputs} := by
  rw [requirement_comp, requirement_comp]
  intro s _ t sealedStep u environment v compile
  have captured : u.captured = inputs :=
    (Snapshot.captured_stable inputs).closure sealedStep.2.1 environment
  exact compile.2.trans (congrArg some captured)

/-- Recover the ordinary caller-facing safety contract from the requirement. -/
theorem captured_safe {I : Type*} (inputs : I) :
    Safe (fun _ => True)
      (Relation.Comp (Snapshot.Seal inputs)
        (Relation.Comp (Relation.ReflTransGen Snapshot.Environment) Snapshot.CompileCaptured))
      (fun s => s.compiled = some inputs) :=
  (safe_iff_subset_requirement _ _ _).mpr (captured_requirement inputs)

/-- A source-side requirement transfers through a coarse refinement without
claiming the discarded publication observation is preserved. -/
theorem refined_count : ({Evidence.unrecorded} : Set Evidence.State) ⊆ {s | s.effects = 1} := by
  apply Evidence.coarse_refinement.requirement
  intro s hs t related
  have hs : s = Evidence.recorded := hs
  subst s
  exact related.symm

end Examples.InteractionTransport
