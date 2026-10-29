import Applications.Interaction.EvidenceBounds
namespace AuthorAShared
open Interaction Interaction.Evidence

theorem optional_bound : ∀ t ∈ some '' encodedReachable,
    (t.map Prod.fst).getD 0 ≤ 1 := by
  have optionalCoverage : Refines (fun (x : Encoded) y => some x = y)
      encodedReachable (some '' encodedReachable) := by
    rintro t ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  have composed := encoding_coverage.trans optionalCoverage
  exact composed.bound State.effects (fun t => (t.map Prod.fst).getD 0) id
    (fun _ _ h => h)
    (by
      rintro s t ⟨x, hx, rfl⟩
      cases hx
      exact Nat.le_refl _)
    1 (fun s hs => (reachable_effects s hs).le)

theorem acknowledged_reachable : recorded ∈ reachable :=
  Relation.ReflTransGen.single recovery_can_finish

theorem acknowledged_case :
    some (1, (true, true)) ∈ some '' encodedReachable ∧
    ((some (1, (true, true))).map Prod.fst).getD 0 ≤ 1 := by
  have h : some (1, (true, true)) ∈ some '' encodedReachable :=
    ⟨encode recorded, ⟨recorded, acknowledged_reachable, rfl⟩, rfl⟩
  exact ⟨h, optional_bound _ h⟩
#print axioms optional_bound
#print axioms acknowledged_case
end AuthorAShared
