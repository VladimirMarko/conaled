import Applications.Interaction.EvidenceBounds
namespace AuthorADirect
open Interaction Interaction.Evidence

theorem optional_bound : ∀ t ∈ some '' encodedReachable,
    (t.map Prod.fst).getD 0 ≤ 1 := by
  rintro t ⟨x, ⟨s, hs, rfl⟩, rfl⟩
  exact (reachable_effects s hs).le

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
end AuthorADirect
