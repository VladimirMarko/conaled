import Applications.Interaction.EvidenceBounds
namespace AuthorA
open Interaction Interaction.Evidence

theorem direct : ∀ t ∈ some '' encodedReachable,
    (t.map Prod.fst).getD 0 ≤ 1 := by
  rintro t ⟨e, ⟨s, hs, rfl⟩, rfl⟩
  exact (reachable_effects s hs).le

theorem acknowledged : some (encode recorded) ∈ some '' encodedReachable := by
  refine ⟨encode recorded, ⟨recorded, ?_, rfl⟩, rfl⟩
  exact Relation.ReflTransGen.single recovery_can_finish

example : ((some (encode recorded)).map Prod.fst).getD 0 ≤ 1 :=
  direct _ acknowledged
example : (encode recorded).2 = (true, true) := rfl
end AuthorA
