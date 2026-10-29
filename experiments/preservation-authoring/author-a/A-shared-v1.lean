import Applications.Interaction.EvidenceBounds
namespace AuthorAShared
open Interaction Interaction.Evidence

theorem shared : ∀ t ∈ some '' encodedReachable,
    (t.map Prod.fst).getD 0 ≤ 1 := by
  have optional : Refines (fun (e : Encoded) (t : Option Encoded) => some e = t)
      encodedReachable (some '' encodedReachable) := by
    rintro t ⟨e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  have covered := encoding_coverage.trans optional
  exact covered.bound State.effects (fun t => (t.map Prod.fst).getD 0) id
    (fun _ _ h => h)
    (by
      rintro s t ⟨e, he, ht⟩
      cases ht
      cases he
      exact le_rfl)
    1 (fun s hs => (reachable_effects s hs).le)

theorem acknowledged : some (encode recorded) ∈ some '' encodedReachable := by
  refine ⟨encode recorded, ⟨recorded, ?_, rfl⟩, rfl⟩
  exact Relation.ReflTransGen.single recovery_can_finish
example : ((some (encode recorded)).map Prod.fst).getD 0 ≤ 1 := shared _ acknowledged
example : (encode recorded).2 = (true, true) := rfl
end AuthorAShared
