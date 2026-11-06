import SquareKit.Internal.Cubical.IdentityElimination
import Examples.CubicalSumFilling

/-! Strict identity elimination in a motive whose finite fiber depends on the
variable endpoint. The selected branch survives two context substitutions. -/
namespace Examples.CubicalIdentityElimination
open CategoryTheory SquareKit.Cubical.Presheaf CubicalPresheaf CubicalDiscreteFilling CubicalSumFilling

abbrev endpointProjection := projection (IdentitySingleton.fiber argument chosen)
abbrev motive := reindex result endpointProjection
abbrev motiveFilling := secondFilling.reindex endpointProjection
abbrev motiveLawful := (discreteFilling_lawful secondIndex (fun n => Fin (n+1))).reindex endpointProjection
abbrev eliminated : Term motive := IdentityElimination.eliminate argument chosen motive chosenResult
  motiveFilling.toComposition

theorem strict_branch : eliminated.reindex (IdentitySingleton.reflexivity argument chosen) = chosenResult :=
  IdentityElimination.eliminate_beta argument chosen motive chosenResult _
    (Filling.toComposition_lawful motiveLawful)

theorem two_substitutions :
    ((eliminated.reindex (IdentitySingleton.reflexivity argument chosen)).reindex successor).reindex twice =
      (chosenResult.reindex successor).reindex twice :=
  congrArg (fun t => (t.reindex successor).reindex twice) strict_branch

theorem selected_result :
    (((eliminated.reindex (IdentitySingleton.reflexivity argument chosen)).reindex successor).reindex twice).val
      (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ)) = (6 : Fin 7) := by
  rw [two_substitutions]
  rfl

theorem erasure_rejected :
    ((((eliminated.reindex (IdentitySingleton.reflexivity argument chosen)).reindex successor).reindex twice).val
      (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ))).val ≠ 0 := by
  rw [selected_result]
  decide

end Examples.CubicalIdentityElimination
