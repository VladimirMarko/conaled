import SquareKit.Internal.Cubical.NormalizedIdentityElimination
import SquareKit.Internal.Cubical.IdentitySingletonSubstitution

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace NormalizedIdentitySingleton
variable {Γ Δ : Context.{u}} (A : Family Γ) (a : Term A)

def reindexMap (σ : Δ ⟶ Γ) : context (reindex A σ) (a.reindex σ) ⟶ context A a :=
  (presentation (reindex A σ) (a.reindex σ)).inv ≫
    IdentitySingleton.reindexMap A a σ ≫ (presentation A a).hom

theorem presentation_reindexMap (σ : Δ ⟶ Γ) :
    (presentation (reindex A σ) (a.reindex σ)).hom ≫ reindexMap A a σ =
      IdentitySingleton.reindexMap A a σ ≫ (presentation A a).hom := by
  simp [reindexMap]

theorem reindexMap_reflexivity (σ : Δ ⟶ Γ) :
    reflexivity (reindex A σ) (a.reindex σ) ≫ reindexMap A a σ = σ ≫ reflexivity A a := by
  change (IdentitySingleton.reflexivity (reindex A σ) (a.reindex σ) ≫
    (presentation (reindex A σ) (a.reindex σ)).hom) ≫ reindexMap A a σ = _
  rw [Category.assoc,presentation_reindexMap,← Category.assoc,IdentitySingleton.reindexMap_reflexivity]
  rfl

end NormalizedIdentitySingleton
end SquareKit.Cubical.Presheaf
