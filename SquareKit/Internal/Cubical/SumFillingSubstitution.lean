import SquareKit.Internal.Cubical.SumFilling

/-! The chosen dependent sum filler commutes with substitution of its inputs. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem sigmaFilling_reindex {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (σ : Δ ⟶ Γ) :
    (sigmaFilling F hF G).reindex σ =
      sigmaFilling (F.reindex σ) (hF.reindex σ) (G.reindex (liftSub A σ)) := rfl

end SquareKit.Cubical.Presheaf
