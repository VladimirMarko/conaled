import SquareKit.Internal.Cubical.FunctionFilling
import SquareKit.Internal.Cubical.FillingTransport

/-! The chosen dependent function composition is stable when its input
families and their chosen operations are reindexed. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace FunctionComposition
variable {Γ Δ E : Context.{u}} {A : Family Γ} {B : Family (total A)}

theorem body_reindex (F : Filling A) (hF : F.Lawful) (G : Composition B)
    (σ : E ⟶ Γ) (p : total (interval Δ) ⟶ E) (φ : Cofibration Δ)
    (b : OpenBox (reindex (pi A B) (p ≫ σ)) φ) :
    body (F.reindex σ) (hF.reindex σ) (G.reindex (liftSub A σ)) p φ
      (b.map (Functor.whiskerLeft p.mapElements (piReindex A B σ))) =
      body F hF G (p ≫ σ) φ b := rfl

theorem comp_reindex (F : Filling A) (hF : F.Lawful) (G : Composition B)
    (σ : E ⟶ Γ) (p : total (interval Δ) ⟶ E) (φ : Cofibration Δ)
    (b : OpenBox (reindex (pi A B) (p ≫ σ)) φ) :
    comp (F.reindex σ) (hF.reindex σ) (G.reindex (liftSub A σ)) p φ
      (b.map (Functor.whiskerLeft p.mapElements (piReindex A B σ))) =
      Term.map (Functor.whiskerLeft (endpointSub Δ true ≫ p).mapElements (piReindex A B σ))
        (comp F hF G (p ≫ σ) φ b) := by
  apply Term.map_injective_of_iso (piReindexIso (reindex A σ) (reindex B (liftSub A σ))
    (endpointSub Δ true ≫ p))
  change Term.map (piReindex (reindex A σ) (reindex B (liftSub A σ)) (endpointSub Δ true ≫ p)) _ = _
  rw [comp_normalize,body_reindex]
  exact (comp_normalize F hF G (p ≫ σ) φ b).symm

end FunctionComposition
end SquareKit.Cubical.Presheaf
