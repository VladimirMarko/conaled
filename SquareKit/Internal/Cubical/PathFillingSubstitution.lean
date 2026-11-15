import SquareKit.Internal.Cubical.PathFilling
import SquareKit.Internal.Cubical.FillingTransportLaws

/-! Reindexing the selected body filler preserves the selected Path filler. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem pathFilling_reindex_family {Γ Δ E : Context.{u}} {B : Family (total (interval Γ))}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term (reindex B (endpointSub Γ false))) (a₁ : Term (reindex B (endpointSub Γ true)))
    (σ : E ⟶ Γ) (p : total (interval Δ) ⟶ E) (φ : Cofibration Δ)
    (b : OpenBox (reindex (path B a₀ a₁) (p ≫ σ)) φ) :
    (pathFilling (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _) (a₀.reindex σ) (a₁.reindex σ)).fill p φ
      (b.map (Functor.whiskerLeft p.mapElements (pathReindex B a₀ a₁ σ))) =
      Term.map (Functor.whiskerLeft p.mapElements (pathReindex B a₀ a₁ σ))
        ((pathFilling F hF a₀ a₁).fill (p ≫ σ) φ b) := by
  apply Term.map_injective_of_iso (pathReindexIso (reindex B (liftSub (interval Γ) σ))
    (a₀.reindex σ) (a₁.reindex σ) p)
  change Term.map (pathReindex (reindex B (liftSub (interval Γ) σ)) (a₀.reindex σ) (a₁.reindex σ) p) _ = _
  change Term.map _ (pathFillingResult p φ _ _ _) = _
  let b' := b.map (Functor.whiskerLeft p.mapElements (pathReindex B a₀ a₁ σ))
  have hn := pathFillingResult_normalize p φ b'
    ((F.reindex (liftSub (interval Γ) σ)).fill (pathFillingContext p) (pathBoundaryFace φ) (pathFillingBox p φ b'))
    ((hF.reindex (liftSub (interval Γ) σ)).fills (pathFillingContext p) (pathBoundaryFace φ) (pathFillingBox p φ b'))
  exact hn.trans (pathFillingResult_normalize (p ≫ σ) φ b
    (F.fill (pathFillingContext (p ≫ σ)) (pathBoundaryFace φ) (pathFillingBox (p ≫ σ) φ b))
    (hF.fills _ _ _)).symm

theorem pathFilling_reindex_iso {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term (reindex B (endpointSub Γ false))) (a₁ : Term (reindex B (endpointSub Γ true))) (σ : Δ ⟶ Γ) :
    ((pathFilling F hF a₀ a₁).reindex σ).transport (pathReindexIso B a₀ a₁ σ) =
      pathFilling (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _) (a₀.reindex σ) (a₁.reindex σ) :=
  Filling.transport_eq _ _ _ (pathFilling_reindex_family F hF a₀ a₁ σ)

end SquareKit.Cubical.Presheaf
