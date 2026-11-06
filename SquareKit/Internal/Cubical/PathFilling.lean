import SquareKit.Internal.Cubical.PathFillingResult

/-! Dependent Path filling is constructed from filling of its body family. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

noncomputable def pathFilling {Γ : Context.{u}} {B : Family (total (interval Γ))}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) : Filling (path B a₀ a₁) where
  fill p φ b := pathFillingResult p φ b
    (F.fill (pathFillingContext p) (pathBoundaryFace φ) (pathFillingBox p φ b))
    (hF.fills (pathFillingContext p) (pathBoundaryFace φ) (pathFillingBox p φ b))

theorem pathFilling_fills {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true)))
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (path B a₀ a₁) p) φ) :
    b.Fills ((pathFilling F hF a₀ a₁).fill p φ b) :=
  pathFillingResult_fills p φ b _ (hF.fills _ _ _)

theorem pathFilling_uniform {Γ Δ Θ : Context.{u}} {B : Family (total (interval Γ))}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true)))
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (path B a₀ a₁) p) φ) (σ : Θ ⟶ Δ) :
    (pathFilling F hF a₀ a₁).fill (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ) =
      ((pathFilling F hF a₀ a₁).fill p φ b).reindex (liftSub (interval Δ) σ) := by
  let t := F.fill (pathFillingContext p) (pathBoundaryFace φ) (pathFillingBox p φ b)
  have ht : (pathFillingBox p φ b).Fills t := hF.fills _ _ _
  have ht' : (pathFillingBox (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ)).Fills
      (t.reindex (liftSub (interval (total (interval Δ))) (liftSub (interval Δ) σ))) :=
    (pathFillingBox_reindex p φ b σ).symm ▸ (ht.reindex (liftSub (interval Δ) σ))
  have he : F.fill (pathFillingContext (liftSub (interval Δ) σ ≫ p)) (pathBoundaryFace (φ.reindex σ))
      (pathFillingBox (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ)) =
      t.reindex (liftSub (interval (total (interval Δ))) (liftSub (interval Δ) σ)) :=
    (congrArg (F.fill (pathFillingContext (liftSub (interval Δ) σ ≫ p))
      (pathBoundaryFace (φ.reindex σ))) (pathFillingBox_reindex p φ b σ)).trans
        (hF.uniform (pathFillingContext p) (pathBoundaryFace φ) (pathFillingBox p φ b)
          (liftSub (interval Δ) σ))
  exact (pathFillingResult_congr (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ)
    _ (hF.fills _ _ _) _ ht' he).trans (pathFillingResult_reindex p φ b t ht σ ht')

theorem pathFilling_lawful {Γ : Context.{u}} {B : Family (total (interval Γ))}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) : (pathFilling F hF a₀ a₁).Lawful where
  fills := pathFilling_fills F hF a₀ a₁
  uniform := pathFilling_uniform F hF a₀ a₁

end SquareKit.Cubical.Presheaf
