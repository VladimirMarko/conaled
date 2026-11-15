import SquareKit.Internal.Cubical.PathFillingBody
import SquareKit.Internal.Cubical.Substitution

/-! Return the filled dependent path through the full substitution equivalence. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

section
variable {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
  {a₀ : Term (reindex B (endpointSub Γ false))}
  {a₁ : Term (reindex B (endpointSub Γ true))}
  (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
  (b : OpenBox (reindex (path B a₀ a₁) p) φ)
  (t : Term (reindex B (pathFillingContext p)))
  (ht : (pathFillingBox p φ b).Fills t)

def pathFillingResult : Term (reindex (path B a₀ a₁) p) :=
  Term.map (pathReindexIso B a₀ a₁ p).inv (pathFillingBody_path p φ b t ht)

theorem pathFillingResult_normalize :
    Term.map (pathReindex B a₀ a₁ p) (pathFillingResult p φ b t ht) =
      pathFillingBody_path p φ b t ht :=
  Term.map_iso_roundtrip (pathReindexIso B a₀ a₁ p).symm _

theorem pathFillingResult_cap :
    (pathFillingResult p φ b t ht).reindex (endpointSub Δ false) = b.base := by
  apply Term.map_injective_of_iso (pathReindexIso B a₀ a₁ (endpointSub Δ false ≫ p))
  apply pathApp_injective
  have hn := congrArg (fun s => pathApp
    (Term.map (pathReindex (reindex B (liftSub (interval Γ) p))
      (a₀.reindex p) (a₁.reindex p) (endpointSub Δ false))
      (s.reindex (endpointSub Δ false)))) (pathFillingResult_normalize p φ b t ht)
  exact hn.trans ht.1

theorem pathFillingResult_tube (x : (total (interval Δ)).Elements)
    (hx : (φ.reindex (projection (interval Δ))).full x) :
    (pathFillingResult p φ b t ht).val x = b.tube.val x hx := by
  apply ((pathReindexIso B a₀ a₁ p).app x).toEquiv.injective
  let s := b.tube.map (pathReindex B a₀ a₁ p)
  change (Term.map (pathReindex B a₀ a₁ p) (pathFillingResult p φ b t ht)).val x = s.val x hx
  calc
    _ = (pathFillingBody_path p φ b t ht).val x :=
      congrArg (fun v => v.val x) (pathFillingResult_normalize p φ b t ht)
    _ = _ := by
      apply Subtype.ext
      apply PiElement.ext
      intro y f j
      have hy := (φ.reindex (projection (interval Δ))).full_natural f hx
      let z := extendObj (interval (total (interval Δ))) y j
      have hz : (pathBoundaryFace φ).full
          ((projection (interval (total (interval Δ)))).mapElements.obj
            ((swapIntervals Δ).mapElements.obj z)) :=
        (Cofibration.full_join _ _ _).mpr (Or.inl hy)
      have hfill := ht.2 ((swapIntervals Δ).mapElements.obj z) hz
      have hold := s.pathBoundary_old z hz hy
      have hprop : (s.val x hx).val.val f j = (s.val y hy).val.val (𝟙 _) j := by
        have h := congrArg (fun v => v.val.val (𝟙 _) j) (s.property f hx)
        change (s.val x hx).val.val (f ≫ 𝟙 _) j = _ at h
        simpa only [Category.comp_id] using h
      exact hfill.trans (hold.trans hprop.symm)

theorem pathFillingResult_fills : b.Fills (pathFillingResult p φ b t ht) :=
  ⟨pathFillingResult_cap p φ b t ht, pathFillingResult_tube p φ b t ht⟩

theorem pathFillingResult_congr (t' : Term (reindex B (pathFillingContext p)))
    (ht' : (pathFillingBox p φ b).Fills t') (h : t = t') :
    pathFillingResult p φ b t ht = pathFillingResult p φ b t' ht' := by
  cases h
  rfl

theorem pathFillingResult_reindex {Θ : Context.{u}} (σ : Θ ⟶ Δ)
    (ht' : (pathFillingBox (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ)).Fills
      (t.reindex (liftSub (interval (total (interval Δ))) (liftSub (interval Δ) σ)))) :
    pathFillingResult (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ)
      (t.reindex (liftSub (interval (total (interval Δ))) (liftSub (interval Δ) σ))) ht' =
      (pathFillingResult p φ b t ht).reindex (liftSub (interval Δ) σ) := by
  apply Term.map_injective_of_iso (pathReindexIso B a₀ a₁ (liftSub (interval Δ) σ ≫ p))
  apply pathApp_injective
  have hn := congrArg (fun s => pathApp
    (Term.map (pathReindex (reindex B (liftSub (interval Γ) p))
      (a₀.reindex p) (a₁.reindex p) (liftSub (interval Δ) σ))
      (s.reindex (liftSub (interval Δ) σ)))) (pathFillingResult_normalize p φ b t ht)
  have hn' := congrArg pathApp (pathFillingResult_normalize
    (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ)
    (t.reindex (liftSub (interval (total (interval Δ))) (liftSub (interval Δ) σ))) ht')
  exact hn'.trans hn.symm

end
end SquareKit.Cubical.Presheaf
