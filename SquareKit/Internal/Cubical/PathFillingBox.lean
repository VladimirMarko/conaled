import SquareKit.Internal.Cubical.PathBoundaries
import SquareKit.Internal.Cubical.Filling

/-! The body box for path filling fixes both path endpoints throughout the
filling dimension and retains the original partial path tube. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def pathFillingContext {Γ Δ : Context.{u}} (p : total (interval Δ) ⟶ Γ) :
    total (interval (total (interval Δ))) ⟶ total (interval Γ) :=
  swapIntervals Δ ≫ liftSub (interval Γ) p

noncomputable def pathFillingBox {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))}
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (path B a₀ a₁) p) φ) :
    OpenBox (reindex B (pathFillingContext p)) (pathBoundaryFace φ) where
  tube := ((b.tube.map (pathReindex B a₀ a₁ p)).pathBoundary).reindex (swapIntervals Δ)
  base := pathApp (Term.map (pathReindex B a₀ a₁ (endpointSub Δ false ≫ p)) b.base)
  boundary x h := by
    rcases x with @⟨I,⟨δ,j⟩⟩
    let y := Δ.elementsMk I δ
    let s := b.tube.map (pathReindex B a₀ a₁ p)
    let z := (total (interval (total (interval Δ)))).elementsMk I
      ⟨⟨δ,(endpoint Δ false).val y⟩,j⟩
    have hp : (pathBoundaryFace (φ.reindex (projection (interval Δ)))).full z := h
    rcases (Cofibration.full_join _ _ ((total (interval Δ)).elementsMk I ⟨δ,j⟩)).mp h with hφ | he
    · have hv := s.pathBoundary_old z hp hφ
      exact hv.trans (congrArg (fun v => v.val.val (𝟙 _) j) (b.boundary y hφ))
    · rcases (Cofibration.full_join _ _ ((total (interval Δ)).elementsMk I ⟨δ,j⟩)).mp he with h₀ | h₁
      · have hr := (Cofibration.full_endpoint (generic (interval Δ)) false
          ((total (interval Δ)).elementsMk I ⟨δ,j⟩)).mp h₀
        change j = (endpoint Δ false).val y at hr
        subst j
        exact eq_of_heq ((s.pathBoundary_zero z hp h₀).trans
          (heq_of_eq ((b.base.val y).property (𝟙 _)).1).symm)
      · have hr := (Cofibration.full_endpoint (generic (interval Δ)) true
          ((total (interval Δ)).elementsMk I ⟨δ,j⟩)).mp h₁
        change j = (endpoint Δ true).val y at hr
        subst j
        exact eq_of_heq ((s.pathBoundary_one z hp h₁).trans
          (heq_of_eq ((b.base.val y).property (𝟙 _)).2).symm)

theorem pathFillingBox_reindex {Γ Δ Θ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))}
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (path B a₀ a₁) p) φ) (σ : Θ ⟶ Δ) :
    pathFillingBox (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ) =
      (pathFillingBox p φ b).reindex (liftSub (interval Δ) σ) := by
  apply OpenBox.ext
  · let s := b.tube.map (pathReindex B a₀ a₁ p)
    exact (congrArg (fun s => s.reindex (swapIntervals Θ))
      (s.pathBoundary_reindex (liftSub (interval Δ) σ))).symm
  · exact pathApp_reindex
      (Term.map (pathReindex B a₀ a₁ (endpointSub Δ false ≫ p)) b.base) σ

end SquareKit.Cubical.Presheaf
