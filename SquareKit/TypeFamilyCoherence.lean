import SquareKit.FamilyCoherence
import SquareKit.TypeFamily

/-! Experimental compatibility of chosen categorical substitution comparisons
with the existing strict split Type-family equations. -/
noncomputable section
namespace SquareKit.TypeFamily
open CategoryTheory Limits Family
universe u
variable {Γ Δ Ξ : Type u} (A : Γ → Type u)

/-- Transport supplied by the existing strict identity equation. -/
def splitIdentity : DependentSquares.Ext Γ (DependentSquares.tySub A DependentSquares.idSub) ≅
    DependentSquares.Ext Γ A :=
  eqToIso (congrArg (DependentSquares.Ext Γ) (DependentSquares.tySub_id A))

/-- Transport supplied by the existing strict composition equation. -/
def splitComposition (σ : Δ → Γ) (τ : Ξ → Δ) :
    DependentSquares.Ext Ξ (DependentSquares.tySub (DependentSquares.tySub A σ) τ) ≅
      DependentSquares.Ext Ξ (DependentSquares.tySub A (DependentSquares.compSub σ τ)) :=
  eqToIso (congrArg (DependentSquares.Ext Ξ) (DependentSquares.tySub_comp A σ τ))

private theorem splitComposition_hom (σ : Δ → Γ) (τ : Ξ → Δ) :
    (splitComposition A σ τ).hom = 𝟙 _ := rfl

theorem identity_comparison :
    (pullbackIso A DependentSquares.idSub).hom ≫ (identityIso (display A)).hom =
      (splitIdentity A).hom := by
  change (pullbackIso A DependentSquares.idSub).hom ≫ comparison (display A) (↾DependentSquares.idSub) = _
  rw [pullbackIso_comparison]
  rfl

theorem composition_comparison (σ : Δ → Γ) (τ : Ξ → Δ) :
    (pullbackIso (DependentSquares.tySub A σ) τ).hom ≫
      Family.map (display (DependentSquares.tySub A σ)) (reindex (display A) (↾σ)) (↾τ)
        (pullbackIso A σ).hom (pullbackIso_display A σ) ≫
          (compositionIso (display A) (↾σ) (↾τ)).hom =
    (splitComposition A σ τ).hom ≫ (pullbackIso A (DependentSquares.compSub σ τ)).hom := by
  apply pullback.hom_ext <;> simp [Category.assoc, splitComposition_hom, pullbackIso_comparison_assoc]
  change (↾(DependentSquares.lift (A := DependentSquares.tySub A σ) τ)) ≫
    (↾(DependentSquares.lift (A := A) σ)) =
    (pullbackIso A (DependentSquares.compSub σ τ)).hom ≫
      comparison (display A) (↾(DependentSquares.compSub σ τ))
  rw [pullbackIso_comparison]
  rfl
  change display (DependentSquares.tySub A (DependentSquares.compSub σ τ)) =
    (pullbackIso A (DependentSquares.compSub σ τ)).hom ≫
      reindex (display A) (↾(DependentSquares.compSub σ τ))
  exact (pullbackIso_display A (DependentSquares.compSub σ τ)).symm

/-- Strict split term identity agrees with transport of the categorical section. -/
theorem split_identity_term (t : DependentSquares.Tm A) :
    (asSection (DependentSquares.tySub A DependentSquares.idSub)
      (DependentSquares.tmSub t DependentSquares.idSub)).val ≫
      (pullbackIso A DependentSquares.idSub).hom ≫ (identityIso (display A)).hom =
        (asSection A t).val := by
  exact congrArg (fun k : DependentSquares.Ext Γ (DependentSquares.tySub A DependentSquares.idSub) ⟶
    DependentSquares.Ext Γ A =>
      (asSection (DependentSquares.tySub A DependentSquares.idSub)
        (DependentSquares.tmSub t DependentSquares.idSub)).val ≫ k) (identity_comparison A)

/-- The strict tmSub composition equation controls the direct section route. -/
theorem split_composition_term (σ : Δ → Γ) (τ : Ξ → Δ) (t : DependentSquares.Tm A) :
    (asSection (DependentSquares.tySub (DependentSquares.tySub A σ) τ)
      (DependentSquares.tmSub (DependentSquares.tmSub t σ) τ)).val ≫
      (splitComposition A σ τ).hom ≫ (pullbackIso A (DependentSquares.compSub σ τ)).hom =
        (termSub (display A) (↾(DependentSquares.compSub σ τ)) (asSection A t)).val := by
  exact (congrArg (fun s : DependentSquares.Tm (DependentSquares.tySub A (DependentSquares.compSub σ τ)) =>
      (asSection _ s).val ≫ (pullbackIso A (DependentSquares.compSub σ τ)).hom)
    (DependentSquares.tmSub_comp t σ τ)).trans (term_substitution A (DependentSquares.compSub σ τ) t)
end SquareKit.TypeFamily
