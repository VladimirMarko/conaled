import SquareKit.Internal.Cubical.ContextIsoSectionSquares

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem Term.descendIso_boundary {Γ Δ Γ₀ Δ₀ : Context.{u}} (e : Γ ≅ Δ) (b : Γ₀ ≅ Δ₀)
    (r : Γ₀ ⟶ Γ) (s : Δ₀ ⟶ Δ) (h : b.hom ≫ s = r ≫ e.hom) {A : Family Δ}
    (t : Term (Presheaf.reindex A e.hom)) (d : Term (Presheaf.reindex A s))
    (ht : HEq (t.reindex r) (d.reindex b.hom)) :
    (t.descendIso e).reindex s = d := by
  apply Term.reindex_injective_iso b
  exact eq_of_heq ((Term.descendIso_square e t r (b.hom ≫ s) h).trans ht)

end SquareKit.Cubical.Presheaf

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem Term.reindex_convert {Γ Δ : Context.{u}} {A : Family Γ} (t : Term A)
    {σ τ : Δ ⟶ Γ} (h : σ = τ) :
    (t.reindex σ).convert (congrArg (Presheaf.reindex A) h) = t.reindex τ := by cases h; rfl

theorem Term.reindexSquare_of_reindex {Γ Δ Ω Ξ : Context.{u}} (C : Family Ω)
    (r : Γ ⟶ Ω) (σ : Δ ⟶ Γ) (r' : Δ ⟶ Ξ) (τ : Ξ ⟶ Ω)
    (h : r' ≫ τ = σ ≫ r) (t : Term C) :
    Term.reindexSquare C r σ r' τ h (t.reindex r) = (t.reindex τ).reindex r' :=
  Term.reindex_convert t h.symm

end SquareKit.Cubical.Presheaf
