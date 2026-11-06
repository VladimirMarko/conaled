import SquareKit.Internal.Cubical.ContextIsoSections

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem Term.reindex_injective_iso {Γ Δ : Context.{u}} (e : Γ ≅ Δ) {A : Family Δ} :
    Function.Injective (fun t : Term A => t.reindex e.hom) := by
  intro t s h
  exact (Term.descendIso_reindex_section e t).symm.trans
    ((congrArg (fun t => t.descendIso e) h).trans (Term.descendIso_reindex_section e s))

theorem Term.reindex_heq_maps {Γ Δ : Context.{u}} {A : Family Γ} (t : Term A)
    {σ τ : Δ ⟶ Γ} (e : σ = τ) : HEq (t.reindex σ) (t.reindex τ) := by cases e; rfl

theorem Term.descendIso_square {Γ Δ Ω : Context.{u}} (e : Γ ≅ Δ) {A : Family Δ}
    (t : Term (Presheaf.reindex A e.hom)) (r : Ω ⟶ Γ) (s : Ω ⟶ Δ) (hs : s = r ≫ e.hom) :
    HEq ((t.descendIso e).reindex s) (t.reindex r) :=
  (Term.reindex_heq_maps (t.descendIso e) hs).trans
    (heq_of_eq (congrArg (fun q => q.reindex r) (Term.descendIso_reindex e t)))

end SquareKit.Cubical.Presheaf

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem Term.descendIso_naturality {Γ Γ' Δ Δ' : Context.{u}}
    (e : Γ ≅ Δ) (e' : Γ' ≅ Δ') (τ : Δ' ⟶ Δ) (τ₀ : Γ' ⟶ Γ)
    (hs : e'.hom ≫ τ = τ₀ ≫ e.hom) {A : Family Δ}
    (t : Term (Presheaf.reindex A e.hom))
    (t' : Term (Presheaf.reindex (Presheaf.reindex A τ) e'.hom))
    (ht : HEq t' (t.reindex τ₀)) :
    t'.descendIso e' = (t.descendIso e).reindex τ := by
  apply Term.reindex_injective_iso e'
  apply eq_of_heq
  exact (heq_of_eq (Term.descendIso_reindex e' t')).trans
    (ht.trans ((heq_of_eq (congrArg (fun q => q.reindex τ₀) (Term.descendIso_reindex e t))).symm.trans
      (Term.reindex_heq_maps (t.descendIso e) hs.symm)))

end SquareKit.Cubical.Presheaf

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def Term.reindexSquare {Γ Δ Ω Ξ : Context.{u}} (C : Family Ω)
    (r : Γ ⟶ Ω) (σ : Δ ⟶ Γ) (r' : Δ ⟶ Ξ) (τ : Ξ ⟶ Ω)
    (h : r' ≫ τ = σ ≫ r) (d : Term (Presheaf.reindex C r)) :
    Term (Presheaf.reindex (Presheaf.reindex C τ) r') :=
  (d.reindex σ).convert (congrArg (Presheaf.reindex C) h.symm)

theorem Term.reindexSquare_heq {Γ Δ Ω Ξ : Context.{u}} (C : Family Ω)
    (r : Γ ⟶ Ω) (σ : Δ ⟶ Γ) (r' : Δ ⟶ Ξ) (τ : Ξ ⟶ Ω)
    (h : r' ≫ τ = σ ≫ r) (d : Term (Presheaf.reindex C r)) :
    HEq (Term.reindexSquare C r σ r' τ h d) (d.reindex σ) := Term.convert_heq _ _

end SquareKit.Cubical.Presheaf
