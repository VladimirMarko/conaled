import SquareKit.Internal.Cubical.FillingTransportLaws
import SquareKit.Internal.Cubical.TelescopeFillingSubstitution

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem family_reindex_eqToHom_heq {Γ Δ : Context.{u}} (h : Γ = Δ) (A : Family Δ) :
    HEq (reindex A (eqToHom h)) A := by cases h; rfl

theorem Filling.reindex_eqToHom_heq {Γ Δ : Context.{u}} (h : Γ = Δ) {A : Family Δ} (F : Filling A) :
    HEq (F.reindex (eqToHom h)) F := by cases h; rfl

theorem Term.reindex_eqToHom_heq {Γ Δ : Context.{u}} (h : Γ = Δ) {A : Family Δ} (t : Term A) :
    HEq (t.reindex (eqToHom h)) t := by cases h; rfl

theorem family_reindex_context_square {Γ Δ Ω Ξ : Context.{u}} (A : Family Ω)
    (s : Δ ⟶ Ω) (e : Γ ⟶ Δ) (h : Γ = Ξ) (r : Ξ ⟶ Ω) (hs : e ≫ s = eqToHom h ≫ r) :
    HEq (reindex (reindex A s) e) (reindex A r) :=
  (heq_of_eq (congrArg (reindex A) hs)).trans (family_reindex_eqToHom_heq h (reindex A r))

theorem Filling.reindex_context_square {Γ Δ Ω Ξ : Context.{u}} {A : Family Ω} (F : Filling A)
    (s : Δ ⟶ Ω) (e : Γ ⟶ Δ) (h : Γ = Ξ) (r : Ξ ⟶ Ω) (hs : e ≫ s = eqToHom h ≫ r) :
    HEq ((F.reindex s).reindex e) (F.reindex r) := by
  have hm : ∀ {σ τ : Γ ⟶ Ω}, σ = τ → HEq (F.reindex σ) (F.reindex τ) := by intro σ τ he; cases he; rfl
  exact (hm hs).trans (Filling.reindex_eqToHom_heq h (F.reindex r))

theorem Term.reindex_context_square {Γ Δ Ω Ξ : Context.{u}} {A : Family Ω} (t : Term A)
    (s : Δ ⟶ Ω) (e : Γ ⟶ Δ) (h : Γ = Ξ) (r : Ξ ⟶ Ω) (hs : e ≫ s = eqToHom h ≫ r) :
    HEq ((t.reindex s).reindex e) (t.reindex r) := by
  have hm : ∀ {σ τ : Γ ⟶ Ω}, σ = τ → HEq (t.reindex σ) (t.reindex τ) := by intro σ τ he; cases he; rfl
  exact (hm hs).trans (Term.reindex_eqToHom_heq h (t.reindex r))

theorem Telescope.map_congr {Γ Δ : Context.{u}} (T : Telescope Γ) {σ τ : Δ ⟶ Γ} (h : σ = τ) :
    eqToHom (congrArg (fun f => (T.reindex f).context) h) ≫ T.map τ = T.map σ := by cases h; simp

theorem Telescope.Fillings.reindex_heq {Γ Δ : Context.{u}} {T : Telescope Γ} (fs : T.Fillings)
    {σ τ : Δ ⟶ Γ} (h : σ = τ) : HEq (fs.reindex σ) (fs.reindex τ) := by cases h; rfl

end SquareKit.Cubical.Presheaf
