import SquareKit.Internal.Cubical.FillingTransport

/-! Algebra of transporting selected filling data. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

@[ext] theorem Filling.ext {Γ : Context.{u}} {A : Family Γ} {F G : Filling A}
    (h : ∀ {Δ : Context.{u}} (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
      (b : OpenBox (Presheaf.reindex A p) φ), F.fill p φ b = G.fill p φ b) : F = G := by
  cases F
  cases G
  congr 1
  funext Δ p φ b
  exact h p φ b

theorem OpenBox.map_iso_roundtrip {Γ : Context.{u}} {A B : Family (total (interval Γ))}
    (e : A ≅ B) {φ : Cofibration Γ} (b : OpenBox B φ) : (b.map e.inv).map e.hom = b := by
  apply OpenBox.ext
  · apply PartialSection.ext
    intro x hx
    exact congrArg (fun η => η.app x (b.tube.val x hx)) e.inv_hom_id
  · apply Term.ext
    intro x
    exact congrArg (fun η => η.app ((endpointSub Γ false).mapElements.obj x) (b.base.val x)) e.inv_hom_id

theorem Filling.transport_eq {Γ : Context.{u}} {A B : Family Γ}
    (F : Filling A) (G : Filling B) (e : A ≅ B)
    (h : ∀ {Δ : Context.{u}} (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
      (b : OpenBox (Presheaf.reindex A p) φ),
      G.fill p φ (b.map (Functor.whiskerLeft p.mapElements e.hom)) =
        Term.map (Functor.whiskerLeft p.mapElements e.hom) (F.fill p φ b)) :
    F.transport e = G := by
  apply Filling.ext
  intro Δ p φ b
  exact (h p φ (b.map (Functor.whiskerLeft p.mapElements e.inv))).symm.trans
    (congrArg (G.fill p φ) (OpenBox.map_iso_roundtrip (Functor.isoWhiskerLeft p.mapElements e) b))

theorem Filling.transport_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (F : Filling A) (e : A ≅ B) (σ : Δ ⟶ Γ) :
    (F.transport e).reindex σ = (F.reindex σ).transport (Functor.isoWhiskerLeft σ.mapElements e) := rfl

theorem Filling.transport_trans {Γ : Context.{u}} {A B C : Family Γ}
    (F : Filling A) (e : A ≅ B) (d : B ≅ C) :
    (F.transport e).transport d = F.transport (e.trans d) := rfl

theorem Filling.transport_refl {Γ : Context.{u}} {A : Family Γ} (F : Filling A) :
    F.transport (Iso.refl A) = F := rfl

end SquareKit.Cubical.Presheaf
