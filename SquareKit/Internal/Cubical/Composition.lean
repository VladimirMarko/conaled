import SquareKit.Internal.Cubical.Filling

/-! Endpoint composition exposes only the far face. Its boundary and substitution
laws are separate from the selected operation. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

structure Composition {Γ : Context.{u}} (A : Family Γ) where
  comp : {Δ : Context.{u}} → (p : total (interval Δ) ⟶ Γ) →
    (φ : Cofibration Δ) → OpenBox (reindex A p) φ →
    Term (reindex A (endpointSub Δ true ≫ p))

structure Composition.Lawful {Γ : Context.{u}} {A : Family Γ} (C : Composition A) : Prop where
  boundary : ∀ {Δ : Context.{u}} (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex A p) φ) (x : Δ.Elements) (hx : φ.full x),
    (C.comp p φ b).val x = b.tube.val ((endpointSub Δ true).mapElements.obj x) hx
  uniform : ∀ {Δ Θ : Context.{u}} (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex A p) φ) (σ : Θ ⟶ Δ),
    C.comp (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ) =
      (C.comp p φ b).reindex σ

def Filling.toComposition {Γ : Context.{u}} {A : Family Γ} (F : Filling A) : Composition A where
  comp := F.comp

theorem Filling.toComposition_lawful {Γ : Context.{u}} {A : Family Γ}
    {F : Filling A} (h : F.Lawful) : F.toComposition.Lawful where
  boundary := Filling.comp_boundary h
  uniform := Filling.comp_reindex h

end SquareKit.Cubical.Presheaf
