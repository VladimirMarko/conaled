import SquareKit.Internal.Cubical.PartialSections

/-! Restrict a partial section to a smaller face, or read it as a total section
when every generalized element belongs to its face. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem PartialSection.val_heq {Γ : Context.{u}} {A : Family Γ} {φ : Cofibration Γ}
    (a : PartialSection A φ) {x y : Γ.Elements} (h : x = y) (hx : φ.full x) (hy : φ.full y) :
    HEq (a.val x hx) (a.val y hy) := by
  cases h
  rfl

def PartialSection.restrict {Γ : Context.{u}} {A : Family Γ} {φ ψ : Cofibration Γ}
    (a : PartialSection A φ) (h : ∀ x, ψ.full x → φ.full x) : PartialSection A ψ where
  val x p := a.val x (h x p)
  property f _ := a.property f _

def PartialSection.toTerm {Γ : Context.{u}} {A : Family Γ} {φ : Cofibration Γ}
    (a : PartialSection A φ) (h : ∀ x, φ.full x) : Term A where
  val x := a.val x (h x)
  property f := a.property f _

theorem PartialSection.restrict_reindex {Γ Δ : Context.{u}} {A : Family Γ}
    {φ ψ : Cofibration Γ} (a : PartialSection A φ) (h : ∀ x, ψ.full x → φ.full x)
    (σ : Δ ⟶ Γ) :
    (a.restrict h).reindex σ = (a.reindex σ).restrict (fun x => h (σ.mapElements.obj x)) := rfl

theorem PartialSection.toTerm_reindex {Γ Δ : Context.{u}} {A : Family Γ}
    {φ : Cofibration Γ} (a : PartialSection A φ) (h : ∀ x, φ.full x) (σ : Δ ⟶ Γ) :
    (a.toTerm h).reindex σ = (a.reindex σ).toTerm (fun x => h (σ.mapElements.obj x)) := rfl

end SquareKit.Cubical.Presheaf
