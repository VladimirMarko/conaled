import SquareKit.RepresentedFamilies
import Mathlib.CategoryTheory.Types.Basic

/-! A signature-free instance built directly from dependent functions. No
PathTransport model or primitive base/fiber/identity assignment is required. -/
namespace SquareKit.TypeFamilyRepresentation
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def families : IndexedFamilies (Type u) where
  Ty Γ := Γ → Type u
  Tm Γ A := ULift.{u+1} ((γ : Γ) → A γ)
  pullTy A f := fun δ => A (f δ)
  pullTm t f := ⟨fun δ => t.down (f δ)⟩
  ty_id _ := rfl
  ty_comp _ _ _ := rfl
  tm_id _ := HEq.rfl
  tm_comp _ _ _ := HEq.rfl

def representation : families.{u}.Representation where
  ext Γ A := (γ : Γ) × A γ
  decode _A _Δ := {
    toFun f := ⟨↾fun δ => (f δ).1, ⟨fun δ => (f δ).2⟩⟩
    invFun e := ↾fun δ => ⟨e.1 δ, e.2.down δ⟩
    left_inv _ := rfl
    right_inv _ := rfl
  }
  natural _ _ _ := rfl

/-- The recovered generic element is the selected dependent component. -/
theorem generic_apply {Γ : Type u} (A : Γ → Type u) (γ : Γ) (a : A γ) :
    (representation.generic A).down ⟨γ,a⟩ = a := rfl

/-- The representation-derived pairing law supplies substitution of both
components of a dependent pair. -/
theorem pair_natural {Γ Δ Θ : Type u} (A : Γ → Type u) (f : Δ → Γ)
    (t : (δ : Δ) → A (f δ)) (g : Θ → Δ) :
    (↾g) ≫ representation.pair A (↾f) ⟨t⟩ =
      representation.pair A (↾(f ∘ g)) ⟨fun θ => t (g θ)⟩ :=
  representation.pair_natural A (↾f) ⟨t⟩ (↾g)

end SquareKit.TypeFamilyRepresentation
