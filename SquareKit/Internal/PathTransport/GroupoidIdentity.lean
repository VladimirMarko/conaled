import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
# Arrow-valued identity for constant groupoid families

The endpoints are functors, so their action on context arrows participates
in identity reindexing. The resulting set-valued family acts by endpoint
conjugation. This is one ingredient of a groupoid interpretation, not a
soundness theorem for the source fragment.

These declarations use Mathlib directly. No SynthLean declarations or trust
assumptions are imported or adapted.
-/
noncomputable section

namespace SquareKit.Internal.PathTransport.GroupoidIdentity

open CategoryTheory

universe u v uΓ vΓ uΔ vΔ

variable {C : Type u} [Groupoid.{v} C]
variable {Γ : Type uΓ} [Category.{vΓ} Γ]

/-- Identity between two sections of a constant groupoid family. Its elements
are arrows, even when a separate set-valued action forgets those arrows. -/
def family (x y : Γ ⥤ C) : Γ ⥤ Type v where
  obj γ := x.obj γ ⟶ y.obj γ
  map f := ↾fun p => inv (x.map f) ≫ p ≫ y.map f
  map_id γ := by
    ext p
    simp
  map_comp f g := by
    ext p
    simp [Category.assoc]

/-- Identity-family reindexing retains exactly the underlying arrow. -/
def basePathEquiv (x y : Γ ⥤ C) (γ : Γ) :
    (family x y).obj γ ≃ (x.obj γ ⟶ y.obj γ) := Equiv.refl _

/-- Reflexivity is the identity arrow. -/
def reflexivity (x : Γ ⥤ C) (γ : Γ) : (family x x).obj γ := 𝟙 _

@[simp] theorem basePathEquiv_reflexivity (x : Γ ⥤ C) (γ : Γ) :
    basePathEquiv x x γ (reflexivity x γ) = 𝟙 (x.obj γ) := rfl

/-- Semantic composition, independent of any source concatenation derivation.
The first arrow runs first: a set-valued action runs `q` after `p`. -/
def compose (x y z : Γ ⥤ C) (γ : Γ)
    (p : (family x y).obj γ) (q : (family y z).obj γ) :
    (family x z).obj γ := p ≫ q

@[simp] theorem basePathEquiv_compose (x y z : Γ ⥤ C) (γ : Γ)
    (p : (family x y).obj γ) (q : (family y z).obj γ) :
    basePathEquiv x z γ (compose x y z γ p q) =
      basePathEquiv x y γ p ≫ basePathEquiv y z γ q := rfl

/-- Reflexivity is a section of the identity family. -/
theorem reflexivity_natural (x : Γ ⥤ C) {γ δ : Γ} (f : γ ⟶ δ) :
    (family x x).map f (reflexivity x γ) = reflexivity x δ := by
  change inv (x.map f) ≫ 𝟙 _ ≫ x.map f = 𝟙 _
  simp

/-- Endpoint conjugation preserves composition. -/
theorem compose_natural (x y z : Γ ⥤ C) {γ δ : Γ} (f : γ ⟶ δ)
    (p : (family x y).obj γ) (q : (family y z).obj γ) :
    (family x z).map f (compose x y z γ p q) =
      compose x y z δ ((family x y).map f p) ((family y z).map f q) := by
  change inv (x.map f) ≫ (p ≫ q) ≫ z.map f =
    (inv (x.map f) ≫ p ≫ y.map f) ≫ (inv (y.map f) ≫ q ≫ z.map f)
  dsimp [family] at p q
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]

/-- Identity formation commutes strictly with substitution of the context. -/
theorem family_substitution {Δ : Type uΔ} [Category.{vΔ} Δ]
    (σ : Δ ⥤ Γ) (x y : Γ ⥤ C) :
    family (σ ⋙ x) (σ ⋙ y) = σ ⋙ family x y := rfl

/-- Reflexivity commutes strictly with substitution of the context. -/
theorem reflexivity_substitution {Δ : Type uΔ} [Category.{vΔ} Δ]
    (σ : Δ ⥤ Γ) (x : Γ ⥤ C) (δ : Δ) :
    reflexivity (σ ⋙ x) δ = reflexivity x (σ.obj δ) := rfl

/-- Composition commutes strictly with substitution of the context. -/
theorem compose_substitution {Δ : Type uΔ} [Category.{vΔ} Δ]
    (σ : Δ ⥤ Γ) (x y z : Γ ⥤ C) (δ : Δ)
    (p : (family (σ ⋙ x) (σ ⋙ y)).obj δ)
    (q : (family (σ ⋙ y) (σ ⋙ z)).obj δ) :
    compose (σ ⋙ x) (σ ⋙ y) (σ ⋙ z) δ p q =
      compose x y z (σ.obj δ) p q := rfl

end SquareKit.Internal.PathTransport.GroupoidIdentity
