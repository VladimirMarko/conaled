import SquareKit.Internal.Cubical.Substitution
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! Localization at a generalized element uses a category determined only by its
underlying cube. Context substitution preserves the resulting diagrams by equality. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

/-- Restrict a generalized element along every arrow out of its cube. -/
def localize (Γ : Context.{u}) (x : Γ.Elements) : Under x.obj ⥤ Γ.Elements where
  obj f := Γ.elementsMk f.right (Γ.map f.hom x.val)
  map {f g} h := Functor.Elements.homMk h.right (by
    rw [← Functor.map_comp_apply, Under.w h])
  map_id _ := rfl
  map_comp _ _ := rfl

theorem elementHom_hext {Γ : Context.{u}} {x x' y y' : Γ.Elements}
    (hx : x = x') (hy : y = y') (f : x ⟶ y) (g : x' ⟶ y')
    (h : HEq f.hom g.hom) : HEq f g := by
  subst x'
  subst y'
  apply heq_of_eq
  apply Functor.Elements.hom_ext
  exact eq_of_heq h

/-- The localized diagrams are equal, not merely naturally isomorphic. -/
theorem localize_substitution {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    localize Δ x ⋙ σ.mapElements = localize Γ (σ.mapElements.obj x) := by
  have ho : ∀ f : Under x.obj,
      (localize Δ x ⋙ σ.mapElements).obj f = (localize Γ (σ.mapElements.obj x)).obj f := by
    intro f
    exact congrArg (Γ.elementsMk f.right) (σ.naturality_apply f.hom x.val)
  apply Functor.hext ho
  intro f g h
  exact elementHom_hext (ho f) (ho g) _ _ (HEq.rfl)

/-- Restriction of the base element is also equality of localized diagrams. -/
theorem localize_restriction {Γ : Context.{u}} {x y : Γ.Elements} (f : x ⟶ y) :
    Under.map f.hom ⋙ localize Γ x = localize Γ y := by
  have ho : ∀ g : Under y.obj,
      (Under.map f.hom ⋙ localize Γ x).obj g = (localize Γ y).obj g := by
    intro g
    apply congrArg (Γ.elementsMk g.right)
    exact (Γ.map_comp_apply f.hom g.hom x.val).trans (congrArg (Γ.map g.hom) f.map_val)
  apply Functor.hext ho
  intro g h k
  exact elementHom_hext (ho g) (ho h) _ _ (HEq.rfl)

/-- Forgetting an arrow of elements and then lifting it recovers its target. -/
theorem localize_forget {Γ : Context.{u}} (x : Γ.Elements) :
    Under.post (Functor.Elements.π Γ) ⋙ localize Γ x = Under.forget x := by
  have ho : ∀ f : Under x,
      (Under.post (Functor.Elements.π Γ) ⋙ localize Γ x).obj f =
        (Under.forget x).obj f := by
    intro f
    exact congrArg (Γ.elementsMk f.right.obj) f.hom.map_val
  apply Functor.hext ho
  intro f g h
  exact elementHom_hext (ho f) (ho g) _ _ (HEq.rfl)

/-- Localization of a family commutes with substitution by equality. -/
theorem localFamily_substitution {Γ Δ : Context.{u}} (A : Family Γ)
    (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    localize Δ x ⋙ reindex A σ = localize Γ (σ.mapElements.obj x) ⋙ A := by
  change (localize Δ x ⋙ σ.mapElements) ⋙ A = _
  rw [localize_substitution]

end SquareKit.Cubical.Presheaf
