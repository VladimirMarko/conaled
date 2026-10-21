import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Yoneda

/-!
# Based paths and set-valued dependent elimination

The objects of `Space x` are pairs of an endpoint and an arrow from `x`.
Their morphisms are commuting triangles, not equalities of endpoints.
`eliminate` constructs a section of any set-valued family on this space.

The construction works in any category; over a groupoid its path category
is also a groupoid.

This is a semantic ingredient only. It does not interpret source J for
arbitrary groupoid-valued motives or generalized dependent telescopes.
-/
namespace SquareKit.Internal.PathTransport.BasedPath

open CategoryTheory Opposite

universe u v w
variable {C : Type u} [Category.{v} C]

/-- The category of paths with fixed source. It inherits a groupoid structure
when the base is a groupoid. -/
abbrev Space (x : C) := (coyoneda.obj (op x)).Elements

/-- The reflexive based path. -/
def root (x : C) : Space x := .mk (𝟙 x)

/-- The canonical triangle from reflexivity to a based path. -/
def fromRoot {x : C} (p : Space x) : root x ⟶ p :=
  Functor.Elements.homMk p.val (by
    change 𝟙 x ≫ p.val = p.val
    exact Category.id_comp _)

@[simp] theorem fromRoot_root (x : C) : fromRoot (root x) = 𝟙 (root x) := by
  apply Functor.Elements.hom_ext
  rfl

/-- Every triangle with fixed source preserves the canonical path. -/
theorem fromRoot_natural {x : C} {p q : Space x} (f : p ⟶ q) :
    fromRoot p ≫ f = fromRoot q := by
  apply Functor.Elements.hom_ext
  exact f.map_val

/-- Semantic dependent elimination for a set-valued motive. -/
def eliminate {x : C} (D : Space x ⥤ Type w) (d : D.obj (root x))
    (p : Space x) : D.obj p := D.map (fromRoot p) d

/-- Reflexive computation is an equation of elements of the set fiber. -/
@[simp] theorem eliminate_root {x : C} (D : Space x ⥤ Type w)
    (d : D.obj (root x)) : eliminate D d (root x) = d := by
  simp [eliminate]

/-- Elimination produces a section, including its action on path triangles. -/
theorem eliminate_natural {x : C} (D : Space x ⥤ Type w)
    (d : D.obj (root x)) {p q : Space x} (f : p ⟶ q) :
    D.map f (eliminate D d p) = eliminate D d q := by
  rw [eliminate, ← ConcreteCategory.comp_apply, ← D.map_comp, fromRoot_natural]
  rfl

/-- The set-valued section is determined by its reflexive component. -/
theorem eliminate_unique {x : C} (D : Space x ⥤ Type w)
    (s : ∀ p, D.obj p)
    (natural : ∀ {p q} (f : p ⟶ q), D.map f (s p) = s q)
    (p : Space x) : eliminate D (s (root x)) p = s p :=
  natural (fromRoot p)

end SquareKit.Internal.PathTransport.BasedPath
