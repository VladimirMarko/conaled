import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Whiskering

/-! Bounded routes for set-valued families over categories. A base functor
retains the action on arrows; a natural fibre map supplies transport
preservation. This does not interpret arbitrary changes of source syntax. -/
namespace SquareKit.GroupoidTransport
open CategoryTheory CategoryTheory.Functor
universe uC uD uE uH v
variable {C : Type uC} {D : Type uD} {E : Type uE} {H : Type uH} [Category C] [Category D] [Category E] [Category H]

structure Route (B : C ⥤ Type v) (A : D ⥤ Type v) where
  base : C ⥤ D
  fiber : B ⟶ base ⋙ A

namespace Route
variable {B : C ⥤ Type v} {A : D ⥤ Type v} {K : E ⥤ Type v}

def identity (B : C ⥤ Type v) : Route B B := ⟨𝟭 C, 𝟙 B⟩

def comp (r : Route B A) (s : Route A K) : Route B K :=
  ⟨r.base ⋙ s.base, r.fiber ≫ whiskerLeft r.base s.fiber⟩

/-- Naturality is precisely the transport comparison, not an extra premise. -/
theorem transport (r : Route B A) {x y : C} (p : x ⟶ y) (b : B.obj x) :
    r.fiber.app y (B.map p b) = A.map (r.base.map p) (r.fiber.app x b) :=
  ConcreteCategory.congr_hom (r.fiber.naturality p) b

@[simp] theorem comp_arrow (r : Route B A) (s : Route A K) {x y : C} (p : x ⟶ y) :
    (r.comp s).base.map p = s.base.map (r.base.map p) := rfl

@[simp] theorem comp_fiber (r : Route B A) (s : Route A K) (x : C) (b : B.obj x) :
    (r.comp s).fiber.app x b = s.fiber.app (r.base.obj x) (r.fiber.app x b) := rfl

/-- Functorial transport preserves path composition after a route. -/
theorem transport_concat (r : Route B A) {x y z : C}
    (p : x ⟶ y) (q : y ⟶ z) (b : B.obj x) :
    r.fiber.app z (B.map (p ≫ q) b) =
      A.map (r.base.map q) (A.map (r.base.map p) (r.fiber.app x b)) := by
  rw [r.transport, r.base.map_comp, A.map_comp]
  rfl

/-- Context substitution precomposes both the family and the base route. -/
def reindex (r : Route B A) (σ : H ⥤ C) : Route (σ ⋙ B) A :=
  ⟨σ ⋙ r.base, whiskerLeft σ r.fiber⟩

theorem substitution_arrow (r : Route B A) (σ : H ⥤ C) {x y : H} (p : x ⟶ y) :
    (r.reindex σ).base.map p = r.base.map (σ.map p) := rfl

theorem substitution_transport (r : Route B A) (σ : H ⥤ C)
    {x y : H} (p : x ⟶ y) (b : B.obj (σ.obj x)) :
    (r.reindex σ).fiber.app y ((σ ⋙ B).map p b) =
      A.map (r.base.map (σ.map p)) (r.fiber.app (σ.obj x) b) :=
  (r.reindex σ).transport p b

theorem reindex_comp (r : Route B A) (s : Route A K) (σ : H ⥤ C) :
    (r.comp s).reindex σ = (r.reindex σ).comp s := rfl

/-- Route composition and its identity are strict for these chosen functors. -/
theorem identity_comp (r : Route B A) : (identity B).comp r = r := by cases r; rfl
theorem comp_identity (r : Route B A) : r.comp (identity A) = r := by cases r; rfl

theorem comp_assoc {L : H ⥤ Type v} (r : Route B A) (s : Route A K) (t : Route K L) :
    (r.comp s).comp t = r.comp (s.comp t) := rfl
end Route
end SquareKit.GroupoidTransport
