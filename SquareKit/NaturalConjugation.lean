import Mathlib.CategoryTheory.NatIso

/-! Naturality retains the endpoint comparisons when transporting an arrow. -/
namespace SquareKit
open CategoryTheory
universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {F G : C ⥤ D} (β : F ⟶ G)

/-- Conjugating the mapped arrow by the selected endpoint comparisons recovers
its image under the comparison target. Only the first component needs inversion. -/
theorem natural_conjugation {x y : C} [IsIso (β.app x)] (h : x ⟶ y) :
    inv (β.app x) ≫ F.map h ≫ β.app y = G.map h := by
  rw [β.naturality]
  simp

end SquareKit
