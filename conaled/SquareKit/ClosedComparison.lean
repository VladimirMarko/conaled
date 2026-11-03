import Mathlib.CategoryTheory.Monoidal.Closed.Functor

/-! Experimental operation comparison for Cartesian closed functors, using
Mathlib's canonical exponential comparison (the mate of product comparison). -/
noncomputable section
namespace SquareKit.ClosedComparison
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
universe u u' v
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
variable [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
variable [MonoidalClosed C] [MonoidalClosed D]
variable (F : C ⥤ D) [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) F]

/-- Currying commutes with the canonical exponential comparison. -/
theorem curry_compare {A X B : C} (f : A ⊗ X ⟶ B) :
    F.map (curry f) ≫ (expComparison F A).app B =
      curry (inv (prodComparison F A X) ≫ F.map f) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_expComparison, uncurry_curry]
  rw [← Category.assoc, ← prodComparison_inv_natural_whiskerLeft]
  rw [Category.assoc, ← F.map_comp, ← uncurry_eq, uncurry_curry]

end SquareKit.ClosedComparison
