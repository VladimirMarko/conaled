import SquareKit.Internal.PathTransport.TwoFamilyHigherReindex
import Examples.TwoFamilyCoherence

/-!
# Higher substitution retains a non-discrete fiber

Reindex the universal family along its own total projection. The resulting nested
extension has integer-valued fiber cells, and higher substitution retains them.
-/
namespace Examples.TwoFamilyHigherReindex
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev universal := TwoFamilyCoherence.universal
abbrev substitution := TwoFamily.projectionHigher universal
abbrev family := TwoFamily.reindex substitution universal

def point : TwoFamily.Total family :=
  ⟨TwoFamilyCoherence.point, TwoFamilyCoherence.point.fiber⟩

def arrow : TwoFamily.Hom family point point := TwoFamily.identity family point

def cell (n : ℤ) : arrow ⟶ arrow :=
  TwoGroupoidHom.cell (𝟙 arrow.base) (Multiplicative.ofAdd n)

abbrev higher := TwoFamily.reindexHigher universal substitution

/-- Nonzero fiber information survives a substitution from a total context. -/
theorem retains_fiber (n : ℤ) : (higher.map₂ (cell n)).fiber = Multiplicative.ofAdd n := rfl

theorem retains_distinction : higher.map₂ (cell 1) ≠ higher.map₂ (cell 0) := by
  intro h
  have := congrArg (fun c : higher.map arrow ⟶ higher.map arrow =>
    Multiplicative.toAdd c.fiber) h
  exact Int.one_ne_zero this

/-- Vertical composition uses the constructed higher functor. -/
theorem vertical : higher.map₂ (cell 1 ≫ cell 2) =
    higher.map₂ (cell 1) ≫ higher.map₂ (cell 2) := higher.map₂_comp _ _

theorem left_retains_one :
    (higher.map₂ (TwoFamily.whiskerLeft family arrow (cell 1))).fiber =
      Multiplicative.ofAdd (1 : ℤ) := rfl

theorem right_retains_one :
    (higher.map₂ (TwoFamily.whiskerRight family (cell 1) arrow)).fiber =
      Multiplicative.ofAdd (1 : ℤ) := rfl

/-- Projection commutes as an equality of strict pseudofunctors. -/
theorem projection :
    higher.comp (TwoFamily.projectionHigher universal) =
      (TwoFamily.projectionHigher family).comp substitution :=
  TwoFamily.reindexHigher_projection universal substitution

end Examples.TwoFamilyHigherReindex
