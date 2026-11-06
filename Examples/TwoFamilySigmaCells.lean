import SquareKit.Internal.PathTransport.TwoFamilySigmaCells
import Examples.TwoFamilySigmaAction

namespace Examples.TwoFamilySigmaCells
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Canonical comparison cells have equality fibers even for nonzero base cells. -/
example (k : ℤ) : TwoFamily.EqualityFiber integerFamily
    (TwoFamily.cartesianComparisonCell integerFamily
      (show arrow ⟶ arrow from Multiplicative.ofAdd k) point) :=
  TwoFamily.cartesianComparisonCell_equalityFiber integerFamily _ _

/-- Arbitrary genuine fiber cells are not being restricted to equality fibers. -/
theorem nonzero_fiber_not_equality : ¬ TwoFamily.EqualityFiber integerFamily
    ((TwoFamily.fiberInclusion integerFamily point).map₂
      (show arrow ⟶ arrow from Multiplicative.ofAdd (1 : ℤ))) := by
  rintro ⟨h, hh⟩
  have hi := TwoFamily.fiberInclusionCell_fiber_heq integerFamily point
    (show arrow ⟶ arrow from Multiplicative.ofAdd (1 : ℤ))
  have hz : Multiplicative.ofAdd (0 : ℤ) = Multiplicative.ofAdd 1 :=
    eq_of_heq ((heq_of_eq hh).symm.trans hi)
  exact Int.zero_ne_one (congrArg Multiplicative.toAdd hz)

/-- Base-cell components act on actual dependent pairs for every integer base cell. -/
example (k : ℤ) :
    (TwoFamily.sigmaMap integerFamily laterFamily arrow).obj pairPoint ⟶
      (TwoFamily.sigmaMap integerFamily laterFamily arrow).obj pairPoint :=
  TwoFamily.sigmaCellComponent integerFamily laterFamily
    (show arrow ⟶ arrow from Multiplicative.ofAdd k) pairPoint

end Examples.TwoFamilySigmaCells
