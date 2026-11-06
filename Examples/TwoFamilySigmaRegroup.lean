import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroup
import SquareKit.Internal.PathTransport.TwoFamilyCartesianFactorization
import Examples.TwoFamilySigmaLaws

namespace Examples.TwoFamilySigmaRegroup
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Cartesian pasting reconstructs both independently selected integer cells. -/
example (m n : ℤ) :
    TwoFamily.cartesianCellFactorization
      (TwoFamily.fiberRestriction integerFamily point laterFamily) (pairCell m n) =
        pairCell m n := TwoFamily.cartesianCellFactorization_eq _ _

/-- Reconstructing a cell retains the second integer observation. -/
example :
    TwoFamily.cartesianCellFactorization
      (TwoFamily.fiberRestriction integerFamily point laterFamily) (pairCell 0 1) ≠
    TwoFamily.cartesianCellFactorization
      (TwoFamily.fiberRestriction integerFamily point laterFamily) (pairCell 0 0) := by
  simpa only [TwoFamily.cartesianCellFactorization_eq] using distinct_second_cells

example (x : TwoFamily.Total (TwoFamily.sigmaFamily integerFamily laterFamily)) :
    (TwoFamily.sigmaRegroupObjectEquiv integerFamily laterFamily).symm
      ((TwoFamily.sigmaRegroupObjectEquiv integerFamily laterFamily) x) = x :=
  (TwoFamily.sigmaRegroupObjectEquiv integerFamily laterFamily).left_inv x

example {x y : TwoFamily.Total (TwoFamily.sigmaFamily integerFamily laterFamily)} (p : x ⟶ y) :
    (TwoFamily.sigmaRegroupArrowEquiv integerFamily laterFamily x y).symm
      ((TwoFamily.sigmaRegroupArrowEquiv integerFamily laterFamily x y) p) = p :=
  (TwoFamily.sigmaRegroupArrowEquiv integerFamily laterFamily x y).left_inv p
end Examples.TwoFamilySigmaRegroup
