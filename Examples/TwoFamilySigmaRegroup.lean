import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroupCells
import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroupMapLaws
import SquareKit.Internal.PathTransport.TwoFamilyCartesianFactorization
import Examples.TwoFamilySigmaProjection

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

open Examples.TwoFamilySigmaProjection

/-- Reassociation retains the selected second fiber cell, as well as the two base cells. -/
theorem regroup_retains_second (k m n : ℤ) :
    HEq (TwoFamily.sigmaRegroupCell integerFamily laterFamily (totalCell k m n)).fiber
      (Multiplicative.ofAdd n) := TwoFamily.sigmaRegroupCell_fiber_heq _ _ _

example (k m n : ℤ) :
    ((TwoFamily.sigmaRegroupCell integerFamily laterFamily (totalCell k m n)).base.base,
      (TwoFamily.sigmaRegroupCell integerFamily laterFamily (totalCell k m n)).base.fiber) =
        (Multiplicative.ofAdd k, Multiplicative.ofAdd m) := rfl

example : TwoFamily.sigmaRegroupCell integerFamily laterFamily (totalCell 0 0 1) ≠
    TwoFamily.sigmaRegroupCell integerFamily laterFamily (totalCell 0 0 0) := by
  intro h
  have hh := congr_arg_heq (fun α => α.fiber) h
  have hi : Multiplicative.ofAdd (1:ℤ) = Multiplicative.ofAdd 0 :=
    eq_of_heq ((regroup_retains_second 0 0 1).symm.trans (hh.trans (regroup_retains_second 0 0 0)))
  exact Int.one_ne_zero (congrArg Multiplicative.toAdd hi)

example : TwoFamily.sigmaRegroupMap integerFamily laterFamily (totalArrow ≫ totalArrow) =
    TwoFamily.sigmaRegroupMap integerFamily laterFamily totalArrow ≫
      TwoFamily.sigmaRegroupMap integerFamily laterFamily totalArrow :=
  TwoFamily.sigmaRegroupMap_comp _ _ _ _
end Examples.TwoFamilySigmaRegroup
