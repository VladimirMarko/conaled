import SquareKit.Internal.PathTransport.TwoFamilySigmaLaws
import Examples.TwoFamilySigmaHigherNaturality

/-! Whole Sigma laws specialized to pairs with independent integer cells. -/
namespace Examples.TwoFamilySigmaLaws
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

example : TwoFamily.sigmaMap integerFamily laterFamily (𝟙 point) =
    StrictPseudofunctor.id pairFiber :=
  TwoFamily.sigmaMap_id integerFamily laterFamily point

example : TwoFamily.sigmaMap integerFamily laterFamily (arrow ≫ arrow) =
    (TwoFamily.sigmaMap integerFamily laterFamily arrow).comp
      (TwoFamily.sigmaMap integerFamily laterFamily arrow) :=
  TwoFamily.sigmaMap_comp integerFamily laterFamily arrow arrow

/-- Identity transport retains both independently selected integer witnesses. -/
theorem identity_retains_integers (m n : ℤ) :
    HEq ((TwoFamily.sigmaMap integerFamily laterFamily (𝟙 point)).map₂ (pairCell m n))
      (pairCell m n) :=
  TwoFamily.sigmaMap_cell_id_heq integerFamily laterFamily point (pairCell m n)

/-- Sequential transport retains both witnesses of the composite calculation. -/
example (m n : ℤ) :
    HEq ((TwoFamily.sigmaMap integerFamily laterFamily (arrow ≫ arrow)).map₂ (pairCell m n))
      ((TwoFamily.sigmaMap integerFamily laterFamily arrow).map₂
        ((TwoFamily.sigmaMap integerFamily laterFamily arrow).map₂ (pairCell m n))) :=
  TwoFamily.sigmaMap_cell_comp_heq integerFamily laterFamily arrow arrow (pairCell m n)

example : (TwoFamily.sigmaMap integerFamily laterFamily (𝟙 point)).map₂ (pairCell 0 1) ≠
    (TwoFamily.sigmaMap integerFamily laterFamily (𝟙 point)).map₂ (pairCell 0 0) := by
  intro h
  exact distinct_second_cells (eq_of_heq ((identity_retains_integers 0 1).symm.trans
    ((heq_of_eq h).trans (identity_retains_integers 0 0))))

example : TwoFamily.sigmaCell integerFamily laterFamily (𝟙 arrow) =
    StrictTwoTransformation.Trans.id (TwoFamily.sigmaMap integerFamily laterFamily arrow) :=
  TwoFamily.sigmaCell_id integerFamily laterFamily arrow

end Examples.TwoFamilySigmaLaws
