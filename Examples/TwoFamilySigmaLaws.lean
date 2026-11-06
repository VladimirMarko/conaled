import SquareKit.Internal.PathTransport.TwoFamilySigmaFamily
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

/-- Two selected integer cells compose through the constructed Sigma transformation. -/
example (m n : ℤ) :
    TwoFamily.sigmaCell integerFamily laterFamily
      ((show arrow ⟶ arrow from Multiplicative.ofAdd m) ≫ Multiplicative.ofAdd n) =
    StrictTwoTransformation.Trans.comp
      (TwoFamily.sigmaCell integerFamily laterFamily
        (show arrow ⟶ arrow from Multiplicative.ofAdd m))
      (TwoFamily.sigmaCell integerFamily laterFamily
        (show arrow ⟶ arrow from Multiplicative.ofAdd n)) :=
  TwoFamily.sigmaCell_comp integerFamily laterFamily _ _


/-- The assembled family transports the selected genuine pair cell. -/
example (m n : ℤ) :
    HEq (((TwoFamily.sigmaFamily integerFamily laterFamily).map (𝟙 point)).map₂ (pairCell m n))
      (pairCell m n) := identity_retains_integers m n

example (m : ℤ) :
    HEq (TwoFamily.sigmaCellComponent integerFamily laterFamily
      (arrow ◁ (show arrow ⟶ arrow from Multiplicative.ofAdd m)) pairPoint)
      (TwoFamily.sigmaCellComponent integerFamily laterFamily
        (show arrow ⟶ arrow from Multiplicative.ofAdd m)
        ((TwoFamily.sigmaMap integerFamily laterFamily arrow).obj pairPoint)) :=
  TwoFamily.sigmaCellComponent_left_heq integerFamily laterFamily arrow _ pairPoint

end Examples.TwoFamilySigmaLaws
