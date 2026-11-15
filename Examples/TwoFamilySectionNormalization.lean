import SquareKit.Internal.PathTransport.TwoFamilySectionNormalization
import Examples.TwoFamilySigmaProjection

/-! Normalization retains the selected genuine pair cell in a generic section. -/
namespace Examples.TwoFamilySectionNormalization
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyFiber
open Examples.TwoFamilySigmaProjection
open TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

abbrev selectedFamily := sigmaFamily integerFamily laterFamily
abbrev selectedSection := variableSection selectedFamily
abbrev displayedFamily := reindex (projectionHigher selectedFamily) selectedFamily

theorem retains_pair_cell (k m n : ℤ) :
    HEq (((selectedSection.normalized displayedFamily).lift.map₂ (totalCell k m n)).fiber)
      (pairCell m n) := by
  rw [Section.normalized_eq]
  rfl

example (k m n : ℤ) :
    ((selectedSection.normalized displayedFamily).lift.map₂ (totalCell k m n)).base =
      totalCell k m n := selectedSection.normalized_cell_base displayedFamily _

example : ¬ HEq (((selectedSection.normalized displayedFamily).lift.map₂ (totalCell 0 0 1)).fiber)
    (pairCell 0 0) := by
  intro h
  exact distinct_second_cells (eq_of_heq ((retains_pair_cell 0 0 1).symm.trans h))
end Examples.TwoFamilySectionNormalization
