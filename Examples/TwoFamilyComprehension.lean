import SquareKit.Internal.PathTransport.TwoFamilyComprehension
import Examples.TwoFamilySigmaProjection

/-! Reconstructing a substitution preserves its selected base and fiber cells. -/
namespace Examples.TwoFamilyComprehension
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyFiber
open TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

abbrev selectedFamily := sigmaFamily integerFamily laterFamily
abbrev selectedSubstitution := StrictPseudofunctor.id (Total selectedFamily)

def selectedSection := Section.cast
  (reindex_comp selectedFamily (projectionHigher selectedFamily) selectedSubstitution)
  ((variableSection selectedFamily).reindex _ selectedSubstitution)

theorem reconstructed_substitution :
    pairLift selectedFamily (selectedSubstitution.comp (projectionHigher selectedFamily))
      selectedSection = selectedSubstitution := pairLift_eta selectedFamily selectedSubstitution

open Examples.TwoFamilySigmaProjection

theorem retains_three_cells (k m n : ℤ) :
    HEq ((pairLift selectedFamily (selectedSubstitution.comp (projectionHigher selectedFamily))
      selectedSection).map₂ (totalCell k m n)) (totalCell k m n) := by
  rw [reconstructed_substitution]
  rfl

example : (pairLift selectedFamily (selectedSubstitution.comp (projectionHigher selectedFamily))
    selectedSection).map₂ (totalCell 0 0 1) ≠
    (pairLift selectedFamily (selectedSubstitution.comp (projectionHigher selectedFamily))
    selectedSection).map₂ (totalCell 0 0 0) := by
  intro h
  have he := eq_of_heq ((retains_three_cells 0 0 1).symm.trans
    ((heq_of_eq h).trans (retains_three_cells 0 0 0)))
  have hh := congr_arg_heq (fun α => α.fiber.fiber) he
  have hi : Multiplicative.ofAdd (1:ℤ) = Multiplicative.ofAdd 0 := eq_of_heq hh
  exact Int.one_ne_zero (congrArg Multiplicative.toAdd hi)
end Examples.TwoFamilyComprehension
