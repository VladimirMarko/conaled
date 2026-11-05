import SquareKit.Internal.PathTransport.TwoFamilySections
import Examples.TwoFamilyCoherence

/-! The generic section retains genuine, distinct fiber 2-cells. -/
namespace Examples.TwoFamilySections
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev genericSection := TwoFamily.variableSection TwoFamilyCoherence.universal

theorem generic_retains_fiber (n : ℤ) :
    (genericSection.lift.map₂ (TwoFamilyCoherence.cell n)).fiber = Multiplicative.ofAdd n := rfl

theorem generic_distinguishes_cells :
    genericSection.lift.map₂ (TwoFamilyCoherence.cell 1) ≠
      genericSection.lift.map₂ (TwoFamilyCoherence.cell 0) := by
  intro h
  have hn := congrArg (fun α => Multiplicative.toAdd α.fiber) h
  exact Int.one_ne_zero hn

end Examples.TwoFamilySections
