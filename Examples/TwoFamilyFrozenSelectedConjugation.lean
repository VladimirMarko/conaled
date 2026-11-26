import Examples.TwoFamilyFrozenOrdinaryAction
import Examples.TwoFamilySelectedConjugation
namespace Examples.TwoFamilyFrozenOrdinaryAction
open CategoryTheory Bicategory SquareKit.Internal.PathTransport HigherInterpretation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 3000
noncomputable section
theorem selected_conjugation (k : ℤ) :
    type_of% (TwoFamilySelectedOrdinaryAction.selectedConjugated_eq
      Examples.TwoFamilyModelData.integerContext Examples.TwoFamilyModelData.integerContext
      paths (Examples.TwoFamilyFrozenPoint.assignedPoint k)) :=
  TwoFamilySelectedOrdinaryAction.selectedConjugated_eq
    Examples.TwoFamilyModelData.integerContext Examples.TwoFamilyModelData.integerContext
    paths (Examples.TwoFamilyFrozenPoint.assignedPoint k)
end
end Examples.TwoFamilyFrozenOrdinaryAction
