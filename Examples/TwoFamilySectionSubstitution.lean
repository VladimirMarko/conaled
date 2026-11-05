import SquareKit.Internal.PathTransport.TwoFamilySectionSubstitution
import Examples.TwoFamilySections

/-! Factoring and substituting sections retains the original integer fiber cells. -/
namespace Examples.TwoFamilySectionSubstitution
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev factored := TwoFamily.sectionOfLift TwoFamilyCoherence.universal
  (StrictPseudofunctor.id (TwoFamily.Total TwoFamilyCoherence.universal))

theorem factor_retains_fiber (n : ℤ) :
    (factored.lift.map₂ (TwoFamilyCoherence.cell n)).fiber = Multiplicative.ofAdd n := rfl

abbrev substituted := TwoFamily.Section.reindex _ TwoFamilySections.genericSection
  (StrictPseudofunctor.id _)

theorem substitution_projects :
    substituted.lift.comp (TwoFamily.projectionHigher _) = StrictPseudofunctor.id _ :=
  substituted.over

end Examples.TwoFamilySectionSubstitution
