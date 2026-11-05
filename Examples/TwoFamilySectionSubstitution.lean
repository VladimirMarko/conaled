import SquareKit.Internal.PathTransport.TwoFamilySectionLaws
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

set_option maxHeartbeats 1000000 in
/-- Identity substitution retains the chosen integer, including nonzero cells. -/
theorem substitution_retains_fiber (n : ℤ) :
    HEq ((substituted.lift.map₂ (TwoFamilyCoherence.cell n)).fiber)
      (Multiplicative.ofAdd n) := by
  exact TwoFamily.Section.reindex_cell_fiber _ TwoFamilySections.genericSection
    (StrictPseudofunctor.id _) (TwoFamilyCoherence.cell n)

/-- The identity law recovers the whole section, including its higher action. -/
theorem substitution_is_identity :
    TwoFamily.Section.cast (TwoFamily.reindex_id _) substituted =
      TwoFamilySections.genericSection :=
  TwoFamily.Section.reindex_id _ _

abbrev genericFamily := TwoFamily.reindex
  (TwoFamily.projectionHigher TwoFamilyCoherence.universal) TwoFamilyCoherence.universal
abbrev firstProjection := TwoFamily.projectionHigher genericFamily
abbrev nextProjection := TwoFamily.projectionHigher (TwoFamily.reindex firstProjection genericFamily)

/-- Two genuine context-extension projections compose as substitution on the whole generic section. -/
theorem nested_projection_substitution :
    TwoFamily.Section.cast (TwoFamily.reindex_comp genericFamily firstProjection nextProjection)
      ((TwoFamilySections.genericSection.reindex genericFamily firstProjection).reindex _ nextProjection) =
      TwoFamilySections.genericSection.reindex genericFamily (nextProjection.comp firstProjection) :=
  TwoFamily.Section.reindex_comp _ _ _ _

end Examples.TwoFamilySectionSubstitution
