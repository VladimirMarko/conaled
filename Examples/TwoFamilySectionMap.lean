import SquareKit.Internal.PathTransport.TwoFamilySectionMap
import Examples.TwoFamilySections

/-! Coherent family maps preserve the generic section's genuine integer cells. -/
namespace Examples.TwoFamilySectionMap
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
abbrev mapped := TwoFamily.Section.map
  (Pseudofunctor.StrongTrans.id _)
  TwoFamilySections.genericSection

theorem mapped_retains_fiber (n : ℤ) :
    (mapped.lift.map₂ (TwoFamilyCoherence.cell n)).fiber = Multiplicative.ofAdd n := by
  dsimp [mapped, TwoFamily.Section.map, TwoFamily.StrongMap.toHigher,
    TwoFamily.StrongMap.map₂, TwoFamilyCoherence.cell, TwoFamilySections.genericSection,
    TwoFamily.variableSection, TwoFamily.variableLift]
  simp only [Category.comp_id]
  rfl
end Examples.TwoFamilySectionMap
