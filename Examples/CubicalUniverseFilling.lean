import Examples.CubicalGlue
import SquareKit.Internal.Cubical.UniverseKan

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalGlue
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf

/-- A native open universe box carries the actual Boolean code on its whole tube. -/
def booleanUniverseLine : Term (SmallUniverse.family
    (total (interval (raisedContext terminal.{0})))) :=
  SmallUniverse.term (projection (interval (raisedContext terminal.{0})) ≫ (constantLocal terminal Bool).code)

def booleanUniverseBox : OpenBox
    (SmallUniverse.family (total (interval (raisedContext terminal.{0}))))
    (Cofibration.top (raisedContext terminal.{0})) where
  tube := PartialSection.ofTerm _ booleanUniverseLine
  base := SmallUniverse.term (constantLocal terminal Bool).code
  boundary _ _ := rfl

theorem boolean_universe_fills :
    booleanUniverseBox.Fills (SmallUniverse.fillTerm booleanUniverseBox) :=
  SmallUniverse.fillTerm_fills booleanUniverseBox

/-- This exercises the constructed large-universe filler, including exact
recovery of the Boolean code and its chosen filling on the entire face. -/
theorem boolean_universe_whole_tube :
    SmallUniverse.fillTerm booleanUniverseBox = booleanUniverseLine := by
  apply Term.ext
  intro x
  exact SmallUniverse.fillTerm_tube booleanUniverseBox x rfl

end Examples.CubicalGlue
