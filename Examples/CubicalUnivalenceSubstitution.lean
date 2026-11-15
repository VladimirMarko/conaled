import Examples.CubicalUnivalenceTransport
import SquareKit.Internal.Cubical.UnivalenceSubstitution

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalUnivalenceSubstitution
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalGlue Examples.CubicalUnivalenceTransport

abbrev boolCode := (constantLocal terminal Bool).code
abbrev flip := (codeIso booleanTransposition).hom
abbrev flipEquivalence := HomotopyEquivalence.ofIso (codeIso booleanTransposition)

/-- The nonidentity Boolean loop retains its entire chosen code when pulled to an interval context. -/
theorem booleanLoop_interval_substitution :
    raisedSub (liftSub (interval terminal) (projection (interval terminal))) ≫
      Univalence.uaCode boolCode boolCode flip flipEquivalence =
    Univalence.uaCode
      (raisedSub (projection (interval terminal)) ≫ boolCode)
      (raisedSub (projection (interval terminal)) ≫ boolCode)
      (Functor.whiskerLeft (projection (interval terminal)).mapElements flip)
      (flipEquivalence.reindex (projection (interval terminal))) :=
  Univalence.uaCode_reindex boolCode boolCode (projection (interval terminal)) flip flipEquivalence

end Examples.CubicalUnivalenceSubstitution
