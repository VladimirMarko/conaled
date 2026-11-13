import Examples.CubicalUniversalDecode
import SquareKit.Internal.Cubical.UniverseRaising

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalUnivalenceTransport
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalGlue

/-- Lowering retains a genuine native fiber contraction for the actual
universal-decoding transport of the Boolean universe loop. -/
noncomputable def loweredBooleanTransportEquivalence :
    HomotopyEquivalence (SmallUniverse.lowerChartMap
      (constantLocal terminal Bool).code (constantLocal terminal Bool).code (𝟙 _)
      (SmallUniverse.NativeUnivalence.pathToMap booleanUniverseLoop)) :=
  SmallUniverse.lowerChartEquivalence _ _ (𝟙 _) _ booleanUniversalTransportEquivalence

end Examples.CubicalUnivalenceTransport
