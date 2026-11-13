import Examples.CubicalUnivalenceTransport
import SquareKit.Internal.Cubical.UniversePathEquivalence

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalUnivalenceTransport
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf

/-- The Boolean loop also acts through the universal decoding family at the
larger universe level. Its actual transport has native contractible fibers. -/
noncomputable def booleanUniversalTransportEquivalence :
    HomotopyEquivalence (SmallUniverse.NativeUnivalence.pathToMap booleanUniverseLoop) :=
  SmallUniverse.NativeUnivalence.pathToEquivalence booleanUniverseLoop

end Examples.CubicalUnivalenceTransport
