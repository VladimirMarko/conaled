import Examples.CubicalUnivalenceTransport
import SquareKit.Internal.Cubical.NativeUnivalenceMap

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalUnivalenceTransport
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf

/-- The Boolean loop also acts through the universal decoding family at the
larger universe level. Its actual transport has native contractible fibers. -/
noncomputable def booleanUniversalTransportEquivalence :
    HomotopyEquivalence (SmallUniverse.NativeUnivalence.pathToMap booleanUniverseLoop) :=
  SmallUniverse.NativeUnivalence.pathToEquivalence booleanUniverseLoop

/-- The generic native map produces a section of the internal equivalence
family, not merely a host pair standing in for that family. -/
noncomputable def booleanInternalEquivalence :=
  Term.map (SmallUniverse.NativeUnivalence.pathToEquiv
    (CubicalGlue.constantLocal terminal Bool).code (CubicalGlue.constantLocal terminal Bool).code)
    booleanUniverseLoop

end Examples.CubicalUnivalenceTransport
