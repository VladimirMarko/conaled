import Examples.CubicalUniversalDecode
import SquareKit.Internal.Cubical.NativeUnivalenceUa
import SquareKit.Internal.Cubical.UnivalenceEliminationSubstitution
import Examples.CubicalUnivalenceSubstitution

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalNativeUnivalenceUa
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalGlue Examples.CubicalUnivalenceTransport
open SmallUniverse.NativeUnivalence

/-- Apply the generic native reverse operation to the actual universal Boolean transport equivalence. -/
noncomputable def recoveredBooleanLoop :=
  ua (constantLocal terminal Bool).code (constantLocal terminal Bool).code
    (pathToMap booleanUniverseLoop) booleanUniversalTransportEquivalence

theorem recoveredBooleanLine_zero :
    (uaLine (constantLocal terminal Bool).code (constantLocal terminal Bool).code
      (pathToMap booleanUniverseLoop) booleanUniversalTransportEquivalence).reindex
        (endpointSub (raisedContext terminal) false) =
    SmallUniverse.term (constantLocal terminal Bool).code :=
  uaLine_zero _ _ _ _

theorem recoveredBooleanLine_one :
    (uaLine (constantLocal terminal Bool).code (constantLocal terminal Bool).code
      (pathToMap booleanUniverseLoop) booleanUniversalTransportEquivalence).reindex
        (endpointSub (raisedContext terminal) true) =
    SmallUniverse.term (constantLocal terminal Bool).code :=
  uaLine_one _ _ _ _

open Examples.CubicalUnivalenceSubstitution in
/-- The actual Boolean Glue eliminator commutes with pulling the complete chosen loop to an interval. -/
theorem booleanUnglue_interval_substitution :
    Functor.whiskerLeft (liftSub (interval terminal) (projection (interval terminal))).mapElements
      (Univalence.unglueLine boolCode boolCode flip flipEquivalence) =
    eqToHom (congrArg decode (Univalence.uaCode_reindex boolCode boolCode
      (projection (interval terminal)) flip flipEquivalence)) ≫
      Univalence.unglueLine
        (raisedSub (projection (interval terminal)) ≫ boolCode)
        (raisedSub (projection (interval terminal)) ≫ boolCode)
        (Functor.whiskerLeft (projection (interval terminal)).mapElements flip)
        (flipEquivalence.reindex (projection (interval terminal))) :=
  Univalence.unglueLine_reindex _ _ _ _ _

end Examples.CubicalNativeUnivalenceUa
