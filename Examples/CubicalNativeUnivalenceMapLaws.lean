import Examples.CubicalUniversalDecode
import SquareKit.Internal.Cubical.NativeUnivalenceMapLaws

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalNativeUnivalenceMapLaws
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalGlue Examples.CubicalUnivalenceTransport
open SmallUniverse.NativeUnivalence

/-- Adding an interval parameter preserves the entire Boolean transport equivalence,
including its selected fiber contractions. -/
theorem booleanTransport_interval :
    HEq (booleanUniversalTransportEquivalence.reindex
      (projection (interval (raisedContext terminal))))
      (pathToEquivalence (reindexPath booleanUniverseLoop
        (projection (interval (raisedContext terminal))))) :=
  pathToEquivalence_reindex booleanUniverseLoop _

/-- Evaluating the generic native construction recovers the full chosen Boolean data. -/
theorem booleanGeneric_complete :
    (⟨Functor.whiskerLeft
        (pair (A := paths (constantLocal terminal Bool).code (constantLocal terminal Bool).code)
          (𝟙 (raisedContext terminal)) booleanUniverseLoop).mapElements
        (pathToMap (genericPath (constantLocal terminal Bool).code (constantLocal terminal Bool).code)),
      (pathToEquivalence (genericPath (constantLocal terminal Bool).code
        (constantLocal terminal Bool).code)).reindex
        (pair (A := paths (constantLocal terminal Bool).code (constantLocal terminal Bool).code)
          (𝟙 (raisedContext terminal)) booleanUniverseLoop)⟩ :
      Σ f : SmallUniverse.liftedDecode (constantLocal terminal Bool).code ⟶
        SmallUniverse.liftedDecode (constantLocal terminal Bool).code, HomotopyEquivalence f) =
      ⟨pathToMap booleanUniverseLoop, booleanUniversalTransportEquivalence⟩ :=
  pathEquivalence_generic booleanUniverseLoop

/-- The chosen Boolean Glue path is stable under an additional interval parameter. -/
theorem booleanUa_interval :
    reindexPath (ua (constantLocal terminal Bool).code (constantLocal terminal Bool).code
      (pathToMap booleanUniverseLoop) booleanUniversalTransportEquivalence)
        (projection (interval (raisedContext terminal))) =
      ua (projection (interval (raisedContext terminal)) ≫ (constantLocal terminal Bool).code)
        (projection (interval (raisedContext terminal)) ≫ (constantLocal terminal Bool).code)
        (Functor.whiskerLeft (projection (interval (raisedContext terminal))).mapElements
          (pathToMap booleanUniverseLoop))
        (booleanUniversalTransportEquivalence.reindex
          (projection (interval (raisedContext terminal)))) :=
  ua_reindex _ _ _ _ _

end Examples.CubicalNativeUnivalenceMapLaws
