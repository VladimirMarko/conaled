import Examples.CubicalNativeUnivalenceUa
import SquareKit.Internal.Cubical.NativeUnivalenceSectionBeta

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalNativeUnivalenceSectionBeta
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalGlue Examples.CubicalUnivalenceTransport
open SmallUniverse.NativeUnivalence

/-- The native Boolean result contains exactly the chosen actual transport witness. -/
theorem booleanForward_full :
    EquivalenceFamilies.equivSections
      (SmallUniverse.liftedDecode (constantLocal terminal Bool).code)
      (SmallUniverse.liftedDecode (constantLocal terminal Bool).code)
      ⟨pathToMap booleanUniverseLoop, booleanUniversalTransportEquivalence⟩ =
      booleanInternalEquivalence :=
  pathToEquiv_beta booleanUniverseLoop

/-- Applying the native reverse map to that internal Boolean equivalence gives
its actual constructed Glue path. -/
theorem booleanReverse_full :
    Term.map (equivToPath (constantLocal terminal Bool).code (constantLocal terminal Bool).code)
      booleanInternalEquivalence =
      CubicalNativeUnivalenceUa.recoveredBooleanLoop := by
  exact (congrArg (Term.map (equivToPath (constantLocal terminal Bool).code
    (constantLocal terminal Bool).code)) booleanForward_full.symm).trans
    (equivToPath_beta (pathToMap booleanUniverseLoop) booleanUniversalTransportEquivalence)

/-- The same forward equality holds after adding an interval parameter. -/
theorem booleanForward_interval :
    let a := (constantLocal terminal Bool).code
    let σ := projection (interval (raisedContext terminal))
    let p := booleanUniverseLoop.reindex σ
    Term.map (Functor.whiskerLeft σ.mapElements (pathToEquiv a a)) p =
      EquivalenceFamilies.equivReindexSections (SmallUniverse.liftedDecode a)
        (SmallUniverse.liftedDecode a) σ
        ⟨pathToMap (a := σ ≫ a) (b := σ ≫ a) (Term.map (pathReindex
          (reindex (SmallUniverse.family (raisedContext terminal))
            (projection (interval (raisedContext terminal))))
          (SmallUniverse.term a) (SmallUniverse.term a) σ) p),
         pathToEquivalence (a := σ ≫ a) (b := σ ≫ a) (Term.map (pathReindex
          (reindex (SmallUniverse.family (raisedContext terminal))
            (projection (interval (raisedContext terminal))))
          (SmallUniverse.term a) (SmallUniverse.term a) σ) p)⟩ :=
  pathToEquiv_reindex_beta _ _

end Examples.CubicalNativeUnivalenceSectionBeta
