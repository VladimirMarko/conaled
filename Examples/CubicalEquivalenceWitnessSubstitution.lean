import Examples.CubicalUniversalDecode
import SquareKit.Internal.Cubical.EquivalenceWitnessSubstitution

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalEquivalenceWitnessSubstitution
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalUnivalenceTransport
open SmallUniverse.NativeUnivalence EquivalenceFamilies

/-- Two added interval parameters preserve the encoded Boolean transport witness,
including the chosen center and contraction of every fiber. -/
theorem booleanWitness_two_intervals :
    let σ := projection (interval (raisedContext terminal))
    let τ := projection (interval (total (interval (raisedContext terminal))))
    isEquivReindexSections (pathToMap booleanUniverseLoop) (τ ≫ σ)
      ((booleanUniversalTransportEquivalence.reindex σ).reindex τ) =
      (isEquivReindexSections (pathToMap booleanUniverseLoop) σ
        (booleanUniversalTransportEquivalence.reindex σ)).reindex τ :=
  isEquivReindexSections_comp _ _ _ _

/-- Decoding the substituted internal witness recovers the same full selected data. -/
theorem booleanDecodedWitness_two_intervals :
    let σ := projection (interval (raisedContext terminal))
    let τ := projection (interval (total (interval (raisedContext terminal))))
    let s := (encodeIsEquiv booleanUniversalTransportEquivalence).reindex σ
    (isEquivReindexSections (pathToMap booleanUniverseLoop) (τ ≫ σ)).symm (s.reindex τ) =
      ((isEquivReindexSections (pathToMap booleanUniverseLoop) σ).symm s).reindex τ :=
  isEquivReindexSections_decode_reindex _ _ _ _

end Examples.CubicalEquivalenceWitnessSubstitution
