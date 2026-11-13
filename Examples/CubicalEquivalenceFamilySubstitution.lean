import Examples.CubicalUniversalDecode
import SquareKit.Internal.Cubical.EquivalenceFamilySubstitution

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalEquivalenceFamilySubstitution
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalUnivalenceTransport
open SmallUniverse.NativeUnivalence EquivalenceFamilies

private abbrev booleanCarrier :=
  SmallUniverse.liftedDecode (Examples.CubicalGlue.constantLocal terminal Bool).code

/-- Adding two interval parameters commutes with encoding the actual Boolean
universe-loop transport, including every selected fiber contraction. -/
theorem booleanEquivalence_two_intervals :
    let σ := projection (interval (raisedContext terminal))
    let τ := projection (interval (total (interval (raisedContext terminal))))
    equivReindexSections booleanCarrier booleanCarrier (τ ≫ σ)
      ⟨Functor.whiskerLeft τ.mapElements (Functor.whiskerLeft σ.mapElements
        (pathToMap booleanUniverseLoop)),
        (booleanUniversalTransportEquivalence.reindex σ).reindex τ⟩ =
      (equivReindexSections booleanCarrier booleanCarrier σ
        ⟨Functor.whiskerLeft σ.mapElements (pathToMap booleanUniverseLoop),
          booleanUniversalTransportEquivalence.reindex σ⟩).reindex τ :=
  equivReindexSections_comp _ _ _ _ _ _

/-- The identity substitution bridge agrees on the full chosen equivalence,
not only its Boolean function. -/
theorem booleanEquivalence_identity :
    equivReindexSections booleanCarrier booleanCarrier (𝟙 (raisedContext terminal))
      ⟨pathToMap booleanUniverseLoop, booleanUniversalTransportEquivalence⟩ =
      equivSections booleanCarrier booleanCarrier ⟨pathToMap booleanUniverseLoop, booleanUniversalTransportEquivalence⟩ :=
  equivReindexSections_id _ _ _ _

end Examples.CubicalEquivalenceFamilySubstitution
