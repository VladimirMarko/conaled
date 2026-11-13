import Examples.CubicalUniversalDecode
import SquareKit.Internal.Cubical.EquivalenceFamilyReindex

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalEquivalenceFamilyReindex
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalUnivalenceTransport
open SmallUniverse.NativeUnivalence EquivalenceFamilies

private abbrev booleanCarrier :=
  SmallUniverse.liftedDecode (Examples.CubicalGlue.constantLocal terminal Bool).code

/-- Move the actual Boolean universe-loop equivalence through the native
reindex isomorphism and decode it: its selected contractions are recovered too. -/
theorem booleanSelectedData_recovered :
    let σ := projection (interval (raisedContext terminal))
    let f := Functor.whiskerLeft σ.mapElements (pathToMap booleanUniverseLoop)
    let E := booleanUniversalTransportEquivalence.reindex σ
    (equivSections (reindex booleanCarrier σ) (reindex booleanCarrier σ)).symm
      (Term.map (equivReindexIso booleanCarrier booleanCarrier σ).hom
        (equivReindexSections booleanCarrier booleanCarrier σ ⟨f,E⟩)) = ⟨f,E⟩ := by
  dsimp only
  exact (congrArg (equivSections _ _).symm
    (equivReindexIso_hom_encode booleanCarrier booleanCarrier _ _ _)).trans
      ((equivSections _ _).symm_apply_apply _)

end Examples.CubicalEquivalenceFamilyReindex
