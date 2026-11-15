import Examples.CubicalUniversalDecode
import SquareKit.Internal.Cubical.NativeUnivalenceMapNaturality

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalNativeUnivalenceMapNaturality
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalGlue Examples.CubicalUnivalenceTransport
open SmallUniverse.NativeUnivalence

/-- The native Boolean forward map commutes with adding an interval parameter
through the actual path and full-equivalence family isomorphisms. -/
theorem booleanForward_conjugate_interval :
    let a := (constantLocal terminal Bool).code
    let σ := projection (interval (raisedContext terminal))
    (pathReindexIso
      (reindex (SmallUniverse.family (raisedContext terminal))
        (projection (interval (raisedContext terminal))))
      (SmallUniverse.term a) (SmallUniverse.term a) σ).inv ≫
      Functor.whiskerLeft σ.mapElements (pathToEquiv a a) ≫
      (EquivalenceFamilies.equivReindexIso (SmallUniverse.liftedDecode a)
        (SmallUniverse.liftedDecode a) σ).hom = pathToEquiv (σ ≫ a) (σ ≫ a) :=
  pathToEquiv_conjugate_reindex _ _ _

/-- Evaluating that conjugated map on the actual Boolean loop retains its
chosen universal-El transport map and all selected fiber contractions. -/
theorem booleanLoop_conjugated_full :
    let a := (constantLocal terminal Bool).code
    let σ := projection (interval (raisedContext terminal))
    let p := reindexPath booleanUniverseLoop σ
    Term.map
      ((pathReindexIso
        (reindex (SmallUniverse.family (raisedContext terminal))
          (projection (interval (raisedContext terminal))))
        (SmallUniverse.term a) (SmallUniverse.term a) σ).inv ≫
        Functor.whiskerLeft σ.mapElements (pathToEquiv a a) ≫
        (EquivalenceFamilies.equivReindexIso (SmallUniverse.liftedDecode a)
          (SmallUniverse.liftedDecode a) σ).hom) p =
      EquivalenceFamilies.equivSections (SmallUniverse.liftedDecode (σ ≫ a))
        (SmallUniverse.liftedDecode (σ ≫ a)) ⟨pathToMap p,pathToEquivalence p⟩ := by
  let a := (constantLocal terminal Bool).code
  let σ := projection (interval (raisedContext terminal))
  let p := reindexPath booleanUniverseLoop σ
  exact (congrArg (fun f : paths (σ ≫ a) (σ ≫ a) ⟶ equivalences (σ ≫ a) (σ ≫ a) =>
    Term.map f p) booleanForward_conjugate_interval).trans (pathToEquiv_beta p).symm

end Examples.CubicalNativeUnivalenceMapNaturality
