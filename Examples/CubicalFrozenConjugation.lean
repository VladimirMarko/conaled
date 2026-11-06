import Examples.CubicalFrozenHigherObservation
import Examples.CubicalPathComparison
import SquareKit.Internal.Cubical.CocycleEndpointComparison

/-! The actual J comparison supplies the commuting cube for the frozen higher witness. -/
noncomputable section
namespace Examples.CubicalFrozenConjugation
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SquareKit.Cubical.CategoryCocycles
open Examples.CubicalCocycleAssignment Examples.CubicalPathComparison

/-- The comparison is evaluated along the interpreted frozen homotopy. -/
def conjugationCube := comparisonCube betaLoop selectedNormalizedHomotopy

theorem transport_face : conjugationCube.pullback (Over.map (face3 1 false)) =
    actionSquare (t := transportedLoop) selectedNormalizedHomotopy :=
  comparisonCube_start betaLoop selectedNormalizedHomotopy

theorem witness_face : conjugationCube.pullback (Over.map (face3 1 true)) =
    secondSquare selectedNormalizedHomotopy :=
  comparisonCube_finish betaLoop selectedNormalizedHomotopy

/-- These are the two actual endpoint comparisons, with opposite boundary orientations. -/
theorem endpoint_faces (e : Bool) : conjugationCube.pullback (Over.map (face3 0 e)) =
    comparisonRootSquare betaLoop := comparisonCube_root betaLoop selectedNormalizedHomotopy e

theorem remaining_faces (e : Bool) : conjugationCube.pullback (Over.map (face3 2 e)) =
    zeroCocycle (Over (⟨2⟩ : Cube)) := comparisonCube_side betaLoop selectedNormalizedHomotopy e

theorem transportedHigherObservation :
    observeSquare (actionSquare (t := transportedLoop) selectedNormalizedHomotopy) = 1 :=
  (actionSquare_observation betaLoop selectedNormalizedHomotopy).trans frozenHigherObservation

theorem transportedHigher_no_erasure :
    actionSquare (t := transportedLoop) selectedNormalizedHomotopy ≠ zeroCocycle (Over (⟨2⟩ : Cube)) := by
  intro h
  exact Int.one_ne_zero (transportedHigherObservation.symm.trans
    ((congrArg observeSquare h).trans observeSquare_zero))

end Examples.CubicalFrozenConjugation
