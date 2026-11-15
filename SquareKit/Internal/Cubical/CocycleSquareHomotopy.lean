import SquareKit.Internal.Cubical.CocycleStokes
import SquareKit.Internal.Cubical.CocycleSquareObservation

/-! Relative three-cubes preserve the integer observation of their two square ends. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory

/-- A cubical homotopy relative to the four zero sides. No filler is assumed. -/
structure SquareHomotopy (a b : CubeCocycle (⟨2⟩ : Cube)) where
  cube : CubeCocycle (⟨3⟩ : Cube)
  start : cube.pullback (Over.map (face3 0 false)) = a
  finish : cube.pullback (Over.map (face3 0 true)) = b
  side₁ : ∀ e, cube.pullback (Over.map (face3 1 e)) = zeroCocycle (Over (⟨2⟩ : Cube))
  side₂ : ∀ e, cube.pullback (Over.map (face3 2 e)) = zeroCocycle (Over (⟨2⟩ : Cube))

theorem SquareHomotopy.observation {a b : CubeCocycle (⟨2⟩ : Cube)} (h : SquareHomotopy a b) :
    observeSquare a = observeSquare b := by
  have e := observeSquare_stokes h.cube
  rw [h.start,h.finish,h.side₁ false,h.side₁ true,h.side₂ false,h.side₂ true,observeSquare_zero] at e
  omega

theorem squareCocycle_no_zero_homotopy :
    ¬ Nonempty (SquareHomotopy squareCocycle (zeroCocycle (Over (⟨2⟩ : Cube)))) := by
  rintro ⟨h⟩
  have e := h.observation
  rw [observeSquare_witness,observeSquare_zero] at e
  exact Int.one_ne_zero e

end SquareKit.Cubical.CategoryCocycles
