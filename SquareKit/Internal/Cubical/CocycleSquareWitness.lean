import SquareKit.Internal.Cubical.SquareBoundarySieve
import SquareKit.Internal.Cubical.CubeProductFunctor

/-! A concrete closed square with zero formal boundary and a signed integer observation. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory

def zeroCocycle (C : Type*) [Category C] : Cocycle2 C where
  cochain _ _ := 0
  closed _ _ _ := rfl

theorem squareCocycle_face {I : Cube} (α : I ⟶ (⟨2⟩ : Cube))
    (p : squareBoundarySieve.contains (Over.mk α)) :
    squareCocycle.pullback (Over.map α) = zeroCocycle (Over I) := by
  apply Cocycle2.ext
  funext X Y Z f g
  let k : (Over.map α).obj Z ⟶ Over.mk α := Over.homMk Z.hom rfl
  exact squareCocycle_boundary ((Over.map α).map f) ((Over.map α).map g)
    (squareBoundarySieve.downward k p)

def horizontalEdge (b : Bool) : (⟨1⟩ : Cube) ⟶ (⟨2⟩ : Cube) :=
  Cube.pair (Cube.endpoint ⟨1⟩ b) (𝟙 (⟨1⟩ : Cube))
def verticalEdge (a : Bool) : (⟨1⟩ : Cube) ⟶ (⟨2⟩ : Cube) :=
  Cube.pair (𝟙 (⟨1⟩ : Cube)) (Cube.endpoint ⟨1⟩ a)

theorem horizontalEdge_label (b : Bool) : squareFaceData (Over.mk (horizontalEdge b)) = (none,some b) := by
  cases b <;> rfl

theorem verticalEdge_label (a : Bool) : squareFaceData (Over.mk (verticalEdge a)) = (some a,none) := by
  cases a <;> rfl

theorem squareCocycle_horizontal (b : Bool) :
    squareCocycle.pullback (Over.map (horizontalEdge b)) = zeroCocycle (Over (⟨1⟩ : Cube)) := by
  apply squareCocycle_face
  right
  change (squareFaceData (Over.mk (horizontalEdge b))).2 ≠ none
  rw [horizontalEdge_label]
  simp

theorem squareCocycle_vertical (a : Bool) :
    squareCocycle.pullback (Over.map (verticalEdge a)) = zeroCocycle (Over (⟨1⟩ : Cube)) := by
  apply squareCocycle_face
  left
  change (squareFaceData (Over.mk (verticalEdge a))).1 ≠ none
  rw [verticalEdge_label]
  simp

def observeSquare (z : CubeCocycle (⟨2⟩ : Cube)) : ℤ :=
  z.eval (Cube.endpoint ⟨0⟩ false) (horizontalEdge false) (𝟙 _) -
  z.eval (Cube.endpoint ⟨0⟩ true) (horizontalEdge false) (𝟙 _) +
  z.eval (Cube.endpoint ⟨0⟩ false) (verticalEdge true) (𝟙 _) -
  z.eval (Cube.endpoint ⟨0⟩ true) (verticalEdge true) (𝟙 _) +
  z.eval (Cube.endpoint ⟨0⟩ true) (horizontalEdge true) (𝟙 _) -
  z.eval (Cube.endpoint ⟨0⟩ false) (horizontalEdge true) (𝟙 _) +
  z.eval (Cube.endpoint ⟨0⟩ true) (verticalEdge false) (𝟙 _) -
  z.eval (Cube.endpoint ⟨0⟩ false) (verticalEdge false) (𝟙 _)

end SquareKit.Cubical.CategoryCocycles
