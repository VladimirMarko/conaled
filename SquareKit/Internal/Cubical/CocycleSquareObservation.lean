import SquareKit.Internal.Cubical.CocycleSquareWitness

/-! The concrete boundary cocycle has signed square observation one. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory

private theorem cube_id (I : Cube) : (𝟙 I : I ⟶ I) = Cube.identity I := rfl
private theorem cube_comp {I J K : Cube} (f : I ⟶ J) (g : J ⟶ K) : f ≫ g = Cube.comp f g := rfl


open scoped Classical

private theorem flag_value {I J : Cube} (f : I ⟶ J) (g : J ⟶ (⟨2⟩ : Cube)) :
    squareCocycle.eval f g (𝟙 _) =
      (if h : squareBoundarySieve.contains (Over.mk g) then
        squareEdgeValue (squareLabel (Over.mk (f ≫ g)) (squareBoundarySieve.downward (Over.homMk f rfl : Over.mk (f ≫ g) ⟶ Over.mk g) h))
          (squareLabel (Over.mk g) h) else 0) := by
  have outside : ¬ squareBoundarySieve.contains (Over.mk (𝟙 (⟨2⟩ : Cube))) := by
    change ¬ (none ≠ (none : Option Bool) ∨ none ≠ (none : Option Bool))
    simp
  simp only [CubeCocycle.eval,squareCocycle,coboundary,δ1,extendZero]
  simp only [outside, dite_false, zero_sub, sub_zero, zero_add, Category.comp_id]
  split <;> simp_all [partialSquareCochain, squareLabel, squareEdgeValue, squareFaceData, Category.comp_id]

private theorem horizontal_vertex_label (a b : Bool) :
    squareFaceData (Over.mk (Cube.endpoint ⟨0⟩ a ≫ horizontalEdge b)) = (some a,some b) := by
  cases a <;> cases b <;> rfl

private theorem vertical_vertex_label (a b : Bool) :
    squareFaceData (Over.mk (Cube.endpoint ⟨0⟩ b ≫ verticalEdge a)) = (some a,some b) := by
  cases a <;> cases b <;> rfl

theorem squareCocycle_horizontal_flag (a b : Bool) :
    squareCocycle.eval (Cube.endpoint ⟨0⟩ a) (horizontalEdge b) (𝟙 _) =
      if a && b then 1 else 0 := by
  rw [flag_value]
  simp only [squareLabel,squareEdgeValue,squareBoundarySieve,horizontalEdge_label,horizontal_vertex_label]
  cases a <;> cases b <;> simp

theorem squareCocycle_vertical_flag (a b : Bool) :
    squareCocycle.eval (Cube.endpoint ⟨0⟩ b) (verticalEdge a) (𝟙 _) = 0 := by
  rw [flag_value]
  simp only [squareLabel,squareEdgeValue,squareBoundarySieve,verticalEdge_label,vertical_vertex_label]
  cases a <;> cases b <;> simp

theorem observeSquare_witness : observeSquare squareCocycle = 1 := by
  simp [observeSquare,squareCocycle_horizontal_flag,squareCocycle_vertical_flag]

theorem observeSquare_zero : observeSquare (zeroCocycle (Over (⟨2⟩ : Cube))) = 0 := rfl

theorem squareCocycle_ne_zero : squareCocycle ≠ zeroCocycle (Over (⟨2⟩ : Cube)) := by
  intro h
  have e := congrArg observeSquare h
  rw [observeSquare_witness,observeSquare_zero] at e
  exact Int.one_ne_zero e

end SquareKit.Cubical.CategoryCocycles
