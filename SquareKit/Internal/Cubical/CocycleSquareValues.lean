import SquareKit.Internal.Cubical.CocycleSquareWitness

/-! Evaluation of the selected square at two arbitrary formal dimensions. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory

noncomputable def squareValue {I : Cube} (r s : I ⟶ (⟨1⟩ : Cube)) : CubeCocycle I :=
  cocycles.map (Quiver.Hom.op (Cube.pair s r)) squareCocycle

theorem squareValue_left {I : Cube} (s : I ⟶ (⟨1⟩ : Cube)) (b : Bool) :
    squareValue (Cube.endpoint I b) s = zeroCocycle (Over I) := by
  have e : Cube.comp s (verticalEdge b) = Cube.pair s (Cube.endpoint I b) :=
    (Cube.comp_pair _ _ _).trans
      (congrArg₂ Cube.pair (@Category.comp_id Cube _ I ⟨1⟩ s) (Cube.comp_endpoint s b))
  have h := congrArg (fun f : I ⟶ (⟨2⟩ : Cube) => cocycles.map f.op squareCocycle) e
  exact h.symm.trans ((cocycles.map_comp_apply (verticalEdge b).op s.op squareCocycle).trans
    (congrArg (fun z => cocycles.map s.op z) (squareCocycle_vertical b)))

theorem squareValue_right {I : Cube} (r : I ⟶ (⟨1⟩ : Cube)) (b : Bool) :
    squareValue r (Cube.endpoint I b) = zeroCocycle (Over I) := by
  have e : Cube.comp r (horizontalEdge b) = Cube.pair (Cube.endpoint I b) r :=
    (Cube.comp_pair _ _ _).trans
      (congrArg₂ Cube.pair (Cube.comp_endpoint r b) (@Category.comp_id Cube _ I ⟨1⟩ r))
  have h := congrArg (fun f : I ⟶ (⟨2⟩ : Cube) => cocycles.map f.op squareCocycle) e
  exact h.symm.trans ((cocycles.map_comp_apply (horizontalEdge b).op r.op squareCocycle).trans
    (congrArg (fun z => cocycles.map r.op z) (squareCocycle_horizontal b)))

end SquareKit.Cubical.CategoryCocycles
