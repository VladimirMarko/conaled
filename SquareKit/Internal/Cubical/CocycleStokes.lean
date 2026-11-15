import SquareKit.Internal.Cubical.CocycleCubeFlags

/-! The integer square observation satisfies the cubical Stokes identity. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory

private theorem flag_closed (z : CubeCocycle (⟨3⟩ : Cube)) (j : Fin 3) (k : Fin 2) (s : Fin 3 → Bool) :
    z.eval (edge2 k (s (remainingAxis j (otherAxis2 k)))) (face3 j (s j)) (𝟙 _) -
    z.eval (vertex2 (fun i => s (remainingAxis j i))) (face3 j (s j)) (𝟙 _) +
    z.eval (Cube.endpoint ⟨0⟩ (s (remainingAxis j k))) (edge3 (remainingAxis j k) s) (𝟙 _) -
    z.eval (Cube.endpoint ⟨0⟩ (s (remainingAxis j k)))
      (edge2 k (s (remainingAxis j (otherAxis2 k)))) (face3 j (s j)) = 0 := by
  have e := z.closed_eval (Cube.endpoint ⟨0⟩ (s (remainingAxis j k)))
    (edge2 k (s (remainingAxis j (otherAxis2 k)))) (face3 j (s j)) (𝟙 _)
  rw [endpoint_edge2 k (fun i => s (remainingAxis j i)),edge2_face3,Category.comp_id] at e
  exact e

theorem observeSquare_stokes (z : CubeCocycle (⟨3⟩ : Cube)) :
    observeSquare (z.pullback (Over.map (face3 0 false))) -
    observeSquare (z.pullback (Over.map (face3 0 true))) -
    observeSquare (z.pullback (Over.map (face3 1 false))) +
    observeSquare (z.pullback (Over.map (face3 1 true))) +
    observeSquare (z.pullback (Over.map (face3 2 false))) -
    observeSquare (z.pullback (Over.map (face3 2 true))) = 0 := by
  have h00000 := flag_closed z 0 0 ![false,false,false]
  have h00001 := flag_closed z 0 0 ![false,false,true]
  have h00010 := flag_closed z 0 0 ![false,true,false]
  have h00011 := flag_closed z 0 0 ![false,true,true]
  have h00100 := flag_closed z 0 0 ![true,false,false]
  have h00101 := flag_closed z 0 0 ![true,false,true]
  have h00110 := flag_closed z 0 0 ![true,true,false]
  have h00111 := flag_closed z 0 0 ![true,true,true]
  have h01000 := flag_closed z 0 1 ![false,false,false]
  have h01001 := flag_closed z 0 1 ![false,false,true]
  have h01010 := flag_closed z 0 1 ![false,true,false]
  have h01011 := flag_closed z 0 1 ![false,true,true]
  have h01100 := flag_closed z 0 1 ![true,false,false]
  have h01101 := flag_closed z 0 1 ![true,false,true]
  have h01110 := flag_closed z 0 1 ![true,true,false]
  have h01111 := flag_closed z 0 1 ![true,true,true]
  have h10000 := flag_closed z 1 0 ![false,false,false]
  have h10001 := flag_closed z 1 0 ![false,false,true]
  have h10010 := flag_closed z 1 0 ![false,true,false]
  have h10011 := flag_closed z 1 0 ![false,true,true]
  have h10100 := flag_closed z 1 0 ![true,false,false]
  have h10101 := flag_closed z 1 0 ![true,false,true]
  have h10110 := flag_closed z 1 0 ![true,true,false]
  have h10111 := flag_closed z 1 0 ![true,true,true]
  have h11000 := flag_closed z 1 1 ![false,false,false]
  have h11001 := flag_closed z 1 1 ![false,false,true]
  have h11010 := flag_closed z 1 1 ![false,true,false]
  have h11011 := flag_closed z 1 1 ![false,true,true]
  have h11100 := flag_closed z 1 1 ![true,false,false]
  have h11101 := flag_closed z 1 1 ![true,false,true]
  have h11110 := flag_closed z 1 1 ![true,true,false]
  have h11111 := flag_closed z 1 1 ![true,true,true]
  have h20000 := flag_closed z 2 0 ![false,false,false]
  have h20001 := flag_closed z 2 0 ![false,false,true]
  have h20010 := flag_closed z 2 0 ![false,true,false]
  have h20011 := flag_closed z 2 0 ![false,true,true]
  have h20100 := flag_closed z 2 0 ![true,false,false]
  have h20101 := flag_closed z 2 0 ![true,false,true]
  have h20110 := flag_closed z 2 0 ![true,true,false]
  have h20111 := flag_closed z 2 0 ![true,true,true]
  have h21000 := flag_closed z 2 1 ![false,false,false]
  have h21001 := flag_closed z 2 1 ![false,false,true]
  have h21010 := flag_closed z 2 1 ![false,true,false]
  have h21011 := flag_closed z 2 1 ![false,true,true]
  have h21100 := flag_closed z 2 1 ![true,false,false]
  have h21101 := flag_closed z 2 1 ![true,false,true]
  have h21110 := flag_closed z 2 1 ![true,true,false]
  have h21111 := flag_closed z 2 1 ![true,true,true]
  simp only [observeSquare,CubeCocycle.pullback_eval,Category.id_comp]
  dsimp only [remainingAxis,otherAxis2,vertex2,rawVertex2] at *
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, ite_true, ite_false, Fin.zero_eq_one_iff] at *
  simp [Matrix.vecHead, Matrix.vecTail, edge3, rawEdge3, flagEndpoint] at *
  omega

end SquareKit.Cubical.CategoryCocycles
