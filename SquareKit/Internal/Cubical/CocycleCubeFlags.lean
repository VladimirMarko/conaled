import SquareKit.Internal.Cubical.CocycleSquareWitness
import Mathlib.Data.Fin.VecNotation

/-! The formal flags used in the square and cube boundary formulas. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory

def flagEndpoint (b : Bool) : Expr α := if b then .one else .zero

def rawEdge2 (k : Fin 2) (b : Bool) : Cube.Raw ⟨1⟩ ⟨2⟩ :=
  if k = 0 then Fin.cases (.var 0) (fun _ => flagEndpoint b)
  else Fin.cases (flagEndpoint b) Expr.var

def edge2 (k : Fin 2) (b : Bool) : (⟨1⟩ : Cube) ⟶ (⟨2⟩ : Cube) := Cube.ofRaw (rawEdge2 k b)
@[simp] theorem edge2_zero (b : Bool) : edge2 0 b = horizontalEdge b := rfl
@[simp] theorem edge2_one (b : Bool) : edge2 1 b = verticalEdge b := rfl

def otherAxis2 (k : Fin 2) : Fin 2 := if k = 0 then 1 else 0

def rawVertex2 (v : Fin 2 → Bool) : Cube.Raw ⟨0⟩ ⟨2⟩ := ![flagEndpoint (v 0),flagEndpoint (v 1)]
def vertex2 (v : Fin 2 → Bool) : (⟨0⟩ : Cube) ⟶ (⟨2⟩ : Cube) := Cube.ofRaw (rawVertex2 v)

def remainingAxis (j : Fin 3) (k : Fin 2) : Fin 3 := ![![1,2],![0,2],![0,1]] j k

def rawFace3 (j : Fin 3) (b : Bool) : Cube.Raw ⟨2⟩ ⟨3⟩ :=
  ![![flagEndpoint b,.var 0,.var 1],![.var 0,flagEndpoint b,.var 1],![.var 0,.var 1,flagEndpoint b]] j

def face3 (j : Fin 3) (b : Bool) : (⟨2⟩ : Cube) ⟶ (⟨3⟩ : Cube) := Cube.ofRaw (rawFace3 j b)

def rawEdge3 (k : Fin 3) (s : Fin 3 → Bool) : Cube.Raw ⟨1⟩ ⟨3⟩ :=
  ![if 0 = k then .var 0 else flagEndpoint (s 0),
    if 1 = k then .var 0 else flagEndpoint (s 1),
    if 2 = k then .var 0 else flagEndpoint (s 2)]
def edge3 (k : Fin 3) (s : Fin 3 → Bool) : (⟨1⟩ : Cube) ⟶ (⟨3⟩ : Cube) := Cube.ofRaw (rawEdge3 k s)

private theorem raw_comp_eq {I J K : Cube} (f : Cube.Raw I J) (g : Cube.Raw J K) (h : Cube.Raw I K)
    (e : (fun i => Expr.subst f (g i)) = h) : Cube.comp (Cube.ofRaw f) (Cube.ofRaw g) = Cube.ofRaw h :=
  congrArg (@Cube.ofRaw I K) e

theorem endpoint_edge2 (k : Fin 2) (v : Fin 2 → Bool) :
    Cube.endpoint ⟨0⟩ (v k) ≫ edge2 k (v (otherAxis2 k)) = vertex2 v := by
  have e : ∀ k : Fin 2, ∀ v : Fin 2 → Bool,
      (fun i => Expr.subst (fun _ : Fin 1 => flagEndpoint (v k)) (rawEdge2 k (v (otherAxis2 k)) i)) =
        rawVertex2 v := by decide
  exact raw_comp_eq _ _ _ (e k v)

theorem edge2_face3 (j : Fin 3) (k : Fin 2) (s : Fin 3 → Bool) :
    edge2 k (s (remainingAxis j (otherAxis2 k))) ≫ face3 j (s j) = edge3 (remainingAxis j k) s := by
  have e : ∀ j : Fin 3, ∀ k : Fin 2, ∀ s : Fin 3 → Bool,
      (fun i => Expr.subst (rawEdge2 k (s (remainingAxis j (otherAxis2 k)))) (rawFace3 j (s j) i)) =
        rawEdge3 (remainingAxis j k) s := by decide
  exact raw_comp_eq _ _ _ (e j k s)

end SquareKit.Cubical.CategoryCocycles
