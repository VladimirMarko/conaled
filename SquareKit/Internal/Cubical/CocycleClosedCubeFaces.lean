import SquareKit.Internal.Cubical.CocycleIdentityObservation

/-! Closed cube restrictions and their exact formal interval coordinates. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

def cubeAxis (k : Fin 3) : (⟨3⟩ : Cube) ⟶ (⟨1⟩ : Cube) := Cube.ofRaw (fun _ => Expr.var k)

def faceRestriction (j : Fin 3) (e : Bool) : terminalPoint ⟨3⟩ ⟶ terminalPoint ⟨2⟩ :=
  Functor.Elements.homMk (face3 j e).op rfl

def faceAxis (j : Fin 3) (e : Bool) (k : Fin 3) :
    (interval terminal.{0}).obj (terminalPoint ⟨2⟩) := ⟨Cube.ofRaw (fun _ => rawFace3 j e k)⟩

theorem map_faceAxis (j : Fin 3) (e : Bool) (k : Fin 3) :
    (interval terminal.{0}).map (faceRestriction j e) ⟨cubeAxis k⟩ = faceAxis j e k := rfl

theorem faceAxis00 (e : Bool) : faceAxis 0 e 0 = (endpoint terminal e).val (terminalPoint ⟨2⟩) := by cases e <;> rfl

theorem faceAxis01 (e : Bool) : faceAxis 0 e 1 = ⟨squareAxis 0⟩ := by cases e <;> rfl

theorem faceAxis02 (e : Bool) : faceAxis 0 e 2 = ⟨squareAxis 1⟩ := by cases e <;> rfl

theorem faceAxis10 (e : Bool) : faceAxis 1 e 0 = ⟨squareAxis 0⟩ := by cases e <;> rfl

theorem faceAxis11 (e : Bool) : faceAxis 1 e 1 = (endpoint terminal e).val (terminalPoint ⟨2⟩) := by cases e <;> rfl

theorem faceAxis12 (e : Bool) : faceAxis 1 e 2 = ⟨squareAxis 1⟩ := by cases e <;> rfl

theorem faceAxis20 (e : Bool) : faceAxis 2 e 0 = ⟨squareAxis 0⟩ := by cases e <;> rfl

theorem faceAxis21 (e : Bool) : faceAxis 2 e 1 = ⟨squareAxis 1⟩ := by cases e <;> rfl

theorem faceAxis22 (e : Bool) : faceAxis 2 e 2 = (endpoint terminal e).val (terminalPoint ⟨2⟩) := by cases e <;> rfl

end SquareKit.Cubical.CategoryCocycles
