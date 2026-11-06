import SquareKit.Internal.Cubical.CocycleIdentityRestriction

/-! Actual third identities preserve the integer observation of normalized second identities. -/
noncomputable section
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

def cubeAxis (k : Fin 3) : (⟨3⟩ : Cube) ⟶ (⟨1⟩ : Cube) := Cube.ofRaw (fun _ => Expr.var k)

def thirdCube {a b : Term (SecondIdentityFamily terminal.{0})}
    (h : Term (normalizedIdentity (SecondIdentityFamily terminal.{0}) a b)) : CubeCocycle (⟨3⟩ : Cube) :=
  thirdValue h (terminalPoint ⟨3⟩) ⟨cubeAxis 0⟩ ⟨cubeAxis 1⟩ ⟨cubeAxis 2⟩

private def faceRestriction (j : Fin 3) (e : Bool) : terminalPoint ⟨3⟩ ⟶ terminalPoint ⟨2⟩ :=
  Functor.Elements.homMk (face3 j e).op rfl

private def faceAxis (j : Fin 3) (e : Bool) (k : Fin 3) :
    (interval terminal.{0}).obj (terminalPoint ⟨2⟩) := ⟨Cube.ofRaw (fun _ => rawFace3 j e k)⟩

private theorem map_faceAxis (j : Fin 3) (e : Bool) (k : Fin 3) :
    (interval terminal.{0}).map (faceRestriction j e) ⟨cubeAxis k⟩ = faceAxis j e k := rfl

private theorem thirdCube_face {a b : Term (SecondIdentityFamily terminal.{0})}
    (h : Term (normalizedIdentity (SecondIdentityFamily terminal.{0}) a b)) (j : Fin 3) (e : Bool) :
    (thirdCube h).pullback (Over.map (face3 j e)) =
      thirdValue h (terminalPoint ⟨2⟩) (faceAxis j e 0) (faceAxis j e 1) (faceAxis j e 2) := by
  have q := thirdValue_map h (faceRestriction j e) ⟨cubeAxis 0⟩ ⟨cubeAxis 1⟩ ⟨cubeAxis 2⟩
  have v := congrArg₂ (fun r st => thirdValue h (terminalPoint ⟨2⟩) r st.1 st.2)
    (map_faceAxis j e 0) (congrArg₂ Prod.mk (map_faceAxis j e 1) (map_faceAxis j e 2))
  run_tac Lean.Elab.Tactic.withMainContext do
    let l ← Lean.Meta.getLocalDeclFromUserName `q
    let r ← Lean.Meta.getLocalDeclFromUserName `v
    let tl ← Lean.Meta.whnf l.type
    let tr ← Lean.Meta.whnf r.type
    let #[α,a,b] := tl.getAppArgs | throwError "expected equality"
    let #[_,_,c] := tr.getAppArgs | throwError "expected equality"
    let .const _ levels := tl.getAppFn | throwError "expected equality level"
    (← Lean.Elab.Tactic.getMainGoal).assign
      (Lean.mkAppN (Lean.mkConst ``Eq.trans levels) #[α,a,b,c,l.toExpr,r.toExpr])
    Lean.Elab.Tactic.replaceMainGoal []

private theorem faceAxis00 (e : Bool) : faceAxis 0 e 0 = (endpoint terminal e).val (terminalPoint ⟨2⟩) := by cases e <;> rfl

private theorem faceAxis01 (e : Bool) : faceAxis 0 e 1 = ⟨squareAxis 0⟩ := by cases e <;> rfl

private theorem faceAxis02 (e : Bool) : faceAxis 0 e 2 = ⟨squareAxis 1⟩ := by cases e <;> rfl

private theorem faceAxis10 (e : Bool) : faceAxis 1 e 0 = ⟨squareAxis 0⟩ := by cases e <;> rfl

private theorem faceAxis11 (e : Bool) : faceAxis 1 e 1 = (endpoint terminal e).val (terminalPoint ⟨2⟩) := by cases e <;> rfl

private theorem faceAxis12 (e : Bool) : faceAxis 1 e 2 = ⟨squareAxis 1⟩ := by cases e <;> rfl

private theorem faceAxis20 (e : Bool) : faceAxis 2 e 0 = ⟨squareAxis 0⟩ := by cases e <;> rfl

private theorem faceAxis21 (e : Bool) : faceAxis 2 e 1 = ⟨squareAxis 1⟩ := by cases e <;> rfl

private theorem faceAxis22 (e : Bool) : faceAxis 2 e 2 = (endpoint terminal e).val (terminalPoint ⟨2⟩) := by cases e <;> rfl

theorem thirdCube_start {a b : Term (SecondIdentityFamily terminal.{0})}
    (h : Term (normalizedIdentity (SecondIdentityFamily terminal.{0}) a b)) :
    (thirdCube h).pullback (Over.map (face3 0 false)) = secondSquare a := by
  have e := thirdCube_face h 0 false
  simp only [faceAxis00,faceAxis01,faceAxis02,faceAxis10,faceAxis11,faceAxis12,faceAxis20,faceAxis21,faceAxis22] at e
  exact e.trans (thirdValue_zero h (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩)

theorem thirdCube_finish {a b : Term (SecondIdentityFamily terminal.{0})}
    (h : Term (normalizedIdentity (SecondIdentityFamily terminal.{0}) a b)) :
    (thirdCube h).pullback (Over.map (face3 0 true)) = secondSquare b := by
  have e := thirdCube_face h 0 true
  simp only [faceAxis00,faceAxis01,faceAxis02,faceAxis10,faceAxis11,faceAxis12,faceAxis20,faceAxis21,faceAxis22] at e
  exact e.trans (thirdValue_one h (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩)

theorem thirdCube_side₁ {a b : Term (SecondIdentityFamily terminal.{0})}
    (h : Term (normalizedIdentity (SecondIdentityFamily terminal.{0}) a b)) (e : Bool) :
    (thirdCube h).pullback (Over.map (face3 1 e)) = zeroCocycle (Over (⟨2⟩ : Cube)) := by
  have q := thirdCube_face h 1 e
  simp only [faceAxis00,faceAxis01,faceAxis02,faceAxis10,faceAxis11,faceAxis12,faceAxis20,faceAxis21,faceAxis22] at q
  exact q.trans (thirdValue_middle h (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩ e)

theorem thirdCube_side₂ {a b : Term (SecondIdentityFamily terminal.{0})}
    (h : Term (normalizedIdentity (SecondIdentityFamily terminal.{0}) a b)) (e : Bool) :
    (thirdCube h).pullback (Over.map (face3 2 e)) = zeroCocycle (Over (⟨2⟩ : Cube)) := by
  have q := thirdCube_face h 2 e
  simp only [faceAxis00,faceAxis01,faceAxis02,faceAxis10,faceAxis11,faceAxis12,faceAxis20,faceAxis21,faceAxis22] at q
  exact q.trans (thirdValue_right h (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩ e)

def identitySquareHomotopy {a b : Term (SecondIdentityFamily terminal.{0})}
    (h : Term (normalizedIdentity (SecondIdentityFamily terminal.{0}) a b)) :
    SquareHomotopy (secondSquare a) (secondSquare b) :=
  ⟨thirdCube h,thirdCube_start h,thirdCube_finish h,thirdCube_side₁ h,thirdCube_side₂ h⟩

theorem secondObservation_identity {a b : Term (SecondIdentityFamily terminal.{0})}
    (h : Term (normalizedIdentity (SecondIdentityFamily terminal.{0}) a b)) :
    secondObservation a = secondObservation b := (identitySquareHomotopy h).observation

end SquareKit.Cubical.CategoryCocycles
