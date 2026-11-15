import SquareKit.Internal.Cubical.CocycleComparisonValues
import SquareKit.Internal.Cubical.CocycleClosedCubeFaces

/-! The endpoint-comparison cube witnesses conjugation and preserves the higher observation. -/
noncomputable section
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

variable {t : Term (reindex (FirstIdentityFamily terminal.{0}) (projection (FirstIdentityFamily terminal.{0}))) }
variable (β : Term (normalizedIdentity (reindex (FirstIdentityFamily terminal.{0}) (projection (FirstIdentityFamily terminal.{0})))
  t (generic (FirstIdentityFamily terminal.{0}))))

def comparisonCube (h : Term (SecondIdentityFamily terminal.{0})) : CubeCocycle (⟨3⟩ : Cube) :=
  comparisonValue β h (terminalPoint ⟨3⟩) ⟨cubeAxis 0⟩ ⟨cubeAxis 1⟩ ⟨cubeAxis 2⟩

def comparisonRootSquare : CubeCocycle (⟨2⟩ : Cube) :=
  comparisonRootValue β (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩

def actionSquare (h : Term (SecondIdentityFamily terminal.{0})) : CubeCocycle (⟨2⟩ : Cube) :=
  actionValue (t := t) h (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩

private theorem comparisonCube_face (h : Term (SecondIdentityFamily terminal.{0})) (j : Fin 3) (e : Bool) :
    (comparisonCube β h).pullback (Over.map (face3 j e)) =
      comparisonValue β h (terminalPoint ⟨2⟩) (faceAxis j e 0) (faceAxis j e 1) (faceAxis j e 2) := by
  have q := comparisonValue_map β h (faceRestriction j e) ⟨cubeAxis 0⟩ ⟨cubeAxis 1⟩ ⟨cubeAxis 2⟩
  have v := congrArg₂ (fun r st => comparisonValue β h (terminalPoint ⟨2⟩) r st.1 st.2)
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

theorem comparisonCube_root (h : Term (SecondIdentityFamily terminal.{0})) (e : Bool) :
    (comparisonCube β h).pullback (Over.map (face3 0 e)) = comparisonRootSquare β := by
  have q := comparisonCube_face β h 0 e
  simp only [faceAxis00,faceAxis01,faceAxis02] at q
  exact q.trans (comparisonValue_root β h (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩ e)

theorem comparisonCube_start (h : Term (SecondIdentityFamily terminal.{0})) :
    (comparisonCube β h).pullback (Over.map (face3 1 false)) = actionSquare (t := t) h := by
  have q := comparisonCube_face β h 1 false
  simp only [faceAxis10,faceAxis11,faceAxis12] at q
  exact q.trans (comparisonValue_start β h (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩)

theorem comparisonCube_finish (h : Term (SecondIdentityFamily terminal.{0})) :
    (comparisonCube β h).pullback (Over.map (face3 1 true)) = secondSquare h := by
  have q := comparisonCube_face β h 1 true
  simp only [faceAxis10,faceAxis11,faceAxis12] at q
  exact q.trans (comparisonValue_finish β h (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩)

theorem comparisonCube_side (h : Term (SecondIdentityFamily terminal.{0})) (e : Bool) :
    (comparisonCube β h).pullback (Over.map (face3 2 e)) = zeroCocycle (Over (⟨2⟩ : Cube)) := by
  have q := comparisonCube_face β h 2 e
  simp only [faceAxis20,faceAxis21,faceAxis22] at q
  exact q.trans (comparisonValue_side β h (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩ e)

include β in
/-- Opposite endpoint comparisons cancel with their actual orientations in the cubical boundary. -/
theorem actionSquare_observation (h : Term (SecondIdentityFamily terminal.{0})) :
    observeSquare (actionSquare (t := t) h) = secondObservation h := by
  have e := observeSquare_stokes (comparisonCube β h)
  rw [comparisonCube_root β h false,comparisonCube_root β h true,
    comparisonCube_start β h,comparisonCube_finish β h,
    comparisonCube_side β h false,comparisonCube_side β h true,observeSquare_zero] at e
  change observeSquare (actionSquare (t := t) h) = observeSquare (secondSquare h)
  omega

end SquareKit.Cubical.CategoryCocycles
