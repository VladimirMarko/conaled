import SquareKit.Internal.Cubical.CocycleSourceConjugationValues
import SquareKit.Internal.Cubical.CocycleEndpointComparison

/-! A six-face conjugation cube whose action face is the actual source J-action. -/
noncomputable section
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

variable {t : Term (reindex (FirstIdentityFamily terminal.{0}) (projection (FirstIdentityFamily terminal.{0}))) }
variable (β : Term (normalizedIdentity (reindex (FirstIdentityFamily terminal.{0}) (projection (FirstIdentityFamily terminal.{0})))
  t (generic (FirstIdentityFamily terminal.{0}))))

variable (h : Term (SecondIdentityFamily terminal.{0}))
variable (a : Term (LoopSquareFamily (mappedPoint t)))
variable (H : Term (normalizedIdentity (LoopSquareFamily (mappedPoint t)) a (mappedHigher t h)))

def sourceConjugationCube : CubeCocycle (⟨3⟩ : Cube) :=
  sourceConjugationValue β h a H (terminalPoint ⟨3⟩) ⟨cubeAxis 0⟩ ⟨cubeAxis 1⟩ ⟨cubeAxis 2⟩

def sourceActionSquare : CubeCocycle (⟨2⟩ : Cube) :=
  loopSquareValue a (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩

private theorem sourceConjugationCube_face (j : Fin 3) (e : Bool) :
    (sourceConjugationCube β h a H).pullback (Over.map (face3 j e)) =
      sourceConjugationValue β h a H (terminalPoint ⟨2⟩) (faceAxis j e 0) (faceAxis j e 1) (faceAxis j e 2) := by
  have q := sourceConjugationValue_map β h a H (faceRestriction j e) ⟨cubeAxis 0⟩ ⟨cubeAxis 1⟩ ⟨cubeAxis 2⟩
  have v := congrArg₂ (fun r st => sourceConjugationValue β h a H (terminalPoint ⟨2⟩) r st.1 st.2)
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

theorem sourceConjugationCube_root (e : Bool) :
    (sourceConjugationCube β h a H).pullback (Over.map (face3 0 e)) = comparisonRootSquare β := by
  have q := sourceConjugationCube_face β h a H 0 e
  simp only [faceAxis00,faceAxis01,faceAxis02] at q
  exact q.trans (sourceConjugationValue_root β h a H (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩ e)

theorem sourceConjugationCube_start :
    (sourceConjugationCube β h a H).pullback (Over.map (face3 1 false)) = sourceActionSquare a := by
  have q := sourceConjugationCube_face β h a H 1 false
  simp only [faceAxis10,faceAxis11,faceAxis12] at q
  exact q.trans (sourceConjugationValue_start β h a H (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩)

theorem sourceConjugationCube_finish :
    (sourceConjugationCube β h a H).pullback (Over.map (face3 1 true)) = secondSquare h := by
  have q := sourceConjugationCube_face β h a H 1 true
  simp only [faceAxis10,faceAxis11,faceAxis12] at q
  exact q.trans (sourceConjugationValue_finish β h a H (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩)

theorem sourceConjugationCube_side (e : Bool) :
    (sourceConjugationCube β h a H).pullback (Over.map (face3 2 e)) = zeroCocycle (Over (⟨2⟩ : Cube)) := by
  have q := sourceConjugationCube_face β h a H 2 e
  simp only [faceAxis20,faceAxis21,faceAxis22] at q
  exact q.trans (sourceConjugationValue_side β h a H (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩ e)

include β H in
/-- Opposite endpoint comparisons cancel with their actual orientations in the cubical boundary. -/
theorem sourceActionSquare_observation :
    observeSquare (sourceActionSquare a) = secondObservation h := by
  have e := observeSquare_stokes (sourceConjugationCube β h a H)
  rw [sourceConjugationCube_root β h a H false,sourceConjugationCube_root β h a H true,
    sourceConjugationCube_start β h a H,sourceConjugationCube_finish β h a H,
    sourceConjugationCube_side β h a H false,sourceConjugationCube_side β h a H true,observeSquare_zero] at e
  change observeSquare (sourceActionSquare a) = observeSquare (secondSquare h)
  omega

end SquareKit.Cubical.CategoryCocycles
