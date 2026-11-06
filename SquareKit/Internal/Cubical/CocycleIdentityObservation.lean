import SquareKit.Internal.Cubical.CocycleSecondEvaluation
import SquareKit.Internal.Cubical.CocycleSquareHomotopy
import SquareKit.Internal.Cubical.IdentityEvaluation

/-! The integer observation reads the selected square from normalized identity data. -/
noncomputable section
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

abbrev SecondIdentityFamily (Γ : Context.{0}) :=
  normalizedIdentity (normalizedIdentity (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ))
    (normalizedIdentityRefl (zeroTerm Γ)) (normalizedIdentityRefl (zeroTerm Γ))

noncomputable def secondElementValue {Γ : Context.{0}} {x : Γ.Elements}
    (p : (SecondIdentityFamily Γ).obj x) (r s : (interval Γ).obj x) : CubeCocycle x.obj.unop :=
  (p.eval r).eval s

noncomputable def secondValue {Γ : Context.{0}} (t : Term (SecondIdentityFamily Γ))
    (x : Γ.Elements) (r s : (interval Γ).obj x) : CubeCocycle x.obj.unop :=
  secondElementValue (t.val x) r s

set_option backward.isDefEq.respectTransparency false in
theorem secondValue_selected (Γ : Context.{0}) (x : Γ.Elements) (r s : (interval Γ).obj x) :
    secondValue (secondIdentity Γ) x r s = squareValue r.down s.down := by
  have h := LocalIdentity.fromLocal_toLocal ((secondIdentityRaw Γ).val x)
  have hp : ((secondIdentityRaw Γ).val x).path.val.val (𝟙 x) r =
      (secondIdentityBody Γ).val (extendObj (interval Γ) x r) := rfl
  have he := congrArg (fun p : LocalIdentity (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ) x =>
    p.fromLocal.path.val.val (𝟙 x) s) hp
  have h₁ := congrArg (fun p : IdentityElement
      (normalizedIdentity (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ))
      (normalizedIdentityRefl (zeroTerm Γ)) (normalizedIdentityRefl (zeroTerm Γ)) x =>
    (p.path.val.val (𝟙 x) r).fromLocal.path.val.val (𝟙 x) s) h
  have h₂ := secondIdentityBody_eval Γ x r s
  run_tac Lean.Elab.Tactic.withMainContext do
    let first ← Lean.Meta.getLocalDeclFromUserName `h₁
    let middle ← Lean.Meta.getLocalDeclFromUserName `he
    let last ← Lean.Meta.getLocalDeclFromUserName `h₂
    let tf ← Lean.Meta.whnf first.type
    let tm ← Lean.Meta.whnf middle.type
    let tl ← Lean.Meta.whnf last.type
    let #[α,a,b] := tf.getAppArgs | throwError "expected equality"
    let #[_,_,c] := tm.getAppArgs | throwError "expected equality"
    let #[_,_,d] := tl.getAppArgs | throwError "expected equality"
    let .const _ levels := tf.getAppFn | throwError "expected equality level"
    let tail := Lean.mkAppN (Lean.mkConst ``Eq.trans levels) #[α,b,c,d,middle.toExpr,last.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign
      (Lean.mkAppN (Lean.mkConst ``Eq.trans levels) #[α,a,b,d,first.toExpr,tail])
    Lean.Elab.Tactic.replaceMainGoal []

def terminalPoint (I : Cube) : terminal.{0}.Elements := terminal.elementsMk (Opposite.op I) PUnit.unit

def squareAxis (k : Fin 2) : (⟨2⟩ : Cube) ⟶ (⟨1⟩ : Cube) := Cube.ofRaw (fun _ => Expr.var k)

private theorem squareAxes_pair : Cube.pair (squareAxis 1) (squareAxis 0) = 𝟙 (⟨2⟩ : Cube) := by
  apply congrArg (@Cube.ofRaw ⟨2⟩ ⟨2⟩)
  decide

noncomputable def secondSquare (t : Term (SecondIdentityFamily terminal.{0})) : CubeCocycle (⟨2⟩ : Cube) :=
  secondValue t (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩

noncomputable def secondObservation (t : Term (SecondIdentityFamily terminal.{0})) : ℤ :=
  observeSquare (secondSquare t)

theorem secondSquare_selected : secondSquare (secondIdentity terminal.{0}) = squareCocycle := by
  refine (secondValue_selected terminal (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩).trans ?_
  exact (congrArg (fun f : (⟨2⟩ : Cube) ⟶ (⟨2⟩ : Cube) => cocycles.map f.op squareCocycle)
    squareAxes_pair).trans (cocycles.map_id_apply _ _)

theorem secondObservation_selected : secondObservation (secondIdentity terminal.{0}) = 1 :=
  (congrArg observeSquare secondSquare_selected).trans observeSquare_witness

end SquareKit.Cubical.CategoryCocycles
