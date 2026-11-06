import SquareKit.Internal.Cubical.CocycleActionBridgeValues
import SquareKit.Internal.Cubical.CocycleAdditiveComposition

/-! Paste the typed action comparison with the actual beta homotopy, retaining every boundary. -/
noncomputable section
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf
variable {Γ : Context.{0}}
variable {t : Term (reindex (FirstIdentityFamily Γ) (projection (FirstIdentityFamily Γ)))}
variable (β : Term (normalizedIdentity (reindex (FirstIdentityFamily Γ) (projection (FirstIdentityFamily Γ)))
  t (generic (FirstIdentityFamily Γ))))
variable (h : Term (SecondIdentityFamily Γ)) (a : Term (LoopSquareFamily (mappedPoint t)))
variable (H : Term (normalizedIdentity (LoopSquareFamily (mappedPoint t)) a (mappedHigher t h)))

def sourceConjugationValue (x : Γ.Elements) (r s z : (interval Γ).obj x) : CubeCocycle x.obj.unop :=
  pasteCocycle (bridgeValue H x r s z) (comparisonValue β h x r s z)
    (loopSquareValue (mappedHigher t h) x r z)

theorem sourceConjugationValue_map {x y : Γ.Elements} (f : x ⟶ y)
    (r s z : (interval Γ).obj x) :
    cocycles.map f.hom (sourceConjugationValue β h a H x r s z) =
      sourceConjugationValue β h a H y ((interval Γ).map f r) ((interval Γ).map f s) ((interval Γ).map f z) := by
  have q := pasteCocycle_pullback (bridgeValue H x r s z) (comparisonValue β h x r s z)
    (loopSquareValue (mappedHigher t h) x r z) (Over.map f.hom.unop)
  have e := congrArg₂ (fun (p : CubeCocycle y.obj.unop) (qs : CubeCocycle y.obj.unop × CubeCocycle y.obj.unop) =>
    pasteCocycle p qs.1 qs.2) (bridgeValue_map H f r s z)
    (congrArg₂ Prod.mk (comparisonValue_map β h f r s z) (loopSquareValue_map (mappedHigher t h) f r z))
  run_tac Lean.Elab.Tactic.withMainContext do
    let l ← Lean.Meta.getLocalDeclFromUserName `q
    let r ← Lean.Meta.getLocalDeclFromUserName `e
    let tl ← Lean.Meta.whnf l.type
    let tr ← Lean.Meta.whnf r.type
    let #[α,a,b] := tl.getAppArgs | throwError "expected equality"
    let #[_,_,c] := tr.getAppArgs | throwError "expected equality"
    let .const _ levels := tl.getAppFn | throwError "expected equality level"
    (← Lean.Elab.Tactic.getMainGoal).assign
      (Lean.mkAppN (Lean.mkConst ``Eq.trans levels) #[α,a,b,c,l.toExpr,r.toExpr])
    Lean.Elab.Tactic.replaceMainGoal []

theorem sourceConjugationValue_start (x : Γ.Elements) (r z : (interval Γ).obj x) :
    sourceConjugationValue β h a H x r ((endpoint Γ false).val x) z = loopSquareValue a x r z := by
  unfold sourceConjugationValue
  rw [bridgeValue_start,comparisonValue_start,mappedHigher_value]
  exact pasteCocycle_left _ _

theorem sourceConjugationValue_finish (x : Γ.Elements) (r z : (interval Γ).obj x) :
    sourceConjugationValue β h a H x r ((endpoint Γ true).val x) z = secondValue h x r z := by
  unfold sourceConjugationValue
  rw [bridgeValue_finish,comparisonValue_finish]
  exact pasteCocycle_right _ _

theorem sourceConjugationValue_root (x : Γ.Elements) (s z : (interval Γ).obj x) (e : Bool) :
    sourceConjugationValue β h a H x ((endpoint Γ e).val x) s z = comparisonRootValue β x s z := by
  unfold sourceConjugationValue
  rw [bridgeValue_root,comparisonValue_root]
  change pasteCocycle _ _ (loopSquareElementValue ((mappedHigher t h).val x) _ _) = _
  rw [loopSquareElementValue_root]
  exact pasteCocycle_right _ _

theorem sourceConjugationValue_side (x : Γ.Elements) (r s : (interval Γ).obj x) (e : Bool) :
    sourceConjugationValue β h a H x r s ((endpoint Γ e).val x) = zeroCocycle (Over x.obj.unop) := by
  unfold sourceConjugationValue
  rw [bridgeValue_side,comparisonValue_side]
  change pasteCocycle _ _ (loopSquareElementValue ((mappedHigher t h).val x) _ _) = _
  rw [loopSquareElementValue_side]
  exact pasteCocycle_left _ _

end SquareKit.Cubical.CategoryCocycles
