import SquareKit.Internal.PathTransport.TwoFamilyVerticalValueAt
import SquareKit.Internal.PathTransport.TwoFamilySectionValueFormula
import SquareKit.Internal.PathTransport.TwoFamilyIdentityValueFormula
import SquareKit.Internal.PathTransport.TwoFamilyIdentitySectionCell
import SquareKit.Internal.PathTransport.TwoFamilyEndpointFiberAction
/-! A retained vertical source value agrees with the corresponding identity-fiber action. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ : Context.{u}}
def VerticalValueAction (F : Family Γ) (p q : TwoFamily.Section F.data)
 (s : TwoFamily.Section (reindex (projectionHigher F.data) F.data))
 (k : TwoFamily.Section (closedId F.data p q) → StrictPseudofunctor Γ (Total (rootedPathFamily F.data p)))
 (G : Family Γ) (v : TwoFamily.Section (closedId F.data p q) → TwoFamily.Section G.data) : Prop := ∀ h,
 VerticalValueAt F p s (k h) G (v h)
variable {Γ : Context.{u}} (A : Family Γ) (x y : TwoFamily.Section A.data)
local notation "I" => A.identity x y
def IdentityFiberValueFormula
 (p q : TwoFamily.Section (I).data)
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data))
 (G : Family Γ) (v : TwoFamily.Section (closedId (I).data p q) → TwoFamily.Section G.data) : Prop := ∀ h γ,
 IdentityValueAction ((v h).normalObj G.data γ).fiber
 ((identityFiberFunctor A x y γ s).map
  (identitySectionCell A x y p q h γ))
private theorem ld_mk_heq {X Y : Type u} {a : X} {b : Y} (h : HEq a b) :
 HEq (LocallyDiscrete.mk a) (LocallyDiscrete.mk b) := by
 cases type_eq_of_heq h
 cases eq_of_heq h
 rfl
theorem identityFiberValueFormula_of_vertical
 (p q : TwoFamily.Section (I).data)
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data))
 (k : TwoFamily.Section (closedId (I).data p q) → StrictPseudofunctor Γ (Total (rootedPathFamily (I).data p)))
 (G : Family Γ) (v : TwoFamily.Section (closedId (I).data p q) → TwoFamily.Section G.data)
 (hf : EndpointIdentityFiberAction A x y p q s k)
 (hv : VerticalValueAction I p q s k G v) :
 IdentityFiberValueFormula A x y p q s G v := by
 intro h γ
 have h1 := hv h γ
 have h2 := hf h γ
 run_tac Lean.Elab.Tactic.withMainContext do
  let h1 := (← Lean.Meta.getLocalDeclFromUserName `h1).toExpr
  let h2 := (← Lean.Meta.getLocalDeclFromUserName `h2).toExpr
  let t1 ← Lean.Meta.whnf (← Lean.Meta.inferType h1)
  let t2 ← Lean.Meta.whnf (← Lean.Meta.inferType h2)
  let a := t1.getAppArgs
  let b := t2.getAppArgs
  let h3 := Lean.mkAppN (Lean.mkConst ``ld_mk_heq [Lean.Level.param `u]) #[b[0]!, b[2]!, b[1]!, b[3]!, h2]
  let t3 ← Lean.Meta.inferType h3
  let c := t3.getAppArgs
  let proof := Lean.mkAppN (Lean.mkConst ``HEq.trans t1.getAppFn.constLevels!) #[a[0]!, a[2]!, c[2]!, a[1]!, a[3]!, c[3]!, h1, h3]
  (← Lean.Elab.Tactic.getMainGoal).assign proof
  Lean.Elab.Tactic.replaceMainGoal []
end SquareKit.Internal.PathTransport.HigherInterpretation
