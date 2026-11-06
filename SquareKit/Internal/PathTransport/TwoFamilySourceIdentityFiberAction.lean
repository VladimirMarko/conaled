import SquareKit.Internal.PathTransport.TwoFamilyOrdinarySourceAction
import SquareKit.Internal.PathTransport.TwoFamilyOrdinaryActionFunctions
import SquareKit.Internal.PathTransport.TwoFamilyIdentityFiberValueAction
import SquareKit.Internal.PathTransport.TwoFamilySourceEndpointFiberAction
/-! The actual source ordinary action induces the retained identity-fiber action. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) {Γ : Context.{u}}
local notation "M" => fullModel C D
def SourceOrdinaryVerticalAction (A : Family Γ) (p q : TwoFamily.Section A.data)
 (s : TwoFamily.Section (reindex (projectionHigher A.data) A.data)) : Prop :=
 VerticalValueAction A p q s (endpointSub_native C D A p q)
  (ordinaryActionFamily C D A p q s) (fun h => (ordinaryApValue M A A ⟨s⟩ ⟨p⟩ ⟨q⟩ ⟨h⟩).down)
theorem sourceOrdinaryVerticalAction (A : Family Γ) (p q : TwoFamily.Section A.data)
 (s : TwoFamily.Section (reindex (projectionHigher A.data) A.data))
 [∀ γ, Subsingleton (A.data.obj γ)] :
 SourceOrdinaryVerticalAction C D A p q s := by
 intro h
 have hv := ordinaryApValue_vertical_action C D A ⟨s⟩ ⟨p⟩ ⟨q⟩ ⟨h⟩
 run_tac Lean.Elab.Tactic.withMainContext do
  let hv ← Lean.Meta.getLocalDeclFromUserName `hv
  (← Lean.Elab.Tactic.getMainGoal).assign hv.toExpr
  Lean.Elab.Tactic.replaceMainGoal []

def SourceIdentityFiberAction (A : Family Γ) (x y : TwoFamily.Section A.data)
 (p q : TwoFamily.Section (A.identity x y).data)
 (s : TwoFamily.Section (reindex (projectionHigher (A.identity x y).data) (A.identity x y).data)) : Prop :=
 IdentityFiberValueFormula A x y p q s
  (ordinaryActionFamily C D (A.identity x y) p q s)
  (fun h => (ordinaryApValue M (A.identity x y) (A.identity x y) ⟨s⟩ ⟨p⟩ ⟨q⟩ ⟨h⟩).down)
theorem sourceIdentityFiberAction (A : Family Γ) (x y : TwoFamily.Section A.data)
 (p q : TwoFamily.Section (A.identity x y).data)
 (s : TwoFamily.Section (reindex (projectionHigher (A.identity x y).data) (A.identity x y).data))
 [∀ γ, Subsingleton ((A.identity x y).data.obj γ)] :
 SourceIdentityFiberAction C D A x y p q s := by
 have hf := endpointSub_fiber_action C D A x y p q s
 have hv := sourceOrdinaryVerticalAction C D (A.identity x y) p q s
 have f := identityFiberValueFormula_of_vertical A x y p q s
  (endpointSub_native C D (A.identity x y) p q)
  (ordinaryActionFamily C D (A.identity x y) p q s)
  (fun h => (ordinaryApValue M (A.identity x y) (A.identity x y) ⟨s⟩ ⟨p⟩ ⟨q⟩ ⟨h⟩).down)
 run_tac Lean.Elab.Tactic.withMainContext do
  let f := (← Lean.Meta.getLocalDeclFromUserName `f).toExpr
  let hf := (← Lean.Meta.getLocalDeclFromUserName `hf).toExpr
  let hv := (← Lean.Meta.getLocalDeclFromUserName `hv).toExpr
  (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkAppN f #[hf, hv])
  Lean.Elab.Tactic.replaceMainGoal []
end SquareKit.Internal.PathTransport.HigherInterpretation
