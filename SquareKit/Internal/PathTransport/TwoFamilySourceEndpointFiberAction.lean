import SquareKit.Internal.PathTransport.TwoFamilyEndpointFiberAction
import SquareKit.Internal.PathTransport.TwoFamilyModelEndpointObjects
/-! The source endpoint substitution retains the exact arrow used by the native fiber action. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) {Γ : Context.{u}}
noncomputable def endpointSub_native (A : Family Γ) (p q : TwoFamily.Section A.data)
 (h : TwoFamily.Section (closedId A.data p q)) :
 StrictPseudofunctor Γ (Total (rootedPathFamily A.data p)) :=
 ((structuralModel C D).endpointSub A ⟨p⟩ ⟨q⟩ ⟨h⟩).down
theorem endpointSub_native_projection (A : Family Γ) (p q : TwoFamily.Section A.data)
 (h : TwoFamily.Section (closedId A.data p q)) :
 (endpointSub_native C D A p q h).comp (projectionHigher (rootedPathFamily A.data p)) = q.lift := by
 have ht := endpointSub_projection C D A ⟨p⟩ ⟨q⟩ ⟨h⟩
 run_tac Lean.Elab.Tactic.withMainContext do
  let ht := (← Lean.Meta.getLocalDeclFromUserName `ht).toExpr
  (← Lean.Elab.Tactic.getMainGoal).assign ht
  Lean.Elab.Tactic.replaceMainGoal []
theorem endpointSub_native_objects (A : Family Γ) (p q : TwoFamily.Section A.data) :
 PairLiftFiberFormula (rootedPathFamily A.data p) (closedId A.data p q) (endpointSub_native C D A p q) := by
 have ht := endpointSub_objects C D A ⟨p⟩ ⟨q⟩
 run_tac Lean.Elab.Tactic.withMainContext do
  let ht := (← Lean.Meta.getLocalDeclFromUserName `ht).toExpr
  (← Lean.Elab.Tactic.getMainGoal).assign ht
  Lean.Elab.Tactic.replaceMainGoal []

variable (A : Family Γ) (x y : TwoFamily.Section A.data)
local notation "I" => A.identity x y
def SourceEndpointIdentityFiberAction
 (p q : TwoFamily.Section (I).data)
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data)) : Prop :=
 EndpointIdentityFiberAction A x y p q s (endpointSub_native C D I p q)
theorem endpointSub_fiber_action
 (p q : TwoFamily.Section (I).data)
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data)) :
 SourceEndpointIdentityFiberAction C D A x y p q s := by
 have ht := endpointIdentityFiberAction_of_projection A x y p q s
  (endpointSub_native C D I p q)
  (endpointSub_native_projection C D I p q)
  (endpointSub_native_objects C D I p q)
 run_tac Lean.Elab.Tactic.withMainContext do
  let ht := (← Lean.Meta.getLocalDeclFromUserName `ht).toExpr
  (← Lean.Elab.Tactic.getMainGoal).assign ht
  Lean.Elab.Tactic.replaceMainGoal []
end SquareKit.Internal.PathTransport.HigherInterpretation
