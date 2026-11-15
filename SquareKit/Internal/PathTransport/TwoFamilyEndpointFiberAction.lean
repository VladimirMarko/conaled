import SquareKit.Internal.PathTransport.TwoFamilyOrdinaryEndpointFiberAction
import SquareKit.Internal.PathTransport.TwoFamilyPairLiftObjects
/-! Endpoint data determines the action of a section on the retained identity-fiber arrow. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ : Context.{u}}
theorem normal_projection (A : Family Γ) (p q : TwoFamily.Section A.data)
 (k : StrictPseudofunctor Γ (Total (rootedPathFamily A.data p)))
 (hk : k.comp (projectionHigher (rootedPathFamily A.data p)) = q.lift) (γ : Γ) :
 (k.obj γ).base = q.normalObj A.data γ := by
 have e := congrArg (fun f => f.obj γ) hk
 exact e.trans (q.normalObj_eq A.data γ).symm

variable (A : Family Γ) (x y : TwoFamily.Section A.data)
local notation "I" => A.identity x y
def RootedIdentityFiberAction
 (p q : TwoFamily.Section (I).data)
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data))
 (γ : Γ) (z : Total (rootedPathFamily (I).data p))
 (h : (p.normalObj (I).data γ).fiber ⟶ (q.normalObj (I).data γ).fiber) : Prop :=
 HEq (s.lift.map ((fiberInclusion (I).data z.base.base).map z.fiber.as)).fiber
 (Discrete.mk ((identityFiberFunctor A x y γ s).map h.as))
def EndpointIdentityFiberAction
 (p q : TwoFamily.Section (I).data)
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data))
 (k : TwoFamily.Section (closedId (I).data p q) → StrictPseudofunctor Γ (Total (rootedPathFamily (I).data p))) : Prop :=
 ∀ h γ, RootedIdentityFiberAction A x y p q s γ ((k h).obj γ)
 (h.normalObj (closedId (I).data p q) γ).fiber.as
theorem endpointIdentityFiberAction_of_projection
 (p q : TwoFamily.Section (I).data)
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data))
 (k : TwoFamily.Section (closedId (I).data p q) → StrictPseudofunctor Γ (Total (rootedPathFamily (I).data p)))
 (hk : ∀ h, (k h).comp (projectionHigher (rootedPathFamily (I).data p)) = q.lift)
 (hf : PairLiftFiberFormula (rootedPathFamily (I).data p) (closedId (I).data p q) k) :
 EndpointIdentityFiberAction A x y p q s k := by
 intro h γ
 have he := normal_projection I p q (k h) (hk h) γ
 have ht := rooted_identity_fiber_action A x y p q s γ _
   (h.normalObj (closedId (I).data p q) γ).fiber.as he (hf h γ)
 run_tac Lean.Elab.Tactic.withMainContext do
   let ht := (← Lean.Meta.getLocalDeclFromUserName `ht).toExpr
   (← Lean.Elab.Tactic.getMainGoal).assign ht
   Lean.Elab.Tactic.replaceMainGoal []
end SquareKit.Internal.PathTransport.HigherInterpretation
