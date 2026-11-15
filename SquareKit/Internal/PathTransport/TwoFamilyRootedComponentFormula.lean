import SquareKit.Internal.PathTransport.TwoFamilyRootedComponent
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)] (x : Section F)
def RootedComponentFormula {H K : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))}
 (η : Pseudofunctor.StrongTrans H.toPseudofunctor K.toPseudofunctor) : Prop :=
 ∀ z, HEq ((projectionHigher (rootedPathFamily F x)).map (η.app z)).fiber z.fiber.as
theorem rootedContraction_component : RootedComponentFormula F x (rootedContraction F x) := by
 have h := rootedContraction_app_fiber F x
 run_tac Lean.Elab.Tactic.withMainContext do
  let d ← Lean.Meta.getLocalDeclFromUserName `h
  (← Lean.Elab.Tactic.getMainGoal).assign d.toExpr
  Lean.Elab.Tactic.replaceMainGoal []
omit [IsLocallyGroupoid Γ] in
theorem RootedComponentFormula.congr
 {H K H' K' : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))}
 (eH : H = H') (eK : K = K')
 (η : Pseudofunctor.StrongTrans H.toPseudofunctor K.toPseudofunctor)
 (θ : Pseudofunctor.StrongTrans H'.toPseudofunctor K'.toPseudofunctor)
 (h : HEq η θ) (hf : RootedComponentFormula F x θ) : RootedComponentFormula F x η := by
 cases eH; cases eK; cases eq_of_heq h; exact hf
def RootedBaseFormula {H K : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))}
 (η : Pseudofunctor.StrongTrans H.toPseudofunctor K.toPseudofunctor) : Prop :=
 ∀ z, HEq ((projectionHigher (rootedPathFamily F x)).map (η.app z)).base (𝟙 z.base.base)
theorem rootedContraction_base : RootedBaseFormula F x (rootedContraction F x) := by
 have h := rootedContraction_app_base F x
 run_tac Lean.Elab.Tactic.withMainContext do
  let d ← Lean.Meta.getLocalDeclFromUserName `h
  (← Lean.Elab.Tactic.getMainGoal).assign d.toExpr
  Lean.Elab.Tactic.replaceMainGoal []
omit [IsLocallyGroupoid Γ] in
theorem RootedBaseFormula.congr
 {H K H' K' : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))}
 (eH : H = H') (eK : K = K')
 (η : Pseudofunctor.StrongTrans H.toPseudofunctor K.toPseudofunctor)
 (θ : Pseudofunctor.StrongTrans H'.toPseudofunctor K'.toPseudofunctor)
 (h : HEq η θ) (hf : RootedBaseFormula F x θ) : RootedBaseFormula F x η := by
 cases eH; cases eK; cases eq_of_heq h; exact hf
end SquareKit.Internal.PathTransport.TwoFamily
