import SquareKit.Internal.PathTransport.TwoFamilyClosedComparison
import SquareKit.Internal.PathTransport.TwoFamilyRootedComponent
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)]
variable (s t : Section F) (p : Section (closedId F s t))
theorem closedComparison_app (z : Γ) : HEq ((closedComparison F s t p).app z)
 ((pathSecond F).map ((pathContraction F).app ((closedSectionEmbedding F s t p).obj z))) := by
 have h := strongTrans_app_heq (closedComparison_source F s t p).symm (closedComparison_target F s t p).symm
  (closedComparison F s t p)
  (strongPostcomp (strongPrecomp (pathContraction F) (closedSectionEmbedding F s t p)) (pathSecond F))
  (closedComparison_heq F s t p) z
 run_tac Lean.Elab.Tactic.withMainContext do
  let d ← Lean.Meta.getLocalDeclFromUserName `h
  (← Lean.Elab.Tactic.getMainGoal).assign d.toExpr
  Lean.Elab.Tactic.replaceMainGoal []
theorem closedComparison_app_fiber (z : Γ) :
 HEq ((closedComparison F s t p).app z).fiber (p.lift.obj z).fiber.as := by
 have h1 := total_hom_fiber_heq_family (F := F) (G := F) rfl
  (heq_of_eq (congrArg (fun H => H.obj z) (closedComparison_source F s t p).symm))
  (heq_of_eq (congrArg (fun H => H.obj z) (closedComparison_target F s t p).symm))
  (closedComparison_app F s t p z)
 have h2 := pathContraction_app_second_fiber F ((closedSectionEmbedding F s t p).obj z)
 exact HEq.trans h1 h2
theorem closedComparison_app_fiber_normal (z : Γ) :
 HEq ((closedComparison F s t p).app z).fiber (p.normalObj (closedId F s t) z).fiber.as := by
 have h := closedComparison_app_fiber F s t (p.normalized (closedId F s t)) z
 have e := congr_arg_heq (fun q => ((closedComparison F s t q).app z).fiber) (p.normalized_eq (closedId F s t))
 exact HEq.trans (HEq.symm e) h
def ClosedComparisonComponentFormula
 (β : Pseudofunctor.StrongTrans s.lift.toPseudofunctor t.lift.toPseudofunctor) : Prop :=
 ∀ z, HEq (β.app z).fiber (p.normalObj (closedId F s t) z).fiber.as
theorem closedComparison_components :
 ClosedComparisonComponentFormula F s t p (closedComparison F s t p) :=
 closedComparison_app_fiber_normal F s t p
end SquareKit.Internal.PathTransport.TwoFamily
