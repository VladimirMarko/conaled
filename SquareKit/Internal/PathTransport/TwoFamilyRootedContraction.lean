import SquareKit.Internal.PathTransport.TwoFamilyRootedContractionDirect
import SquareKit.Internal.PathTransport.TwoStrongPrecomposition
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
variable (x : Section F)
theorem rootedRetraction_direct :
    (familyCast (rootedPathFamily_direct F x)).comp (rootedRetractionDirect F x) = rootedRetraction F x := by
  unfold rootedRetractionDirect rootedRetraction
  rw [← strictFunctor_comp_assoc, familyCast_projection]

theorem rootedContraction_source :
    ((familyCast (rootedPathFamily_direct F x)).comp (rootedDirectRetract F x)).comp
      (familyCast (rootedPathFamily_direct F x).symm) =
      (rootedRetraction F x).comp (rootedReflexivity F x) := by
  unfold rootedDirectRetract rootedReflexivity
  rw [← strictFunctor_comp_assoc (familyCast _), rootedRetraction_direct, strictFunctor_comp_assoc]
theorem rootedContraction_target :
    ((familyCast (rootedPathFamily_direct F x)).comp (StrictPseudofunctor.id _)).comp
      (familyCast (rootedPathFamily_direct F x).symm) = StrictPseudofunctor.id _ := by
  rw [strictFunctor_comp_id, familyCast_comp]
  rfl
noncomputable def rootedContraction : Pseudofunctor.StrongTrans
    ((rootedRetraction F x).comp (rootedReflexivity F x)).toPseudofunctor
    (StrictPseudofunctor.id (Total (rootedPathFamily F x))).toPseudofunctor :=
  strongCast (rootedContraction_source F x) (rootedContraction_target F x)
    (strongPostcomp (strongPrecomp (rootedContractionDirect F x) (familyCast (rootedPathFamily_direct F x)))
      (familyCast (rootedPathFamily_direct F x).symm))
theorem rootedContraction_heq : HEq (rootedContraction F x)
    (strongPostcomp (strongPrecomp (rootedContractionDirect F x) (familyCast (rootedPathFamily_direct F x)))
      (familyCast (rootedPathFamily_direct F x).symm)) := strongCast_heq _ _ _
end SquareKit.Internal.PathTransport.TwoFamily
