import SquareKit.Internal.PathTransport.TwoFamilyMapComposition
import SquareKit.Internal.PathTransport.TwoStrongInverseCancellation
import SquareKit.Internal.PathTransport.TwoFamilyContractionInverse
import SquareKit.Internal.PathTransport.TwoFamilyCoherentLift
import SquareKit.Internal.PathTransport.TwoFamilyHigherReindexLaws
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 2000
universe u v w uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ]
variable (E : Family.{u,v,w,uE,vE,wE} Γ)

variable {F G F' G' : Family.{u,v,w,uE,vE,wE} Γ}
theorem strongMap_heq (e : F = F') (e' : G = G')
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (θ : Pseudofunctor.StrongTrans F'.toPseudofunctor G'.toPseudofunctor)
    (h : HEq η θ) : HEq (StrongMap.toHigher η) (StrongMap.toHigher θ) := by
  cases e
  cases e'
  cases eq_of_heq h
  rfl

private theorem total_comp_congr {A B : Type*} [Bicategory A] [Bicategory B]
    (e : F = G) (H : StrictPseudofunctor A (Total F)) (H' : StrictPseudofunctor A (Total G))
    (K : StrictPseudofunctor (Total F) B) (K' : StrictPseudofunctor (Total G) B)
    (hH : HEq H H') (hK : HEq K K') : H.comp K = H'.comp K' := by
  cases e
  cases eq_of_heq hH
  cases eq_of_heq hK
  rfl

variable [IsLocallyGroupoid Γ] (R : StrictPseudofunctor Γ Γ)
variable (η : Pseudofunctor.StrongTrans R.toPseudofunctor
  (StrictPseudofunctor.id Γ).toPseudofunctor) [∀x, IsIso (η.app x)]
theorem coherentLiftRight_normalize : coherentLiftRight η E =
    StrongMap.toHigher (forwardFamilyContraction R η E) := by
  have h : HEq (strongPostcomp η E) (forwardFamilyContraction R η E) := by
    exact (forwardFamilyContraction_heq R η E).symm
  have hc := total_comp_congr (StrictTwoTransformation.functor_id_comp E)
    (StrongMap.toHigher (strongPostcomp η E))
    (StrongMap.toHigher (forwardFamilyContraction R η E))
    (reindexHigher E (StrictPseudofunctor.id Γ)) (StrictPseudofunctor.id (Total E))
    (strongMap_heq rfl (StrictTwoTransformation.functor_id_comp E) _ _ h)
    (reindexHigher_id_heq E)
  exact hc.trans (StrictTwoTransformation.functor_comp_id _)

variable [∀ γ, IsLocallyGroupoid (E.obj γ)]
theorem contractionBack_forward :
    (contractionBack R η E).comp (StrongMap.toHigher (forwardFamilyContraction R η E)) =
      StrictPseudofunctor.id (Total E) := by
  change (StrongMap.toHigher (strongInverse (forwardFamilyContraction R η E))).comp
    (StrongMap.toHigher (forwardFamilyContraction R η E)) = _
  rw [StrongMap.toHigher_vcomp, strongInverse_vcomp, StrongMap.toHigher_id]

def castStrongFunctorTarget {A B : Type*} [Bicategory A] [Bicategory B]
    {F G G' : StrictPseudofunctor A B} (e : G = G')
    (θ : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor) :
    Pseudofunctor.StrongTrans F.toPseudofunctor G'.toPseudofunctor := by
  cases e
  exact θ

theorem contractionLift_target :
    (contractionBack R η E).comp (coherentLiftRight η E) =
      StrictPseudofunctor.id (Total E) := by
  rw [coherentLiftRight_normalize E R η]
  exact contractionBack_forward E R η

noncomputable def liftedContraction :
    Pseudofunctor.StrongTrans (contractionLift R η E).toPseudofunctor
      (StrictPseudofunctor.id (Total E)).toPseudofunctor :=
  castStrongFunctorTarget (contractionLift_target E R η)
    (strongPrecomp (coherentLift η E) (contractionBack R η E))


end SquareKit.Internal.PathTransport.TwoFamily
