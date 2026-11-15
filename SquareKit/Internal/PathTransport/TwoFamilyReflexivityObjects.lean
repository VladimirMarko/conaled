import SquareKit.Internal.PathTransport.TwoFamilyTransportObjects
import SquareKit.Internal.PathTransport.TwoFamilyClosedIdentity
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
theorem closedReflexivity_normalObj (s : Section F) (γ : Γ) :
 ((closedReflexivity F s).normalObj (closedId F s s) γ).fiber =
  (show LocallyDiscrete ((s.normalObj F γ).fiber ⟶ (s.normalObj F γ).fiber) from ⟨𝟙 _⟩) := by
 rw [← s.normalized_eq F]
 apply eq_of_heq
 exact ((closedReflexivity F (s.normalized F)).normalObj_fiber_heq _ γ).trans
  (closedReflexivity_obj F (s.normalized F) γ)
end SquareKit.Internal.PathTransport.TwoFamily
