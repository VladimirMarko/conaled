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
variable (s t : Section F)
theorem closedId_map_obj {a b : Γ} (f : a ⟶ b) (p : (closedId F s t).obj a) :
 (((closedId F s t).map f).obj p).as =
 inv (s.normalMap F f).fiber ≫ (F.map f).map p.as ≫ (t.normalMap F f).fiber := rfl
end SquareKit.Internal.PathTransport.TwoFamily
