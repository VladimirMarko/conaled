import SquareKit.Internal.PathTransport.TwoFamilyClosedIdentityObjects
import SquareKit.Internal.PathTransport.TwoFamilyTransportObjects
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Strict Δ]
variable (i : StrictPseudofunctor Δ Γ) (r : StrictPseudofunctor Γ Δ)
variable (η : Pseudofunctor.StrongTrans (r.comp i).toPseudofunctor (StrictPseudofunctor.id Γ).toPseudofunctor)
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
variable (s t : Section F) (d : Section (reindex i (closedId F s t)))
def IdentityActionFormula (p : Section (closedId F s t)) : Prop :=
 ∀ z, (p.normalObj (closedId F s t) z).fiber.as =
 inv (s.normalMap F (η.app z)).fiber ≫
  (F.map (η.app z)).map (d.normalObj (reindex i (closedId F s t)) (r.obj z)).fiber.as ≫
  (t.normalMap F (η.app z)).fiber
theorem retractionJ_identityAction :
 IdentityActionFormula i r η F s t d (retractionJ i r η (closedId F s t) d) := by
 intro z
 rw [retractionJ_normalObj, closedId_map_obj]
end SquareKit.Internal.PathTransport.TwoFamily
