import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroupCells
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ uB vB wB
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))
theorem sigmaRegroupCell_injective {x y : Total (sigmaFamily F B)} {p q : x ⟶ y} :
    Function.Injective (sigmaRegroupCell F B (p := p) (q := q)) := by
  intro α β h
  have hb := congrArg (fun τ => τ.base.base) h
  have hfirst := congrArg (fun τ => τ.base) h
  have hsecond := congr_arg_heq (fun τ => τ.fiber) h
  have hf := (sigmaRegroupCell_fiber_heq F B α).symm.trans
    (hsecond.trans (sigmaRegroupCell_fiber_heq F B β))
  rcases α with ⟨a,u⟩
  rcases β with ⟨b,v⟩
  change a = b at hb
  cases hb
  have huvbase : u.base = v.base := eq_of_heq (congr_arg_heq (fun τ => τ.fiber) hfirst)
  have huv : u = v := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ huvbase
    exact eq_of_heq (hf.trans (comp_eqToHom_heq _ _).symm)
  cases huv
  rfl
end SquareKit.Internal.PathTransport.TwoFamily
