import SquareKit.Internal.PathTransport.TwoFamilyEndpointSections
import SquareKit.Internal.PathTransport.TwoStrongCast
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (E : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable {A : Type*} [Bicategory A] [Strict A]
private theorem endpoint_cell_hext {x y : Total (endpointFamily E)} {p q p' q' : x ⟶ y}
    (hp : p = p') (hq : q = q') (α : p ⟶ q) (β : p' ⟶ q')
    (h1 : HEq ((endpointProjection E true).map₂ α) ((endpointProjection E true).map₂ β))
    (h2 : HEq ((endpointProjection E false).map₂ α) ((endpointProjection E false).map₂ β)) : HEq α β := by
  cases hp; cases hq
  exact heq_of_eq (endpoint_cell_ext E _ _ (eq_of_heq h1) (eq_of_heq h2))
theorem endpointStrong_hext {F G F' G' : StrictPseudofunctor A (Total (endpointFamily E))}
    (eF : F = F') (eG : G = G')
    (θ : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (η : Pseudofunctor.StrongTrans F'.toPseudofunctor G'.toPseudofunctor)
    (h1 : HEq (strongPostcomp θ (endpointProjection E true)) (strongPostcomp η (endpointProjection E true)))
    (h2 : HEq (strongPostcomp θ (endpointProjection E false)) (strongPostcomp η (endpointProjection E false))) :
    HEq θ η := by
  cases eF; cases eG
  have ha (x : A) : θ.app x = η.app x := by
    apply endpoint_hom_ext E
    · exact congrArg (fun z => z.app x) (eq_of_heq h1)
    · exact congrArg (fun z => z.app x) (eq_of_heq h2)
  apply heq_of_eq
  apply strongTrans_ext _ _ ha
  intro x y p
  apply endpoint_cell_hext E (congrArg (fun a => F.map p ≫ a) (ha y))
    (congrArg (fun a => a ≫ G.map p) (ha x))
  · have a := (strongPostcomp_naturality_heq θ (endpointProjection E true) p).symm
    have b := strongTrans_naturality_heq rfl rfl _ _ h1 p
    have c := strongPostcomp_naturality_heq η (endpointProjection E true) p
    exact a.trans (b.trans c)
  · have a := (strongPostcomp_naturality_heq θ (endpointProjection E false) p).symm
    have b := strongTrans_naturality_heq rfl rfl _ _ h2 p
    have c := strongPostcomp_naturality_heq η (endpointProjection E false) p
    exact a.trans (b.trans c)
end SquareKit.Internal.PathTransport.TwoFamily
