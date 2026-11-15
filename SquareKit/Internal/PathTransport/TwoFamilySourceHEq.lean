import SquareKit.Internal.PathTransport.TwoFamilyHEq
/-! Extensionality of higher functors across equality of their source families. The target is arbitrary; each object, arrow, and genuine cell is compared. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uΓ vΓ wΓ uD vD wD
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable {D : Type uD} [Bicategory.{wD,vD} D]
variable {F G : Family.{uΓ,vΓ,wΓ,u,v,w} Γ}
theorem total_functor_hext_source_family (e : F = G)
    (H : StrictPseudofunctor (Total F) D) (K : StrictPseudofunctor (Total G) D)
    (ho : ∀ x x', HEq x x' → HEq (H.obj x) (K.obj x'))
    (hm : ∀ {x y x' y'} (_hx : HEq x x') (_hy : HEq y y')
      (p : x ⟶ y) (q : x' ⟶ y'), HEq p q → HEq (H.map p) (K.map q))
    (hc : ∀ {x y x' y'} (_hx : HEq x x') (_hy : HEq y y')
      {p q : x ⟶ y} {p' q' : x' ⟶ y'} (_hp : HEq p p') (_hq : HEq q q')
      (α : p ⟶ q) (β : p' ⟶ q'), HEq α β → HEq (H.map₂ α) (K.map₂ β)) : HEq H K := by
  cases e
  apply heq_of_eq
  apply strictFunctorData_ext
  apply prelaxData_ext
  · intro x; exact eq_of_heq (ho x x HEq.rfl)
  · intro x y p; exact hm HEq.rfl HEq.rfl p p HEq.rfl
  · intro x y p q α; exact hc HEq.rfl HEq.rfl HEq.rfl HEq.rfl α α HEq.rfl
end SquareKit.Internal.PathTransport.TwoFamily
