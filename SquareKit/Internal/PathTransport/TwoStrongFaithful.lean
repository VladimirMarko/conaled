import SquareKit.Internal.PathTransport.TwoStrongCongr
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uB vB wB uC vC wC
variable {A : Type u} [Bicategory.{w,v} A]
variable {B : Type uB} [Bicategory.{wB,vB} B] [Strict B]
variable {C : Type uC} [Bicategory.{wC,vC} C] [Strict C]
variable (H : StrictPseudofunctor B C)
variable (hm : ∀{x y : B}, Function.Injective (fun p : x ⟶ y => H.map p))
variable (hc : ∀{x y : B} {p q : x ⟶ y}, Function.Injective (H.map₂ (f := p) (g := q)))
omit [Strict B] [Strict C] in
include hc in
private theorem mappedCell_heq_reflect {x y : B} {p q p' q' : x ⟶ y}
    (hp : p = p') (hq : q = q') (α : p ⟶ q) (β : p' ⟶ q')
    (h : HEq (H.map₂ α) (H.map₂ β)) : HEq α β := by
  cases hp; cases hq
  exact heq_of_eq (hc (eq_of_heq h))

omit [Strict C] in
private theorem strongNaturality_heq {F G : Pseudofunctor A C}
    {α β : Pseudofunctor.StrongTrans F G} (h : α = β) {x y : A} (p : x ⟶ y) :
    HEq (α.naturality p).hom (β.naturality p).hom := by cases h; rfl

include hm hc in
theorem strongPostcomp_heq_reflect {F G F' G' : StrictPseudofunctor A B}
    (hF : F = F') (hG : G = G')
    (α : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (β : Pseudofunctor.StrongTrans F'.toPseudofunctor G'.toPseudofunctor)
    (h : HEq (strongPostcomp α H) (strongPostcomp β H)) : HEq α β := by
  cases hF; cases hG
  have he := eq_of_heq h
  have ha : ∀x, α.app x = β.app x := fun x => hm (congrArg (fun θ => θ.app x) he)
  apply heq_of_eq
  apply strongTrans_ext α β ha
  intro x y p
  have hn := strongNaturality_heq he p
  have hk := (strongPostcomp_naturality_heq α H p).symm.trans
    (hn.trans (strongPostcomp_naturality_heq β H p))
  exact mappedCell_heq_reflect H (@hc)
    (congrArg (fun a => F.map p ≫ a) (ha y))
    (congrArg (fun a => a ≫ G.map p) (ha x)) _ _ hk
end SquareKit.Internal.PathTransport
