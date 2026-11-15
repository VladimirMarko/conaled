import SquareKit.Internal.PathTransport.TwoStrongPrecomp
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
universe u v w u' v' w'
variable {A : Type u} [Bicategory.{w,v} A]
variable {B : Type u'} [Bicategory.{w',v'} B]
/-- Equality of coherent transformations is determined by components and comparison cells. -/
theorem strongTrans_ext {F G : Pseudofunctor A B} (η θ : Pseudofunctor.StrongTrans F G)
    (ha : ∀ x, η.app x = θ.app x)
    (hn : ∀ {x y} (p : x ⟶ y), HEq (η.naturality p).hom (θ.naturality p).hom) : η = θ := by
  rcases η with ⟨ηa, ηn, ηi, ηc, ηh⟩
  rcases θ with ⟨θa, θn, θi, θc, θh⟩
  have hA : ηa = θa := funext ha
  subst θa
  have hN : @ηn = @θn := by
    funext x y p
    apply Iso.ext
    exact eq_of_heq (hn p)
  subst θn
  rfl
/-- Boundary equalities and actual data identify coherent transformations heterogeneously. -/
theorem strongTrans_hext {F G F' G' : Pseudofunctor A B}
    (hF : F = F') (hG : G = G')
    (η : Pseudofunctor.StrongTrans F G) (θ : Pseudofunctor.StrongTrans F' G')
    (ha : ∀ x, HEq (η.app x) (θ.app x))
    (hn : ∀ {x y} (p : x ⟶ y), HEq (η.naturality p).hom (θ.naturality p).hom) : HEq η θ := by
  cases hF
  cases hG
  apply heq_of_eq
  exact strongTrans_ext η θ (fun x => eq_of_heq (ha x)) hn
end SquareKit.Internal.PathTransport
