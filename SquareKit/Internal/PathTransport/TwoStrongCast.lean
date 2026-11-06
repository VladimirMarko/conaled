import SquareKit.Internal.PathTransport.TwoStrongCongr
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
variable {A B : Type*} [Bicategory A] [Bicategory B]
def strongCast {F G F' G' : StrictPseudofunctor A B} (hF : F = F') (hG : G = G')
    (θ : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor) :
    Pseudofunctor.StrongTrans F'.toPseudofunctor G'.toPseudofunctor := by cases hF; cases hG; exact θ
theorem strongCast_heq {F G F' G' : StrictPseudofunctor A B} (hF : F = F') (hG : G = G')
    (θ : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor) :
    HEq (strongCast hF hG θ) θ := by cases hF; cases hG; rfl

theorem strongPostcomp_functor_heq {C : Type*} [Bicategory C] [Strict B] [Strict C]
    {F G : StrictPseudofunctor A B} (θ : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    {H K : StrictPseudofunctor B C} (h : H = K) : HEq (strongPostcomp θ H) (strongPostcomp θ K) := by cases h; rfl

theorem strongTrans_app_heq {F G F' G' : StrictPseudofunctor A B} (eF : F = F') (eG : G = G')
    (θ : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (η : Pseudofunctor.StrongTrans F'.toPseudofunctor G'.toPseudofunctor)
    (h : HEq θ η) (x : A) : HEq (θ.app x) (η.app x) := by
  cases eF; cases eG; cases eq_of_heq h; rfl

theorem strongTrans_naturality_heq {F G F' G' : StrictPseudofunctor A B} (eF : F = F') (eG : G = G')
    (θ : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (η : Pseudofunctor.StrongTrans F'.toPseudofunctor G'.toPseudofunctor)
    (h : HEq θ η) {x y : A} (p : x ⟶ y) : HEq (θ.naturality p).hom (η.naturality p).hom := by
  cases eF; cases eG; cases eq_of_heq h; rfl
end SquareKit.Internal.PathTransport
