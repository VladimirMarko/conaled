import SquareKit.Internal.PathTransport.TwoStrongComposition
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
variable {A B C D : Type*} [Bicategory A] [Bicategory B] [Bicategory C] [Bicategory D]
variable [Strict A] [Strict B] [Strict C] [Strict D]
variable {F G : StrictPseudofunctor A B}
variable (θ : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
theorem strongPrecomp_functor_heq {H K : StrictPseudofunctor C A} (h : H = K) :
    HEq (strongPrecomp θ H) (strongPrecomp θ K) := by cases h; rfl
theorem strongPrecomp_comp (H : StrictPseudofunctor C A) (K : StrictPseudofunctor D C) :
    HEq (strongPrecomp (strongPrecomp θ H) K) (strongPrecomp θ (K.comp H)) := by
  apply strongTrans_hext
    (congrArg (fun L => L.toPseudofunctor) (strictFunctor_comp_assoc K H F).symm)
    (congrArg (fun L => L.toPseudofunctor) (strictFunctor_comp_assoc K H G).symm)
  · intro x; rfl
  · intro x y p; rfl
theorem strongPrecomp_id (F : StrictPseudofunctor A B) (H : StrictPseudofunctor C A) :
    strongPrecomp (Pseudofunctor.StrongTrans.id F.toPseudofunctor) H =
      Pseudofunctor.StrongTrans.id (H.comp F).toPseudofunctor := rfl
end SquareKit.Internal.PathTransport
