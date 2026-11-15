import SquareKit.Internal.PathTransport.TwoFunctorData
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
variable {A B C D : Type*} [Bicategory A] [Bicategory B] [Bicategory C] [Bicategory D]
/-- Strict higher functor composition is associative as a whole functor. -/
theorem strictFunctor_comp_assoc (F : StrictPseudofunctor A B)
    (G : StrictPseudofunctor B C) (H : StrictPseudofunctor C D) :
    (F.comp G).comp H = F.comp (G.comp H) :=
  strictFunctorData_ext rfl
/-- Identity on the source leaves the entire strict higher functor unchanged. -/
theorem strictFunctor_id_comp (F : StrictPseudofunctor A B) :
    (StrictPseudofunctor.id A).comp F = F := strictFunctorData_ext rfl
/-- Identity on the target leaves the entire strict higher functor unchanged. -/
theorem strictFunctor_comp_id (F : StrictPseudofunctor A B) :
    F.comp (StrictPseudofunctor.id B) = F := strictFunctorData_ext rfl
end SquareKit.Internal.PathTransport
