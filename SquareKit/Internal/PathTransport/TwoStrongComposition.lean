import SquareKit.Internal.PathTransport.TwoStrongData
import SquareKit.Internal.PathTransport.TwoFunctorComposition
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ u₄ v₄ w₄
variable {A : Type u₁} [Bicategory.{w₁,v₁} A] [Bicategory.Strict A]
variable {B : Type u₂} [Bicategory.{w₂,v₂} B] [Bicategory.Strict B]
variable {C : Type u₃} [Bicategory.{w₃,v₃} C] [Bicategory.Strict C]
variable {D : Type u₄} [Bicategory.{w₄,v₄} D] [Bicategory.Strict D]
variable {F G : StrictPseudofunctor A B}
variable (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
omit [Strict A] in
/-- Mapping a coherent transformation twice agrees with mapping it by the composite. -/
theorem strongPostcomp_comp (H : StrictPseudofunctor B C) (K : StrictPseudofunctor C D) :
    HEq (strongPostcomp (strongPostcomp η H) K) (strongPostcomp η (H.comp K)) := by
  apply strongTrans_hext
    (congrArg (fun L : StrictPseudofunctor A D => L.toPseudofunctor) (strictFunctor_comp_assoc F H K))
    (congrArg (fun L : StrictPseudofunctor A D => L.toPseudofunctor) (strictFunctor_comp_assoc G H K))
  · intro x
    rfl
  · intro x y p
    simp only [strongPostcomp, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      StrictPseudofunctor.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv,
      Functor.map_comp, eqToHom_map,
      eqToHom_comp_heq_iff, comp_eqToHom_heq_iff, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    rfl
omit [Strict A] [Strict C] in
/-- Precomposition and postcomposition preserve the same actual comparison data. -/
theorem strongPostcomp_precomp (H : StrictPseudofunctor C A) (K : StrictPseudofunctor B D) :
    HEq (strongPostcomp (strongPrecomp η H) K) (strongPrecomp (strongPostcomp η K) H) := by
  apply strongTrans_hext
    (congrArg (fun L : StrictPseudofunctor C D => L.toPseudofunctor) (strictFunctor_comp_assoc H F K))
    (congrArg (fun L : StrictPseudofunctor C D => L.toPseudofunctor) (strictFunctor_comp_assoc H G K))
  · intro x
    rfl
  · intro x y p
    rfl
end SquareKit.Internal.PathTransport
