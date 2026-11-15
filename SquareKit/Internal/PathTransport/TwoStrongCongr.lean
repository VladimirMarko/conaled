import SquareKit.Internal.PathTransport.TwoStrongComposition
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w' u'' v'' w''
variable {A : Type u} [Bicategory.{w,v} A] [Bicategory.Strict A]
variable {B : Type u'} [Bicategory.{w',v'} B] [Bicategory.Strict B]
variable {C : Type u''} [Bicategory.{w'',v''} C] [Bicategory.Strict C]
omit [Strict A] in
/-- Mapping equal coherent transformations retains their full dependent data. -/
theorem strongPostcomp_heq {F G F' G' : StrictPseudofunctor A B}
    (eF : F = F') (eG : G = G')
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (θ : Pseudofunctor.StrongTrans F'.toPseudofunctor G'.toPseudofunctor)
    (h : HEq η θ) (H : StrictPseudofunctor B C) :
    HEq (strongPostcomp η H) (strongPostcomp θ H) := by
  cases eF
  cases eG
  cases eq_of_heq h
  rfl
omit [Strict A] in
/-- Mapping a coherent comparison retains its actual mapped cell up to typed boundaries. -/
theorem strongPostcomp_naturality_heq {F G : StrictPseudofunctor A B}
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (H : StrictPseudofunctor B C) {x y : A} (p : x ⟶ y) :
    HEq ((strongPostcomp η H).naturality p).hom (H.map₂ (η.naturality p).hom) := by
  simp only [strongPostcomp, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    StrictPseudofunctor.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl
end SquareKit.Internal.PathTransport
