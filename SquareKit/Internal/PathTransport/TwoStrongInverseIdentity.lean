import SquareKit.Internal.PathTransport.TwoStrongInverseCancellation
import SquareKit.Internal.PathTransport.TwoStrongData
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
variable {A : Type u} [Bicategory.{w,v} A] [Strict A]
variable {B : Type u'} [Bicategory.{w',v'} B] [Strict B]
variable {F G : StrictPseudofunctor A B}
variable (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
theorem strong_vcomp_id : η.vcomp (Pseudofunctor.StrongTrans.id G.toPseudofunctor) = η := by
  apply strongTrans_ext
  · intro a
    exact Category.comp_id (η.app a)
  · intro a b f
    change HEq ((α_ _ _ _).inv ≫ (η.naturality f).hom ▷ 𝟙 _ ≫ (α_ _ _ _).hom ≫
      η.app a ◁ ((ρ_ (G.map f)).hom ≫ (λ_ (G.map f)).inv) ≫ (α_ _ _ _).inv)
      (η.naturality f).hom
    simp only [Strict.associator_eqToIso, Strict.leftUnitor_eqToIso,
      Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
      whiskerRight_id, whiskerLeft_comp, whiskerLeft_eqToHom, Category.assoc,
      eqToHom_trans_assoc, eqToHom_trans, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl

noncomputable instance strongId_isIso (x : A) :
    IsIso ((Pseudofunctor.StrongTrans.id F.toPseudofunctor).app x) := inferInstanceAs (IsIso (𝟙 (F.obj x)))

theorem strongInverse_id : strongInverse (Pseudofunctor.StrongTrans.id F.toPseudofunctor) =
    Pseudofunctor.StrongTrans.id F.toPseudofunctor := by
  rw [← strong_vcomp_id (strongInverse (Pseudofunctor.StrongTrans.id F.toPseudofunctor))]
  exact strongInverse_vcomp (Pseudofunctor.StrongTrans.id F.toPseudofunctor)
section Postcomposition
universe u'' v'' w''
variable {C : Type u''} [Bicategory.{w'',v''} C] [Strict C]
private theorem casts_heq {D : Type*} [Category D] {a b c d : D}
    (h : a = c) (e : a = b) (e' : c = d) : HEq (eqToHom e) (eqToHom e') := by
  cases e
  cases h
  cases e'
  rfl

theorem strongPostcomp_id (F : StrictPseudofunctor A B) (H : StrictPseudofunctor B C) :
    strongPostcomp (Pseudofunctor.StrongTrans.id F.toPseudofunctor) H =
      Pseudofunctor.StrongTrans.id (F.comp H).toPseudofunctor := by
  apply strongTrans_ext
  · intro x; exact H.map_id (F.obj x)
  · intro x y p
    simp only [strongPostcomp, Pseudofunctor.StrongTrans.id, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, H.mapComp_eq_eqToIso, Strict.leftUnitor_eqToIso,
      Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv, H.map₂_comp,
      H.map₂_eqToHom, eqToHom_trans]
    simp only [eqToHom_map, eqToHom_trans]
    exact casts_heq (by simp [H.map_id]) _ _
end Postcomposition
end SquareKit.Internal.PathTransport
