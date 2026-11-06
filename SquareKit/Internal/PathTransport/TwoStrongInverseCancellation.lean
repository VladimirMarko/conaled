import SquareKit.Internal.PathTransport.TwoStrongInverse
import SquareKit.Internal.PathTransport.TwoStrongData
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w u' v' w'
variable {A : Type u} [Bicategory.{w,v} A] [Strict A]
variable {B : Type u'} [Bicategory.{w',v'} B] [Strict B] [IsLocallyGroupoid B]
variable {F G : StrictPseudofunctor A B}
variable (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
variable [∀ x, IsIso (η.app x)]
private theorem cast_composite_heq {C : Type*} [Category* C]
    {a b c d a' b' c' d' : C} (ha : a = a') (hb : b = b')
    (hc : c = c') (hd : d = d') (α : a ⟶ b) (β : c ⟶ d)
    (α' : a' ⟶ b') (β' : c' ⟶ d') (e : b = c) (e' : b' = c')
    (hα : HEq α α') (hβ : HEq β β') :
    HEq (α ≫ eqToHom e ≫ β) (α' ≫ eqToHom e' ≫ β') := by
  cases ha
  cases hb
  cases hc
  cases hd
  cases eq_of_heq hα
  cases eq_of_heq hβ
  rfl

private theorem id_cast_heq {C : Type*} [Category C] {x y z : C}
    (h : x = y) (k : y = z) : HEq (𝟙 x) (eqToHom k) := by
  cases h
  cases k
  rfl

/-- The coherent inverse cancels the original transformation, including comparison cells. -/
theorem strongInverse_vcomp : Pseudofunctor.StrongTrans.vcomp (strongInverse η) η =
    Pseudofunctor.StrongTrans.id G.toPseudofunctor := by
  apply strongTrans_ext
  · intro a
    exact IsIso.inv_hom_id (η.app a)
  · intro a b f
    change HEq ((α_ _ _ _).inv ≫ inverseComparison η f ▷ η.app b ≫
      (α_ _ _ _).hom ≫ inv (η.app a) ◁ (η.naturality f).hom ≫ (α_ _ _ _).inv)
      ((ρ_ (G.map f)).hom ≫ (λ_ (G.map f)).inv)
    simp only [inverseComparison, mateEquiv_apply, Adjunction.homEquiv₁_apply,
      Adjunction.homEquiv₂_apply, TwoIdentityTransport.inverseAdjunction,
      Strict.associator_eqToIso, Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
      eqToIso.hom, eqToIso.inv, IsIso.inv_comp, inv_eqToHom,
      inv_whiskerLeft, inv_whiskerRight, comp_whiskerRight, eqToHom_whiskerRight,
      whiskerLeft_comp, whiskerLeft_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    simp only [whisker_assoc, whiskerRight_comp_symm, IsIso.inv_hom_id,
      Strict.associator_eqToIso, Strict.rightUnitor_eqToIso,
      whiskerRight_id, eqToIso.hom, eqToIso.inv, whiskerLeft_comp, whiskerLeft_eqToHom,
      Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    refine HEq.trans (eqToHom_comp_heq _ _) ?_
    simp only [← Category.assoc, comp_eqToHom_heq_iff]
    simp only [Category.assoc]
    refine HEq.trans (cast_composite_heq
      (α' := inv (η.app a) ◁ inv (η.naturality f).hom)
      (β' := inv (η.app a) ◁ (η.naturality f).hom)
      ?_ ?_ rfl rfl _ _ _ rfl ?_ HEq.rfl) ?_
    · simp [Category.assoc]
    · simp [Category.assoc]
    · generalize hv : inv (η.app b) ≫ η.app b = v
      have hv' : v = 𝟙 _ := hv.symm.trans (IsIso.inv_hom_id _)
      cases hv'
      simp only [whiskerRight_id, Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
        whiskerLeft_comp, whiskerLeft_eqToHom, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
      rfl
    · simp only [eqToHom_refl, Category.id_comp, ← whiskerLeft_comp,
        IsIso.inv_hom_id, whiskerLeft_id]
      exact id_cast_heq (by simp [← Category.assoc]) _

end SquareKit.Internal.PathTransport
