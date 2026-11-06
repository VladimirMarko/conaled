import SquareKit.Internal.PathTransport.TwoStrongTransport
import SquareKit.Internal.PathTransport.TwoIdentityTransport
/-! Inversion of coherent transformations with invertible components. -/
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
variable {A : Type u} [Bicategory.{w,v} A] [Bicategory.Strict A]
variable {B : Type u'} [Bicategory.{w',v'} B] [Bicategory.Strict B] [IsLocallyGroupoid B]
variable {F G : StrictPseudofunctor A B}
variable (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
variable [∀ x, IsIso (η.app x)]
/-- Inverting the mate reverses a coherent naturality square. -/
noncomputable def inverseComparison {a b : A} (f : a ⟶ b) :
    G.map f ≫ inv (η.app b) ⟶ inv (η.app a) ≫ F.map f :=
  inv (mateEquiv (TwoIdentityTransport.inverseAdjunction (η.app a))
    (TwoIdentityTransport.inverseAdjunction (η.app b)) (η.naturality f).hom)

/-- The reverse comparison retains the original coherent square exactly. -/
theorem inverseComparison_recover {a b : A} (f : a ⟶ b) :
    (mateEquiv (TwoIdentityTransport.inverseAdjunction (η.app a))
      (TwoIdentityTransport.inverseAdjunction (η.app b))).symm
        (inv (inverseComparison η f)) = (η.naturality f).hom := by
  simp only [inverseComparison, IsIso.inv_inv, Equiv.symm_apply_apply]

/-- The inverse comparison preserves the strict identity boundary. -/
theorem inverseComparison_id (a : A) : inverseComparison η (𝟙 a) =
    eqToHom (by simp only [F.map_id, G.map_id, Category.comp_id, Category.id_comp]) := by
  have h := η.naturality_id a
  simp only [F.mapId_eq_eqToIso, G.mapId_eq_eqToIso,
    Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
    whiskerLeft_eqToHom, eqToHom_whiskerRight,  eqToHom_trans] at h
  have hh := (IsIso.eq_comp_inv _).mpr h
  simp only [inverseComparison, hh]
  simp [mateEquiv_apply, Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_apply,TwoIdentityTransport.inverseAdjunction, Strict.associator_eqToIso,
    Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso]

/-- Inverse comparisons preserve pasting by the mates correspondence. -/
theorem inverseComparison_comp {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    inverseComparison η (f ≫ g) ≫ inv (η.app a) ◁ (F.mapComp f g).hom =
      (G.mapComp f g).hom ▷ inv (η.app c) ≫ (α_ _ _ _).hom ≫
        G.map f ◁ inverseComparison η g ≫ (α_ _ _ _).inv ≫
        inverseComparison η f ▷ F.map g ≫ (α_ _ _ _).hom := by
  have hp := mateEquiv_vcomp (TwoIdentityTransport.inverseAdjunction (η.app a))
    (TwoIdentityTransport.inverseAdjunction (η.app b))
    (TwoIdentityTransport.inverseAdjunction (η.app c))
    (η.naturality f).hom (η.naturality g).hom
  have hn := η.naturality_comp_hom f g
  simp only [F.mapComp_eq_eqToIso, G.mapComp_eq_eqToIso, eqToIso.hom,
    eqToIso.inv, eqToHom_whiskerRight, whiskerLeft_eqToHom] at hn
  simp only [inverseComparison, hn]
  simp only [leftAdjointSquare.vcomp, rightAdjointSquare.vcomp,
    mateEquiv_apply, Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_apply,
    TwoIdentityTransport.inverseAdjunction, Strict.associator_eqToIso,
    Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
    whiskerLeft_comp, comp_whiskerRight, whiskerLeft_eqToHom, eqToHom_whiskerRight,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans] at hp ⊢
  have hi := congrArg (fun z => inv z) hp
  simp only [IsIso.inv_comp, inv_eqToHom, inv_whiskerLeft, inv_whiskerRight,
    Category.assoc] at hi
  apply eq_of_heq
  simp only [F.mapComp_eq_eqToIso, G.mapComp_eq_eqToIso, eqToIso.hom,
    eqToHom_whiskerRight, whiskerLeft_eqToHom, IsIso.inv_comp, inv_eqToHom,
    inv_whiskerLeft, inv_whiskerRight, Category.assoc,
    eqToHom_comp_heq_iff]
  have hi' := heq_of_eq hi
  simp only [eqToHom_comp_heq_iff, 
    heq_eqToHom_comp_iff] at hi'
  simpa only [whiskerLeft_comp, comp_whiskerRight, whiskerLeft_eqToHom,
    eqToHom_whiskerRight, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_comp_heq_iff, heq_eqToHom_comp_iff] using hi' 

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

private theorem unit_whiskerLeft_heq {a b : B} (u : a ⟶ a) (hu : u = 𝟙 a)
    {f g : a ⟶ b} (α : f ⟶ g) : HEq (u ◁ α) α := by
  cases hu
  simp only [id_whiskerLeft, Strict.leftUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl
private theorem unit_whiskerRight_left_heq {a b c : B} (u : a ⟶ b)
    (v : c ⟶ c) (hv : v = 𝟙 c) {f g : b ⟶ c} (α : f ⟶ g) :
    HEq (u ◁ α ▷ v) (u ◁ α) := by
  cases hv
  simp only [whiskerRight_id, Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
    whiskerLeft_comp, whiskerLeft_eqToHom,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

/-- Reversing comparisons retains their naturality for genuine cells. -/
theorem inverseComparison_naturality {a b : A} {f g : a ⟶ b} (α : f ⟶ g) :
    G.map₂ α ▷ inv (η.app b) ≫ inverseComparison η g =
      inverseComparison η f ≫ inv (η.app a) ◁ F.map₂ α := by
  have hi : (η.naturality f).inv ≫ F.map₂ α ▷ η.app b =
      η.app a ◁ G.map₂ α ≫ (η.naturality g).inv := by
    apply (cancel_epi (η.naturality f).hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← η.naturality_naturality α]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h := congrArg (fun z => (inv (η.app a) ◁ z) ▷ inv (η.app b)) hi
  simp only [whiskerLeft_comp, comp_whiskerRight] at h
  simp only [inverseComparison, mateEquiv_apply, Adjunction.homEquiv₁_apply,
    Adjunction.homEquiv₂_apply, TwoIdentityTransport.inverseAdjunction,
    Strict.associator_eqToIso, Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
    eqToIso.hom, eqToIso.inv, whiskerLeft_comp,
    whiskerLeft_eqToHom, eqToHom_whiskerRight, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans, IsIso.inv_comp, inv_eqToHom,
    inv_whiskerLeft, inv_whiskerRight]
  simp only [whisker_assoc, whiskerRight_comp_symm, comp_whiskerLeft_symm,
    Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv, whiskerLeft_comp,
    comp_whiskerRight, whiskerLeft_eqToHom, eqToHom_whiskerRight,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans] at h
  apply eq_of_heq
  have hh := heq_of_eq h.symm
  simp only [← Category.assoc, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff] at hh ⊢
  simp only [Category.assoc, eqToHom_comp_heq_iff, heq_eqToHom_comp_iff,
    IsIso.Iso.inv_hom] at hh ⊢
  refine HEq.trans ?_ (hh.trans ?_)
  · exact cast_composite_heq
      (by simp) (by simp) rfl rfl _ _ _ _ _ _
      (unit_whiskerLeft_heq (inv (η.app a) ≫ η.app a)
        (IsIso.inv_hom_id (η.app a)) (G.map₂ α ▷ inv (η.app b))).symm (HEq.rfl)
  · exact cast_composite_heq rfl rfl (by simp) (by simp) _ _ _ _ _ _ (HEq.rfl)
      (unit_whiskerRight_left_heq (inv (η.app a)) (η.app b ≫ inv (η.app b))
        (IsIso.hom_inv_id (η.app b)) (F.map₂ α))

/-- The pointwise inverse, with all coherent naturality laws constructed. -/
noncomputable def strongInverse :
    Pseudofunctor.StrongTrans G.toPseudofunctor F.toPseudofunctor where
  app x := inv (η.app x)
  naturality f := asIso (inverseComparison η f)
  naturality_naturality α := inverseComparison_naturality η α
  naturality_comp f g := inverseComparison_comp η f g
  naturality_id a := by
    simp only [asIso_hom, inverseComparison_id, F.mapId_eq_eqToIso,
      G.mapId_eq_eqToIso, Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
      eqToIso.hom, eqToIso.inv, whiskerLeft_eqToHom, eqToHom_whiskerRight,
      eqToHom_trans]
end SquareKit.Internal.PathTransport
