import SquareKit.Internal.PathTransport.TwoIdentityTransport

/-! Inverse mates preserve endpoint postcomposition and strict higher transport. -/
namespace SquareKit.Internal.PathTransport.TwoIdentityTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000

private theorem whiskerLeft_congr_heq {B : Type*} [Bicategory B]
    {a b c : B} {f g : a ⟶ b} (e : f = g)
    {i j i' j' : b ⟶ c} (hi : i = i') (hj : j = j')
    (α : i ⟶ j) (β : i' ⟶ j') (h : HEq α β) : HEq (f ◁ α) (g ◁ β) := by
  cases e
  cases hi
  cases hj
  cases eq_of_heq h
  rfl

private theorem whiskerRight_congr_heq {B : Type*} [Bicategory B]
    {a b c : B} {f g : a ⟶ b} (α : f ⟶ g) {h k : b ⟶ c} (e : h = k) :
    HEq (α ▷ h) (α ▷ k) := by
  cases e
  rfl

private theorem mixedWhisker_congr_heq {B : Type*} [Bicategory B]
    {a b c d : B} {f g : a ⟶ b} (e : f = g)
    {i j : b ⟶ c} (α : i ⟶ j) {q r : c ⟶ d} (e' : q = r) :
    HEq ((f ◁ α) ▷ q) ((g ◁ α) ▷ r) := by
  cases e
  cases e'
  rfl

/-- Postcomposing an endpoint square by a strictly invertible arrow acts on
its inverse mate by inverse left whiskering. -/

theorem inverseMate_postcomp {B : Type*} [Bicategory B] [Bicategory.Strict B]
    [Bicategory.IsLocallyGroupoid B]
    {a a' b c : B} {u : a ⟶ b} {u' : a' ⟶ b} [IsIso u] [IsIso u']
    {h : a ⟶ a'} (ρ : u ⟶ h ≫ u') (t : b ⟶ c) [IsIso t] :
    inverseMate
      (ρ ▷ t ≫ eqToHom (Category.assoc h u' t)) =
      eqToHom (by simp [IsIso.inv_comp, Category.assoc]) ≫
        inv t ◁ inverseMate ρ ≫
          eqToHom (by simp : inv t ≫ inv u' = inv (u' ≫ t)) := by
  have hu : inv (u ≫ t) = inv t ≫ inv u := IsIso.inv_comp
  have ht : t ≫ inv (u' ≫ t) = inv u' := by
    rw [IsIso.inv_comp]
    simp [← Category.assoc]
  simp only [inverseMate, IsIso.inv_comp, inv_eqToHom,
    inv_whiskerRight, whiskerLeft_comp, comp_whiskerRight,
    Bicategory.whiskerLeft_eqToHom, Bicategory.eqToHom_whiskerRight,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  simp only [Bicategory.whisker_assoc, Strict.associator_eqToIso,
    eqToIso.hom, eqToIso.inv, whiskerLeft_comp,
    Bicategory.whiskerLeft_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  apply eq_of_heq
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  have hr := heq_of_eq (Bicategory.whiskerRight_comp (inv ρ) t (inv (u' ≫ t)))
  simp only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff] at hr
  have hraw := hr.symm.trans (whiskerRight_congr_heq (inv ρ) ht)
  have hleft := whiskerLeft_congr_heq hu
    (by simp only [Category.assoc, ht]) (by simp only [Category.assoc, ht])
    _ _ hraw
  have hnest := heq_of_eq (Bicategory.comp_whiskerLeft (inv t) (inv u) (inv ρ ▷ inv u'))
  simp only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff] at hnest
  exact hleft.trans hnest

/-- Strict fiber functors carry inverse mates to inverse mates, with the strict
composition and inverse boundaries made explicit. -/
theorem inverseMate_map {A B : Type*} [Bicategory A] [Bicategory B]
    [Bicategory.Strict A] [Bicategory.Strict B]
    [Bicategory.IsLocallyGroupoid A] [Bicategory.IsLocallyGroupoid B]
    (G : StrictPseudofunctor A B)
    {a a' b : A} {u : a ⟶ b} {u' : a' ⟶ b} [IsIso u] [IsIso u']
    {h : a ⟶ a'} (ρ : u ⟶ h ≫ u') :
    inverseMate (G.map₂ ρ ≫ eqToHom (G.map_comp h u')) =
      eqToHom (by
        rw [G.map_comp]
        exact congrArg (fun z => z ≫ G.map h) (G.toFunctor.map_inv u).symm) ≫
        G.map₂ (inverseMate ρ) ≫ eqToHom (G.toFunctor.map_inv u') := by
  have hu : G.map (inv u) = inv (G.map u) := G.toFunctor.map_inv u
  have hu' : G.map (inv u') = inv (G.map u') := G.toFunctor.map_inv u'
  simp only [inverseMate, IsIso.inv_comp, inv_eqToHom,
    PrelaxFunctor.map₂_comp, PrelaxFunctor.map₂_inv, PrelaxFunctor.map₂_eqToHom,
    Pseudofunctor.map₂_whisker_left, Pseudofunctor.map₂_whisker_right,
    G.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv,
    whiskerLeft_comp, comp_whiskerRight, Bicategory.whiskerLeft_eqToHom,
    Bicategory.eqToHom_whiskerRight, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  apply eq_of_heq
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact mixedWhisker_congr_heq hu.symm (inv (G.map₂ ρ)) hu'.symm

end SquareKit.Internal.PathTransport.TwoIdentityTransport
