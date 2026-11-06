import SquareKit.Internal.PathTransport.TwoIdentityMateFunctoriality

/-! Horizontal compatibility of the complete hom-groupoid transport. -/
namespace SquareKit.Internal.PathTransport.TwoIdentityTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000
universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃
variable {A : Type u₁} [Bicategory.{w₁,v₁} A] [Bicategory.Strict A]
variable {B : Type u₂} [Bicategory.{w₂,v₂} B] [Bicategory.Strict B]
variable {C : Type u₃} [Bicategory.{w₃,v₃} C] [Bicategory.Strict C]
variable [Bicategory.IsLocallyGroupoid B] [Bicategory.IsLocallyGroupoid C]

private theorem nested_whiskerLeft {D : Type*} [Bicategory D] [Bicategory.Strict D]
    {a b c d : D} (f : a ⟶ b) (g : b ⟶ c) {h i : c ⟶ d} (α : h ⟶ i) :
    f ◁ g ◁ α = eqToHom (Category.assoc f g h).symm ≫
      (f ≫ g) ◁ α ≫ eqToHom (Category.assoc f g i) := by
  rw [Bicategory.comp_whiskerLeft]
  simp [Strict.associator_eqToIso]

private theorem nested_whiskerRight {D : Type*} [Bicategory D] [Bicategory.Strict D]
    {a b c d : D} {f g : a ⟶ b} (α : f ⟶ g) (q : b ⟶ c) (r : c ⟶ d) :
    (α ▷ q) ▷ r = eqToHom (Category.assoc f q r) ≫
      α ▷ (q ≫ r) ≫ eqToHom (Category.assoc g q r).symm := by
  rw [Bicategory.whiskerRight_comp]
  simp [Strict.associator_eqToIso]

private theorem conjugate_whiskerLeft {D : Type*} [Bicategory D]
    {a b c : D} {f g : a ⟶ b} (h : f = g) {i j : b ⟶ c} (α : i ⟶ j)
    {k l : a ⟶ c} (hi : k = f ≫ i) (hj : f ≫ j = l)
    (hi' : k = g ≫ i) (hj' : g ≫ j = l) :
    eqToHom hi ≫ f ◁ α ≫ eqToHom hj = eqToHom hi' ≫ g ◁ α ≫ eqToHom hj' := by
  cases h
  rfl

private theorem conjugate_two_whiskers {D : Type*} [Bicategory D]
    {a b c d e : D} {f f' : a ⟶ b} (hf : f = f')
    {i j : b ⟶ e} (σ : i ⟶ j)
    {g g' : a ⟶ c} (hg : g = g') {k l : c ⟶ d} (ρ : k ⟶ l)
    {t t' : d ⟶ e} (ht : t = t') {x y : a ⟶ e}
    (hi : x = f ≫ i) (hm : f ≫ j = g ≫ k ≫ t) (he : g ≫ l ≫ t = y)
    (hi' : x = f' ≫ i) (hm' : f' ≫ j = g' ≫ k ≫ t') (he' : g' ≫ l ≫ t' = y) :
    eqToHom hi ≫ f ◁ σ ≫ eqToHom hm ≫ g ◁ ρ ▷ t ≫ eqToHom he =
      eqToHom hi' ≫ f' ◁ σ ≫ eqToHom hm' ≫ g' ◁ ρ ▷ t' ≫ eqToHom he' := by
  cases hf
  cases hg
  cases ht
  rfl

omit [Bicategory.Strict A] in
/-- Equal functor and endpoint data transport the whole natural hom comparison. -/
theorem homComparison_heq {H H' K K' : StrictPseudofunctor A C}
    (eH : H = H') (eK : K = K')
    (η : StrictTwoTransformation.Trans H K) (η' : StrictTwoTransformation.Trans H' K')
    (hη : HEq η η') {a a' : A} {b b' : C}
    (u : H.obj a ⟶ b) (u₁ : H'.obj a ⟶ b) [IsIso u] [IsIso u₁]
    (u' : K.obj a ⟶ b) (u₁' : K'.obj a ⟶ b) [IsIso u'] [IsIso u₁']
    (v : H.obj a' ⟶ b') (v₁ : H'.obj a' ⟶ b')
    (v' : K.obj a' ⟶ b') (v₁' : K'.obj a' ⟶ b')
    (hu : HEq u u₁) (hu' : HEq u' u₁') (hv : HEq v v₁) (hv' : HEq v' v₁')
    (ρ : u ⟶ η.app a ≫ u') (ρ₁ : u₁ ⟶ η'.app a ≫ u₁')
    (σ : v ⟶ η.app a' ≫ v') (σ₁ : v₁ ⟶ η'.app a' ≫ v₁')
    (hρ : HEq ρ ρ₁) (hσ : HEq σ σ₁) :
    HEq (homComparison η ρ σ) (homComparison η' ρ₁ σ₁) := by
  cases eH
  cases eK
  cases eq_of_heq hη
  cases eq_of_heq hu
  cases eq_of_heq hu'
  cases eq_of_heq hv
  cases eq_of_heq hv'
  cases eq_of_heq hρ
  cases eq_of_heq hσ
  rfl

theorem homComparison_whiskerRight
    {F F' : StrictPseudofunctor A B} (η : StrictTwoTransformation.Trans F F')
    (G : StrictPseudofunctor B C)
    {a a' : A} {b b' : B} {c c' : C}
    {u : F.obj a ⟶ b} {u' : F'.obj a ⟶ b} [IsIso u] [IsIso u']
    {v : F.obj a' ⟶ b'} {v' : F'.obj a' ⟶ b'}
    (ρ : u ⟶ η.app a ≫ u') (σ : v ⟶ η.app a' ≫ v')
    (s : G.obj b ⟶ c) [IsIso s] (t : G.obj b' ⟶ c') :
    homComparison (StrictTwoTransformation.Trans.whiskerRight η G)
      ((G.map₂ ρ ≫ eqToHom (G.map_comp _ _)) ▷ s ≫ eqToHom (Category.assoc _ _ _))
      ((G.map₂ σ ≫ eqToHom (G.map_comp _ _)) ▷ t ≫ eqToHom (Category.assoc _ _ _)) =
      eqToHom (homTransport_comp F G u v s t) ≫
        Functor.whiskerRight (homComparison η ρ σ) (homTransport G s t) ≫
          eqToHom (homTransport_comp F' G u' v' s t).symm := by
  have hm := inverseMate_postcomp (G.map₂ ρ ≫ eqToHom (G.map_comp _ _)) s
  rw [inverseMate_map] at hm
  simp only [comp_whiskerRight, eqToHom_whiskerRight, whiskerLeft_comp,
    whiskerLeft_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans] at hm
  ext p
  simp [homComparison, homNaturality,
    StrictTwoTransformation.Trans.whiskerRight, Strict.associator_eqToIso]
  rw [hm]
  simp [homTransport, G.mapComp_eq_eqToIso, PrelaxFunctor.map₂_eqToHom,
    Strict.associator_eqToIso]
  simp only [nested_whiskerLeft, whiskerLeft_comp, whiskerLeft_eqToHom,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  simp only [← Category.assoc]
  congr 2
  simp only [Category.assoc]
  apply conjugate_whiskerLeft
  have hi : G.map (inv u) = inv (G.map u) := G.toFunctor.map_inv u
  simp only [IsIso.inv_comp, hi, Category.assoc]

omit [Bicategory.IsLocallyGroupoid B] in
theorem homComparison_whiskerLeft (F : StrictPseudofunctor A B)
    {G G' : StrictPseudofunctor B C} (η : StrictTwoTransformation.Trans G G')
    {a a' : A} {b b' : B} {c c' : C}
    (u : F.obj a ⟶ b) [IsIso u] (v : F.obj a' ⟶ b')
    {s : G.obj b ⟶ c} {s' : G'.obj b ⟶ c} [IsIso s] [IsIso s']
    {t : G.obj b' ⟶ c'} {t' : G'.obj b' ⟶ c'}
    (ρ : s ⟶ η.app b ≫ s') (σ : t ⟶ η.app b' ≫ t') :
    homComparison (StrictTwoTransformation.Trans.whiskerLeft F η)
      (G.map u ◁ ρ ≫ eqToHom (by rw [← Category.assoc, η.naturality u, Category.assoc]; rfl))
      (G.map v ◁ σ ≫ eqToHom (by rw [← Category.assoc, η.naturality v, Category.assoc]; rfl)) =
      eqToHom (homTransport_comp F G u v s t) ≫
        Functor.whiskerLeft (homTransport F u v) (homComparison η ρ σ) ≫
          eqToHom (homTransport_comp F G' u v s' t').symm := by
  ext p
  simp [homComparison, homNaturality, inverseMate, homTransport,
    StrictTwoTransformation.Trans.whiskerLeft, Strict.associator_eqToIso]
  simp only [nested_whiskerLeft, whiskerLeft_comp, whiskerLeft_eqToHom,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  simp only [nested_whiskerRight, comp_whiskerRight, eqToHom_whiskerRight,
    whiskerLeft_comp, whiskerLeft_eqToHom,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  apply conjugate_two_whiskers
  · have hi : G.map (inv u) = inv (G.map u) := G.toFunctor.map_inv u
    simp only [G.map_comp, IsIso.inv_comp, hi, Category.assoc]
  · simp only [IsIso.inv_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  · have hi : G'.map (inv u) = inv (G'.map u) := G'.toFunctor.map_inv u
    simp only [G'.map_comp, IsIso.inv_comp, hi, Category.assoc]

end SquareKit.Internal.PathTransport.TwoIdentityTransport
