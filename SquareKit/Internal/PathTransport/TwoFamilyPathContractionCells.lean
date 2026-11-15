import SquareKit.Internal.PathTransport.TwoFamilyPathContractionCoherence
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
/-- First projection after reflexivity retains every genuine dependent 2-cell. -/
theorem pathFirst_reflexivity_cell_heq {x y : Total F} {p q : x ⟶ y} (α : p ⟶ q) :
    HEq ((pathFirst F).map₂ ((pathReflexivity F).map₂ α)) α := by
  exact congr_arg_heq (fun H : StrictPseudofunctor (Total F) (Total F) => H.map₂ α)
    (pathReflexivity_first F)
private theorem right_identity_heq {C : Type*} [Bicategory C] [Strict C]
    {a b : C} {f g : a ⟶ b} (α : f ⟶ g) (q : b ⟶ b) (h : q = 𝟙 b) :
    HEq (α ▷ q) α := by
  cases h
  simp only [Bicategory.whiskerRight_id, Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl
private theorem left_identity_heq {C : Type*} [Bicategory C] [Strict C]
    {a b : C} {f g : a ⟶ b} (α : f ⟶ g) (q : a ⟶ a) (h : q = 𝟙 a) :
    HEq (q ◁ α) α := by
  cases h
  simp only [Bicategory.id_whiskerLeft, Strict.leftUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl
/-- The actual contraction comparison is natural at every genuine path-context 2-cell. -/
theorem contractionNaturality_naturality {x y : PathContext F} {p q : x ⟶ y} (α : p ⟶ q) :
    (contractionRetract F).map₂ α ▷ contractionComponent F y ≫ contractionNaturalityCell F q =
      contractionNaturalityCell F p ≫ contractionComponent F x ◁ α := by
  apply pathFirst_cell_injective F
  apply eq_of_heq
  simp only [PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_left,
    Pseudofunctor.map₂_whisker_right, (pathFirst F).mapComp_eq_eqToIso,
    eqToIso.hom, eqToIso.inv, contractionNaturalityCell_first,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  have h1 := right_identity_heq ((pathFirst F).map₂ ((contractionRetract F).map₂ α))
    ((pathFirst F).map (X := pathReflexivityObj F ((pathFirst F).obj y)) (Y := y)
      (contractionComponent F y)) (pathFirst_contractionComponent F y)
  have h2 : HEq ((pathFirst F).map₂ ((contractionRetract F).map₂ α)) ((pathFirst F).map₂ α) := by
    change HEq ((pathFirst F).map₂ ((pathReflexivity F).map₂ ((pathFirst F).map₂ α))) _
    exact pathFirst_reflexivity_cell_heq F ((pathFirst F).map₂ α)
  have h3 := left_identity_heq ((pathFirst F).map₂ α)
    ((pathFirst F).map (X := pathReflexivityObj F ((pathFirst F).obj x)) (Y := x)
      (contractionComponent F x)) (pathFirst_contractionComponent F x)
  with_reducible exact h1.trans (h2.trans h3.symm)

end SquareKit.Internal.PathTransport.TwoFamily
