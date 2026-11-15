import SquareKit.Internal.PathTransport.TwoFamilyPathContractionProjection
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
/-- First projection followed by reflexivity on the actual path context. -/
noncomputable def contractionRetract : StrictPseudofunctor (PathContext F) (PathContext F) :=
  (pathFirst F).comp (pathReflexivity F)
/-- The constructed contraction comparison satisfies the strong-transformation unit law. -/
theorem contractionNaturality_id (x : PathContext F) :
    contractionNaturalityCell F (𝟙 x) ≫ contractionComponent F x ◁
      ((StrictPseudofunctor.id (PathContext F)).mapId x).hom =
    ((contractionRetract F).mapId x).hom ▷ contractionComponent F x ≫
      (λ_ (contractionComponent F x)).hom ≫ (ρ_ (contractionComponent F x)).inv := by
  apply pathFirst_cell_injective F
  simp only [PrelaxFunctor.map₂_comp, (contractionRetract F).mapId_eq_eqToIso,
    (StrictPseudofunctor.id (PathContext F)).mapId_eq_eqToIso,
    Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
    eqToIso.hom, eqToIso.inv, Bicategory.whiskerLeft_eqToHom,
    Bicategory.eqToHom_whiskerRight, PrelaxFunctor.map₂_eqToHom,
    contractionNaturalityCell_first, eqToHom_trans]
/-- The constructed contraction comparison satisfies the strong-transformation composition law. -/
theorem contractionNaturality_comp {x y z : PathContext F} (p : x ⟶ y) (q : y ⟶ z) :
    contractionNaturalityCell F (p ≫ q) ≫ contractionComponent F x ◁
      ((StrictPseudofunctor.id (PathContext F)).mapComp p q).hom =
    ((contractionRetract F).mapComp p q).hom ▷ contractionComponent F z ≫
      (α_ _ _ _).hom ≫ (contractionRetract F).map p ◁ contractionNaturalityCell F q ≫
      (α_ _ _ _).inv ≫ contractionNaturalityCell F p ▷ q ≫ (α_ _ _ _).hom := by
  apply pathFirst_cell_injective F
  simp only [PrelaxFunctor.map₂_comp, (contractionRetract F).mapComp_eq_eqToIso,
    (StrictPseudofunctor.id (PathContext F)).mapComp_eq_eqToIso,
    Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
    Bicategory.whiskerLeft_eqToHom, Bicategory.eqToHom_whiskerRight,
    PrelaxFunctor.map₂_eqToHom, Pseudofunctor.map₂_whisker_left,
    Pseudofunctor.map₂_whisker_right, (pathFirst F).mapComp_eq_eqToIso,
    contractionNaturalityCell_first, Bicategory.whiskerLeft_eqToHom,
    Bicategory.eqToHom_whiskerRight, eqToIso.hom, eqToIso.inv, eqToHom_trans]

end SquareKit.Internal.PathTransport.TwoFamily
