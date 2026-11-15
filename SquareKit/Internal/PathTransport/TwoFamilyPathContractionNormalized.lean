import SquareKit.Internal.PathTransport.TwoFamilyPathContractionCells
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
/-- The retract retains each arrow in the reflexivity image exactly. -/
theorem contractionRetract_reflexivity_map {x y : Total F} (p : x ⟶ y) :
    (contractionRetract F).map ((pathReflexivity F).map p) = (pathReflexivity F).map p := by
  change (pathReflexivity F).map ((pathFirst F).map ((pathReflexivity F).map p)) = _
  rw [pathFirst_reflexivity_map]

/-- The source composite of the reflexive comparison is the original reflexive arrow. -/
theorem contraction_refl_left {x y : Total F} (p : x ⟶ y) :
    (contractionRetract F).map ((pathReflexivity F).map p) ≫
      contractionComponent F ((pathReflexivity F).obj y) = (pathReflexivity F).map p := by
  have h := contractionComponent_refl F y
  change contractionComponent F ((pathReflexivity F).obj y) = 𝟙 ((pathReflexivity F).obj y) at h
  rw [contractionRetract_reflexivity_map]
  exact (congrArg (fun q => (pathReflexivity F).map p ≫ q) h).trans (Category.comp_id _)
/-- The target composite of the reflexive comparison is the original reflexive arrow. -/
theorem contraction_refl_right {x y : Total F} (p : x ⟶ y) :
    contractionComponent F ((pathReflexivity F).obj x) ≫ (pathReflexivity F).map p =
      (pathReflexivity F).map p := by
  have h := contractionComponent_refl F x
  change contractionComponent F ((pathReflexivity F).obj x) = 𝟙 ((pathReflexivity F).obj x) at h
  exact (congrArg (fun q => q ≫ (pathReflexivity F).map p) h).trans (Category.id_comp _)
/-- Along reflexivity the full naturality comparison is the canonical identity boundary. -/
theorem contractionNaturalityCell_refl {x y : Total F} (p : x ⟶ y) :
    contractionNaturalityCell F ((pathReflexivity F).map p) =
      eqToHom ((contraction_refl_left F p).trans (contraction_refl_right F p).symm) := by
  apply pathFirst_cell_injective F
  rw [contractionNaturalityCell_first, PrelaxFunctor.map₂_eqToHom]

end SquareKit.Internal.PathTransport.TwoFamily
