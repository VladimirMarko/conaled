import SquareKit.Internal.PathTransport.TwoFamilySigmaFamily

/-! Fiber inclusion and cartesian comparison commute with arbitrary substitution. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ uB vB wB
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) (σ : StrictPseudofunctor Δ Γ)

theorem fiberInclusion_reindex_map_heq (γ : Δ) {a b : F.obj (σ.obj γ)} (p : a ⟶ b) :
    HEq ((reindexHigher F σ).map ((fiberInclusion (reindex σ F) γ).map p))
      ((fiberInclusion F (σ.obj γ)).map p) := by
  apply total_hom_hext F rfl rfl
  · exact heq_of_eq (σ.map_id γ)
  · change HEq (eqToHom _ ≫ p) (eqToHom _ ≫ p)
    simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
    rfl

theorem fiberInclusion_reindex_cell_heq (γ : Δ) {a b : F.obj (σ.obj γ)}
    {p q : a ⟶ b} (α : p ⟶ q) :
    HEq ((reindexHigher F σ).map₂ ((fiberInclusion (reindex σ F) γ).map₂ α))
      ((fiberInclusion F (σ.obj γ)).map₂ α) := by
  apply total_cell_hext F rfl rfl
    (fiberInclusion_reindex_map_heq F σ γ p) (fiberInclusion_reindex_map_heq F σ γ q)
  · change HEq (σ.map₂ (𝟙 (𝟙 γ))) (𝟙 (𝟙 (σ.obj γ)))
    rw [σ.map₂_id, σ.map_id]
  · change HEq (eqToHom _ ◁ α ≫ eqToHom _) (eqToHom _ ◁ α ≫ eqToHom _)
    apply HEq.trans (comp_eqToHom_heq _ _)
    apply HEq.trans (eqToHom_left_heq _ α)
    apply HEq.symm
    apply HEq.trans (comp_eqToHom_heq _ _)
    exact eqToHom_left_heq _ α

theorem fiberInclusion_reindex (γ : Δ) :
    (fiberInclusion (reindex σ F) γ).comp (reindexHigher F σ) =
      fiberInclusion F (σ.obj γ) := by
  apply strictFunctorData_ext
  apply prelaxData_ext
  · intro a; rfl
  · exact fun p => fiberInclusion_reindex_map_heq F σ γ p
  · exact fun α => fiberInclusion_reindex_cell_heq F σ γ α


theorem fiberRestriction_reindex
    (B : Family (Total F)) (γ : Δ) :
    fiberRestriction (reindex σ F) γ (reindex (reindexHigher F σ) B) =
      fiberRestriction F (σ.obj γ) B := by
  calc
    (fiberInclusion (reindex σ F) γ).comp ((reindexHigher F σ).comp B) =
        ((fiberInclusion (reindex σ F) γ).comp (reindexHigher F σ)).comp B :=
      StrictTwoTransformation.functor_ext rfl
    _ = (fiberInclusion F (σ.obj γ)).comp B :=
      congrArg (fun H => H.comp B) (fiberInclusion_reindex F σ γ)

theorem cartesianLift_reindex {γ δ : Δ} (f : γ ⟶ δ) (a : F.obj (σ.obj γ)) :
    (reindexHigher F σ).map (cartesianLift (reindex σ F) f a) =
      cartesianLift F (σ.map f) a := rfl

theorem equalityFiber_reindex {x y : Total (reindex σ F)} {p q : x ⟶ y}
    (α : p ⟶ q) (hα : EqualityFiber (reindex σ F) α) :
    EqualityFiber F ((reindexHigher F σ).map₂ α) := hα

theorem cartesianComparisonCell_reindex_source {γ δ : Δ} {f g : γ ⟶ δ}
    (α : f ⟶ g) (a : F.obj (σ.obj γ)) :
    (reindexHigher F σ).map
      (cartesianLift (reindex σ F) f a ≫
        (fiberInclusion (reindex σ F) δ).map (((reindex σ F).map₂ α).app a)) =
      cartesianLift F (σ.map f) a ≫
        (fiberInclusion F (σ.obj δ)).map ((F.map₂ (σ.map₂ α)).app a) := by
  rw [(reindexHigher F σ).map_comp, cartesianLift_reindex]
  congr 1
  exact eq_of_heq (fiberInclusion_reindex_map_heq F σ δ _)

theorem cartesianComparisonCell_reindex {γ δ : Δ} {f g : γ ⟶ δ}
    (α : f ⟶ g) (a : F.obj (σ.obj γ)) :
    (reindexHigher F σ).map₂ (cartesianComparisonCell (reindex σ F) α a) =
      eqToHom (cartesianComparisonCell_reindex_source F σ α a) ≫
        cartesianComparisonCell F (σ.map₂ α) a := by
  apply equalityFiber_ext F
  · change σ.map₂ (cartesianComparisonCell (reindex σ F) α a).base =
      (eqToHom (cartesianComparisonCell_reindex_source F σ α a)).base ≫
        (cartesianComparisonCell F (σ.map₂ α) a).base
    rw [cartesianComparisonCell_base, cartesianComparisonCell_base,
      total_eqToHom_base, σ.map₂_comp, σ.map₂_eqToHom]
    simp only [eqToHom_trans_assoc]
  · exact equalityFiber_reindex F σ _
      (cartesianComparisonCell_equalityFiber (reindex σ F) α a)
  · exact equalityFiber_comp F (equalityFiber_cast F _)
      (cartesianComparisonCell_equalityFiber F _ a)

end SquareKit.Internal.PathTransport.TwoFamily
