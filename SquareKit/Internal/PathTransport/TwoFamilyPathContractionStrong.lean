import SquareKit.Internal.PathTransport.TwoFamilyPathContractionNormalized
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
/-- The constructed coherent contraction in the actual higher path context. -/
noncomputable def pathContraction [IsLocallyGroupoid Γ] :
    Pseudofunctor.StrongTrans (contractionRetract F).toPseudofunctor
      (StrictPseudofunctor.id (PathContext F)).toPseudofunctor where
  app := contractionComponent F
  naturality p := asIso (contractionNaturalityCell F p)
  naturality_naturality α := by
    simp only [asIso_hom, StrictPseudofunctor.id_map₂, StrictPseudofunctor.id_map]
    with_reducible exact contractionNaturality_naturality F α
  naturality_id x := by
    simp only [asIso_hom, StrictPseudofunctor.id_map]
    with_reducible exact contractionNaturality_id F x
  naturality_comp p q := by
    simp only [asIso_hom, StrictPseudofunctor.id_map]
    with_reducible exact contractionNaturality_comp F p q

/-- The assembled contraction has identity component at every reflexive object. -/
theorem pathContraction_app_refl [IsLocallyGroupoid Γ] (x : Total F) :
    (pathContraction F).app ((pathReflexivity F).obj x) = 𝟙 ((pathReflexivity F).obj x) := by
  exact contractionComponent_refl F x
/-- Its actual comparison at reflexivity is the canonical identity boundary. -/
theorem pathContraction_naturality_refl [IsLocallyGroupoid Γ] {x y : Total F} (p : x ⟶ y) :
    ((pathContraction F).naturality ((pathReflexivity F).map p)).hom =
      eqToHom ((contraction_refl_left F p).trans (contraction_refl_right F p).symm) := by
  exact contractionNaturalityCell_refl F p

end SquareKit.Internal.PathTransport.TwoFamily
