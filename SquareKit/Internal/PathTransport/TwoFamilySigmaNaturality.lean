import SquareKit.Internal.PathTransport.TwoFamilySigmaCells

namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
universe u v w uΓ vΓ wΓ uB vB wB
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))

private theorem classifier_comp_obj {C D E : StrictTwoCategory.{uB,vB,wB}}
    (H : C ⟶ D) (K : D ⟶ E) (x : C) : (H ≫ K).obj x = K.obj (H.obj x) := rfl

private theorem map_paste_heq {C D : Type*} [Bicategory C] [Strict C]
    [Bicategory D] [Strict D] (H K : StrictPseudofunctor C D) (h : H = K)
    {x y : C} (v : x ⟶ y) {z : D} (k : K.obj y ⟶ z) :
    HEq (H.map v ≫ eqToHom (congrArg (fun L => L.obj y) h) ≫ k) (K.map v ≫ k) := by
  cases h
  simp

private theorem sigma_naturality_left_heq {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g)
    {x y : sigmaFiber F γ B} (p : x ⟶ y) :
    HEq (((sigmaMap F B f).map p ≫ sigmaCellComponent F B α y).fiber)
      ((B.map (cartesianLift F f y.base ≫
        (fiberInclusion F δ).map ((F.map₂ α).app y.base))).map p.fiber ≫
          (B.map₂ (cartesianComparisonCell F α y.base)).app y.fiber) := by
  change HEq (compBoundary (fiberRestriction F δ B) _ _ _ ≫ _ ≫ _) _
  apply HEq.trans (eqToHom_comp_heq _ _)
  change HEq ((B.map ((fiberInclusion F δ).map ((F.map₂ α).app y.base))).map
    ((eqToHom ((sigmaTransportComparison F B f).naturality p.base).symm).app x.fiber ≫
      (B.map (cartesianLift F f y.base)).map p.fiber) ≫ eqToHom _ ≫ _) _
  rw [StrictTwoTransformation.Trans.eqToHom_app,
    (B.map ((fiberInclusion F δ).map ((F.map₂ α).app y.base))).map_comp,
    StrongMap.map_eqToHom, Category.assoc]
  apply HEq.trans (eqToHom_comp_heq _ _)
  exact map_paste_heq _ _ (B.map_comp (cartesianLift F f y.base)
    ((fiberInclusion F δ).map ((F.map₂ α).app y.base))).symm p.fiber _

private theorem sigma_naturality_right_heq {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g)
    {x y : sigmaFiber F γ B} (p : x ⟶ y) :
    HEq ((sigmaCellComponent F B α x ≫ (sigmaMap F B g).map p).fiber)
      (((B.map ((fiberInclusion F δ).map ((F.map g).map p.base))).map
        ((B.map₂ (cartesianComparisonCell F α x.base)).app x.fiber) ≫
          (eqToHom ((sigmaTransportComparison F B g).naturality p.base).symm).app x.fiber) ≫
            (B.map (cartesianLift F g y.base)).map p.fiber) := by
  change HEq (compBoundary (fiberRestriction F δ B) _ _ _ ≫ _ ≫ _) _
  apply HEq.trans (eqToHom_comp_heq _ _)
  change HEq ((B.map ((fiberInclusion F δ).map ((F.map g).map p.base))).map
    (eqToHom _ ≫ (B.map₂ (cartesianComparisonCell F α x.base)).app x.fiber) ≫ _ ≫ _) _
  rw [(B.map ((fiberInclusion F δ).map ((F.map g).map p.base))).map_comp,
    StrongMap.map_eqToHom, Category.assoc]
  apply HEq.trans (eqToHom_comp_heq _ _)
  exact heq_of_eq (Category.assoc _ _ _).symm

/-- Genuine base-cell components are natural at every dependent pair arrow. -/
theorem sigmaCellComponent_naturality {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g)
    {x y : sigmaFiber F γ B} (p : x ⟶ y) :
    (sigmaMap F B f).map p ≫ sigmaCellComponent F B α y =
      sigmaCellComponent F B α x ≫ (sigmaMap F B g).map p := by
  apply toUnderlyingHom_injective (fiberRestriction F δ B)
  refine Grothendieck.ext _ _ ?_ ?_
  · exact (F.map₂ α).naturality p.base
  · apply eq_of_heq
    simp only [eqToHom_comp_heq_iff]
    apply HEq.trans (sigma_naturality_left_heq F B α p)
    apply HEq.trans _ (sigma_naturality_right_heq F B α p).symm
    rw [(B.map₂ (cartesianComparisonCell F α y.base)).naturality p.fiber]
    have he :
        (B.map (cartesianLift F f y.base ≫
          (fiberInclusion F δ).map ((F.map₂ α).app y.base))).obj
            ((B.map ((fiberInclusion F γ).map p.base)).obj x.fiber) =
        (B.map ((fiberInclusion F δ).map ((F.map g).map p.base))).obj
          ((B.map (cartesianLift F f x.base ≫
            (fiberInclusion F δ).map ((F.map₂ α).app x.base))).obj x.fiber) := by
      have h := congrArg (fun r => (B.map r).obj x.fiber)
        (cartesianComparisonCell_source F α p.base)
      simpa only [B.map_comp, classifier_comp_obj] using h
    apply heq_comp he rfl rfl _ HEq.rfl
    rw [StrictTwoTransformation.Trans.eqToHom_app]
    exact (cartesianComparisonCell_mapped_naturality_heq F B α p.base x.fiber).trans
      (comp_eqToHom_heq _ _).symm

/-- The underlying natural transformation induced by a genuine base cell.
Its higher naturality is a separate obligation. -/
def sigmaCellNaturalTransformation {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g) :
    (sigmaMap F B f).toFunctor ⟶ (sigmaMap F B g).toFunctor where
  app := sigmaCellComponent F B α
  naturality := fun _ _ p => sigmaCellComponent_naturality F B α p

end SquareKit.Internal.PathTransport.TwoFamily
