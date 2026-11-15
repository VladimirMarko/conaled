import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroupCells
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
private theorem classifier_comp_app {A C : StrictTwoCategory.{uB,vB,wB}}
    {H I J : A ⟶ C} (α : H ⟶ I) (β : I ⟶ J) (x : A) :
    (α ≫ β).app x = α.app x ≫ β.app x := rfl

theorem sigmaRegroupPrefix {x y : Total (sigmaFamily F B)} {p q : x ⟶ y}
    (θ : sigmaRegroupBase F B p ⟶ sigmaRegroupBase F B q) :
    eqToHom (sigmaRegroupBoundary F B p.base p.fiber.base) ≫
      ((fiberRestriction F y.base B).map₂ θ.fiber).app
        ((sigmaMap F B p.base).obj x.fiber).fiber ≫
      compBoundary (fiberRestriction F y.base B)
        ((F.map₂ θ.base).app x.fiber.base) q.fiber.base
        ((sigmaMap F B p.base).obj x.fiber).fiber ≫
      ((fiberRestriction F y.base B).map q.fiber.base).map
        (sigmaCellComponent F B θ.base x.fiber).fiber =
    (B.map₂ θ).app x.fiber.fiber ≫
      eqToHom (sigmaRegroupBoundary F B q.base q.fiber.base) := by
  conv_rhs => rw [← cartesianCellFactorization_eq F θ]
  simp only [cartesianCellFactorization, B.map₂_comp, B.map₂_eqToHom,
    classifier_comp_app, StrongMap.classifier_eqToHom_app]
  change eqToHom _ ≫
    ((fiberRestriction F y.base B).map₂ θ.fiber).app ((sigmaMap F B p.base).obj x.fiber).fiber ≫
      compBoundary (fiberRestriction F y.base B) _ _ _ ≫
      ((fiberRestriction F y.base B).map q.fiber.base).map
        (sigmaCellComponent F B θ.base x.fiber).fiber =
    (eqToHom _ ≫
      (B.map₂ (cartesianLift F p.base x.fiber.base ◁
        (fiberInclusion F y.base).map₂ θ.fiber)).app x.fiber.fiber ≫
      eqToHom _ ≫
      (B.map₂ (cartesianComparisonCell F θ.base x.fiber.base ▷
        (fiberInclusion F y.base).map q.fiber.base)).app x.fiber.fiber ≫
      eqToHom _) ≫ eqToHom _
  rw [action_whiskerLeft, action_whiskerRight]
  change eqToHom _ ≫
    (B.map₂ ((fiberInclusion F y.base).map₂ θ.fiber)).app
      ((B.map (cartesianLift F p.base x.fiber.base)).obj x.fiber.fiber) ≫
    eqToHom _ ≫ (B.map ((fiberInclusion F y.base).map q.fiber.base)).map
      (eqToHom _ ≫ (B.map₂ (cartesianComparisonCell F θ.base x.fiber.base)).app x.fiber.fiber) = _
  rw [(B.map ((fiberInclusion F y.base).map q.fiber.base)).map_comp, StrongMap.map_eqToHom]
  simp only [compBoundary, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

end SquareKit.Internal.PathTransport.TwoFamily
