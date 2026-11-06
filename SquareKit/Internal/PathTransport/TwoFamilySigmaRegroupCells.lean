import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroup
import SquareKit.Internal.PathTransport.TwoFamilyCartesianFactorization
import SquareKit.Internal.PathTransport.TwoFamilySigmaProjection
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

def sigmaRegroupBaseCell {x y : Total (sigmaFamily F B)} {p q : x ⟶ y} (α : p ⟶ q) :
    sigmaRegroupBase F B p ⟶ sigmaRegroupBase F B q := ⟨α.base,α.fiber.base⟩

private theorem classifier_comp_app {A C : StrictTwoCategory.{uB,vB,wB}}
    {H I J : A ⟶ C} (α : H ⟶ I) (β : I ⟶ J) (x : A) :
    (α ≫ β).app x = α.app x ≫ β.app x := rfl

def sigmaRegroupCell {x y : Total (sigmaFamily F B)} {p q : x ⟶ y} (α : p ⟶ q) :
    sigmaRegroupMap F B p ⟶ sigmaRegroupMap F B q := by
  refine ⟨sigmaRegroupBaseCell F B α,
    eqToHom (sigmaRegroupBoundary F B p.base p.fiber.base) ◁ α.fiber.fiber ≫ eqToHom ?_⟩
  change eqToHom _ ≫
    ((fiberRestriction F y.base B).map₂ α.fiber.base).app ((sigmaMap F B p.base).obj x.fiber).fiber ≫
      ((sigmaCellComponent F B α.base x.fiber ≫ q.fiber).fiber) =
    (B.map₂ (sigmaRegroupBaseCell F B α)).app x.fiber.fiber ≫
      (eqToHom _ ≫ q.fiber.fiber)
  rw [← cartesianCellFactorization_eq F (sigmaRegroupBaseCell F B α)]
  simp only [cartesianCellFactorization, B.map₂_comp, B.map₂_eqToHom,
    classifier_comp_app, StrongMap.classifier_eqToHom_app]
  change eqToHom _ ≫
    ((fiberRestriction F y.base B).map₂ α.fiber.base).app ((sigmaMap F B p.base).obj x.fiber).fiber ≫
      ((sigmaCellComponent F B α.base x.fiber ≫ q.fiber).fiber) =
    (eqToHom _ ≫
      (B.map₂ (cartesianLift F p.base x.fiber.base ◁
        (fiberInclusion F y.base).map₂ α.fiber.base)).app x.fiber.fiber ≫
      eqToHom _ ≫
      (B.map₂ (cartesianComparisonCell F α.base x.fiber.base ▷
        (fiberInclusion F y.base).map q.fiber.base)).app x.fiber.fiber ≫
      eqToHom _) ≫ eqToHom _ ≫ q.fiber.fiber
  rw [action_whiskerLeft, action_whiskerRight]
  change eqToHom _ ≫
    (B.map₂ ((fiberInclusion F y.base).map₂ α.fiber.base)).app
      ((B.map (cartesianLift F p.base x.fiber.base)).obj x.fiber.fiber) ≫
    (eqToHom _ ≫ (B.map ((fiberInclusion F y.base).map q.fiber.base)).map
      (eqToHom _ ≫ (B.map₂ (cartesianComparisonCell F α.base x.fiber.base)).app x.fiber.fiber) ≫
      q.fiber.fiber) = _
  rw [(B.map ((fiberInclusion F y.base).map q.fiber.base)).map_comp, StrongMap.map_eqToHom]
  simp only [compBoundary, Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

theorem sigmaRegroupCell_fiber_heq {x y : Total (sigmaFamily F B)}
    {p q : x ⟶ y} (α : p ⟶ q) :
    HEq (sigmaRegroupCell F B α).fiber α.fiber.fiber := by
  change HEq (eqToHom _ ◁ α.fiber.fiber ≫ eqToHom _) _
  exact (comp_eqToHom_heq _ _).trans (eqToHom_left_heq _ _)

private theorem castsFrom_heq {C : Type*} [Category C] {a b c : C}
    (h : a = b) (k : a = c) : HEq (eqToHom h) (eqToHom k) := by
  cases h
  cases k
  rfl

theorem sigmaRegroupCell_id {x y : Total (sigmaFamily F B)} (p : x ⟶ y) :
    sigmaRegroupCell F B (𝟙 p) = 𝟙 (sigmaRegroupMap F B p) := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (sigmaFirstCell_id F B p) ?_
  change (eqToHom _ ◁ (eqToHom (rfl : p = p)).fiber.fiber ≫ eqToHom _) = _
  apply eq_of_heq
  simp only [heq_comp_eqToHom_iff]
  apply HEq.trans (comp_eqToHom_heq _ _)
  rw [total_eqToHom_fiber (sigmaFamily F B),
    total_eqToHom_fiber (fiberRestriction F y.base B), Bicategory.whiskerLeft_eqToHom]
  change HEq (eqToHom _) (eqToHom (rfl : sigmaRegroupMap F B p = _)).fiber
  symm
  apply HEq.trans (heq_of_eq (total_eqToHom_fiber B (rfl : sigmaRegroupMap F B p = _)))
  exact castsFrom_heq _ _
end SquareKit.Internal.PathTransport.TwoFamily
