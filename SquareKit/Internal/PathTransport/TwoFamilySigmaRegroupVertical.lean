import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroupPrefix
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
private theorem prefix_paste_heq {C : Type*} [Bicategory C] [Strict C]
    {a b z : C} {f g : a ⟶ b} (h : f = g) {i j : b ⟶ z} (η : i ⟶ j)
    {l k : a ⟶ z} (c : l ⟶ k) (hi : k = f ≫ i) (hi' : k = g ≫ i) :
    HEq (c ≫ eqToHom hi ≫ f ◁ η) (c ≫ eqToHom hi' ≫ g ◁ η) := by
  cases h
  rfl

theorem sigmaRegroupCell_comp {x y : Total (sigmaFamily F B)} {p q r : x ⟶ y}
    (α : p ⟶ q) (β : q ⟶ r) :
    sigmaRegroupCell F B (α ≫ β) = sigmaRegroupCell F B α ≫ sigmaRegroupCell F B β := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (sigmaFirstCell_comp F B α β) ?_
  apply eq_of_heq
  simp only [heq_comp_eqToHom_iff]
  change HEq (eqToHom _ ◁ (α ≫ β).fiber.fiber ≫ eqToHom _)
    (sigmaRegroupCell F B α ≫ sigmaRegroupCell F B β).fiber
  apply HEq.trans (comp_eqToHom_heq _ _)
  rw [fiber_comp α β]
  change HEq (eqToHom _ ◁ (α.fiber ≫ sigmaCellComponent F B α.base x.fiber ◁
    β.fiber ≫ eqToHom _).fiber) _
  rw [fiber_comp (sigmaRegroupCell F B α) (sigmaRegroupCell F B β)]
  rw [fiber_comp α.fiber (sigmaCellComponent F B α.base x.fiber ◁ β.fiber ≫ eqToHom _)]
  rw [fiber_comp (sigmaCellComponent F B α.base x.fiber ◁ β.fiber) (eqToHom _)]
  simp only [total_eqToHom_fiber (fiberRestriction F y.base B),
    Bicategory.whiskerLeft_comp (B := B.obj ⟨y.base,y.fiber.base⟩),
    Bicategory.whiskerLeft_eqToHom (B := B.obj ⟨y.base,y.fiber.base⟩),
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  change HEq (eqToHom _ ◁ α.fiber.fiber ≫
    eqToHom _ ◁ ((fiberRestriction F y.base B).map₂ α.fiber.base).app
      ((sigmaMap F B p.base).obj x.fiber).fiber ◁
      (compBoundary (fiberRestriction F y.base B) _ _ _ ◁
        (((fiberRestriction F y.base B).map q.fiber.base).map
          (sigmaCellComponent F B α.base x.fiber).fiber ◁ β.fiber.fiber) ≫ eqToHom _) ≫ eqToHom _)
    ((eqToHom _ ◁ α.fiber.fiber ≫ eqToHom _) ≫
      (B.map₂ (sigmaRegroupBaseCell F B α)).app x.fiber.fiber ◁
        (eqToHom _ ◁ β.fiber.fiber ≫ eqToHom _) ≫ eqToHom _)
  simp only [Bicategory.whiskerLeft_comp (B := B.obj ⟨y.base,y.fiber.base⟩),
    Bicategory.whiskerLeft_eqToHom (B := B.obj ⟨y.base,y.fiber.base⟩),
    nested_whiskerLeft (B := B.obj ⟨y.base,y.fiber.base⟩),
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
  simp only [← Category.assoc]
  apply HEq.trans (comp_eqToHom_heq _ _)
  apply HEq.trans _ (comp_eqToHom_heq _ _).symm
  simp only [Category.assoc]
  change HEq
    ((eqToHom (sigmaRegroupBoundary F B p.base p.fiber.base) ◁ α.fiber.fiber) ≫ eqToHom _ ≫
      (eqToHom (sigmaRegroupBoundary F B p.base p.fiber.base) ≫
        ((fiberRestriction F y.base B).map₂ α.fiber.base).app
          ((sigmaMap F B p.base).obj x.fiber).fiber ≫
        compBoundary (fiberRestriction F y.base B) ((F.map₂ α.base).app x.fiber.base)
          q.fiber.base ((sigmaMap F B p.base).obj x.fiber).fiber ≫
        ((fiberRestriction F y.base B).map q.fiber.base).map
          (sigmaCellComponent F B α.base x.fiber).fiber) ◁ β.fiber.fiber)
    ((eqToHom (sigmaRegroupBoundary F B p.base p.fiber.base) ◁ α.fiber.fiber) ≫ eqToHom _ ≫
      ((B.map₂ (sigmaRegroupBaseCell F B α)).app x.fiber.fiber ≫
        eqToHom (sigmaRegroupBoundary F B q.base q.fiber.base)) ◁ β.fiber.fiber)
  exact prefix_paste_heq (sigmaRegroupPrefix F B (sigmaRegroupBaseCell F B α))
    β.fiber.fiber (eqToHom (sigmaRegroupBoundary F B p.base p.fiber.base) ◁ α.fiber.fiber) _ _

end SquareKit.Internal.PathTransport.TwoFamily
