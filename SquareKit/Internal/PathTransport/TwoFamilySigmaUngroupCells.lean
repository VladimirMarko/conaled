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
def sigmaUngroupCell {x y : Total B} {p q : x ⟶ y} (α : p ⟶ q) :
    sigmaUngroupMap F B p ⟶ sigmaUngroupMap F B q := by
  refine ⟨α.base.base,⟨α.base.fiber,
    eqToHom (sigmaRegroupBoundary F B (x := sigmaUngroupObj F B x)
      (y := sigmaUngroupObj F B y) p.base.base p.base.fiber).symm ◁ α.fiber ≫ eqToHom ?_⟩⟩
  have h := sigmaRegroupPrefix F B (p := sigmaUngroupMap F B p)
    (q := sigmaUngroupMap F B q) α.base
  have h' := congrArg (fun k =>
    eqToHom (sigmaRegroupBoundary F B (x := sigmaUngroupObj F B x)
      (y := sigmaUngroupObj F B y) p.base.base p.base.fiber).symm ≫ k ≫
      (sigmaUngroupMap F B q).fiber.fiber) h
  change eqToHom _ ≫ (B.map₂ α.base).app x.fiber ≫ q.fiber =
    ((fiberRestriction F y.base.base B).map₂ α.base.fiber).app
      ((sigmaMap F B p.base.base).obj (sigmaUngroupObj F B x).fiber).fiber ≫
      (compBoundary (fiberRestriction F y.base.base B)
        ((F.map₂ α.base.base).app x.base.fiber) q.base.fiber _ ≫
        ((fiberRestriction F y.base.base B).map q.base.fiber).map
          (sigmaCellComponent F B α.base.base (sigmaUngroupObj F B x).fiber).fiber ≫
        (sigmaUngroupMap F B q).fiber.fiber)
  simpa only [sigmaUngroupMap, sigmaUngroupObj, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp] using h'.symm

theorem sigmaUngroupCell_fiber_heq {x y : Total B} {p q : x ⟶ y} (α : p ⟶ q) :
    HEq (sigmaUngroupCell F B α).fiber.fiber α.fiber := by
  change HEq (eqToHom _ ◁ α.fiber ≫ eqToHom _) _
  exact (comp_eqToHom_heq _ _).trans (eqToHom_left_heq _ _)

theorem sigmaRegroupCell_ungroup_heq {x y : Total B} {p q : x ⟶ y} (α : p ⟶ q) :
    HEq (sigmaRegroupCell F B (sigmaUngroupCell F B α)) α := by
  apply total_cell_hext B rfl rfl (heq_of_eq (sigmaRegroupMap_ungroup F B p))
    (heq_of_eq (sigmaRegroupMap_ungroup F B q))
  · rfl
  · exact (sigmaRegroupCell_fiber_heq F B (sigmaUngroupCell F B α)).trans
      (sigmaUngroupCell_fiber_heq F B α)

end SquareKit.Internal.PathTransport.TwoFamily
