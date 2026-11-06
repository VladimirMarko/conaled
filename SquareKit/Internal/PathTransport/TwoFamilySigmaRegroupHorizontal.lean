import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroupVertical
import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroupMapLaws
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
private theorem cell_cast_fiber_heq {C : Type*} [Bicategory C] [Strict C] (H : Family C)
    {x y : Total H} {p p' q q' : x ⟶ y} (hp : p = p') (hq : q = q') (α : p' ⟶ q') :
    HEq (eqToHom hp ≫ α ≫ eqToHom hq.symm).fiber α.fiber := by
  cases hp; cases hq
  simp only [eqToHom_refl]
  rw [Category.comp_id α, Category.id_comp α]

private theorem cell_postcast_fiber_heq {C : Type*} [Bicategory C] [Strict C] (H : Family C)
    {x y : Total H} {p q q' : x ⟶ y} (α : p ⟶ q) (e : q = q') :
    HEq (α ≫ eqToHom e).fiber α.fiber := by
  cases e
  simp only [eqToHom_refl]
  rw [Category.comp_id α]

private theorem object_cast_left_cell_fiber_heq {C : Type*} [Bicategory C] [Strict C]
    (H : Family C) {x x' y : Total H} (e : x = x') {p q : x' ⟶ y} (α : p ⟶ q) :
    HEq (eqToHom e ◁ α).fiber α.fiber := by
  cases e
  change HEq (𝟙 x ◁ α).fiber α.fiber
  have h := Bicategory.id_whiskerLeft α
  simp only [Strict.leftUnitor_eqToIso, eqToIso.hom, eqToIso.inv] at h
  exact (congr_arg_heq (fun τ => τ.fiber) h).trans (cell_cast_fiber_heq H (Category.id_comp p) (Category.id_comp q) α)

private theorem left_fiber_heq {C : Type*} [Bicategory C] [Strict C]
    (H : Family C) {x y z : Total H} (p : x ⟶ y) {q r : y ⟶ z} (α : q ⟶ r) :
    HEq (p ◁ α).fiber ((H.map q.base).map p.fiber ◁ α.fiber) := by
  change HEq (eqToHom _ ◁ (_ ◁ α.fiber) ≫ eqToHom _) _
  exact (comp_eqToHom_heq _ _).trans (eqToHom_left_heq _ _)

private theorem mapped_source_cast_left_heq {C D : Type*} [Bicategory C] [Strict C] [Bicategory D] [Strict D]
    (H : StrictPseudofunctor C D) {a a' b : C} (e : a = a') (v : a' ⟶ b)
    {z : D} {r s : H.obj b ⟶ z} (α : r ⟶ s) :
    HEq (H.map (eqToHom e ≫ v) ◁ α) (H.map v ◁ α) := by
  cases e
  rw [eqToHom_refl, Category.id_comp v]

private theorem whisker_postcast_heq {C : Type*} [Bicategory C]
    {a b c : C} (p : a ⟶ b) {q r s : b ⟶ c} (α : q ⟶ r) (e : r = s) :
    HEq (p ◁ (α ≫ eqToHom e)) (p ◁ α) := by
  cases e
  rw [eqToHom_refl, Category.comp_id α]

private theorem map_cell_paste_heq {C D : Type*} [Bicategory C] [Strict C] [Bicategory D] [Strict D]
    (H K : StrictPseudofunctor C D) (h : H = K) {a b : C} (v : a ⟶ b)
    {z : D} {p q : K.obj b ⟶ z} (α : p ⟶ q) :
    HEq ((H.map v ≫ eqToHom (congrArg (fun L => L.obj b) h)) ◁ α) (K.map v ◁ α) := by
  cases h
  rw [eqToHom_refl, Category.comp_id]

private theorem nested_left_heq {C : Type*} [Bicategory C] [Strict C]
    {a b c d : C} (p : a ⟶ b) (q : b ⟶ c) {r s : c ⟶ d} (α : r ⟶ s) :
    HEq (p ◁ q ◁ α) ((p ≫ q) ◁ α) := by
  rw [nested_whiskerLeft]
  apply HEq.trans (eqToHom_comp_heq _ _)
  exact comp_eqToHom_heq _ _

theorem sigmaRegroup_left_fiber {x y z : Total (sigmaFamily F B)}
    (p : x ⟶ y) {q r : y ⟶ z} (α : q ⟶ r) :
    HEq (p ◁ α).fiber.fiber
      (sigmaRegroupMap F B p ◁ sigmaRegroupCell F B α).fiber := by
  change HEq ((eqToHom _ ◁ ((sigmaMap F B q.base).map p.fiber ◁ α.fiber) ≫ eqToHom _).fiber) _
  apply HEq.trans (cell_postcast_fiber_heq (fiberRestriction F z.base B) _ _)
  apply HEq.trans (object_cast_left_cell_fiber_heq (fiberRestriction F z.base B) _ _)
  apply HEq.trans (left_fiber_heq (fiberRestriction F z.base B) _ _)
  apply HEq.trans _ (left_fiber_heq B _ _).symm
  change HEq
    ((B.map ((fiberInclusion F z.base).map q.fiber.base)).map
      ((eqToHom ((sigmaTransportComparison F B q.base).naturality p.fiber.base).symm).app
        ((sigmaMap F B p.base).obj x.fiber).fiber ≫
        (B.map (cartesianLift F q.base y.fiber.base)).map p.fiber.fiber) ◁ α.fiber.fiber)
    ((B.map (sigmaRegroupBase F B q)).map (eqToHom _ ≫ p.fiber.fiber) ◁
      (eqToHom _ ◁ α.fiber.fiber ≫ eqToHom _))
  rw [StrictTwoTransformation.Trans.eqToHom_app]
  apply HEq.trans (mapped_source_cast_left_heq _ _ _ _)
  apply HEq.trans _ (mapped_source_cast_left_heq _ _ _ _).symm
  apply HEq.trans _ (whisker_postcast_heq _ _ _).symm
  apply HEq.trans _ (nested_left_heq _ _ _).symm
  exact (map_cell_paste_heq _ _ (sigmaRegroupTransport F B q) p.fiber.fiber α.fiber.fiber).symm
theorem sigmaRegroupCell_whiskerLeft {x y z : Total (sigmaFamily F B)}
    (p : x ⟶ y) {q r : y ⟶ z} (α : q ⟶ r) :
    sigmaRegroupCell F B (p ◁ α) =
      eqToHom (sigmaRegroupMap_comp F B p q) ≫
        sigmaRegroupMap F B p ◁ sigmaRegroupCell F B α ≫
          eqToHom (sigmaRegroupMap_comp F B p r).symm := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · change (sigmaFirst F B).map₂ (p ◁ α) = (projectionHigher B).map₂
      (eqToHom (sigmaRegroupMap_comp F B p q) ≫
        sigmaRegroupMap F B p ◁ sigmaRegroupCell F B α ≫
          eqToHom (sigmaRegroupMap_comp F B p r).symm)
    rw [PrelaxFunctor.map₂_comp, PrelaxFunctor.map₂_comp,
      PrelaxFunctor.map₂_eqToHom, PrelaxFunctor.map₂_eqToHom]
    change (sigmaFirst F B).map₂ (p ◁ α) =
      eqToHom (sigmaFirstMap_comp F B p q) ≫
        (sigmaFirst F B).map p ◁ (sigmaFirst F B).map₂ α ≫
          eqToHom (sigmaFirstMap_comp F B p r).symm
    simpa only [(sigmaFirst F B).mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv] using
      (sigmaFirst F B).map₂_whisker_left p α
  · apply eq_of_heq
    simp only [heq_comp_eqToHom_iff]
    exact (sigmaRegroupCell_fiber_heq F B (p ◁ α)).trans
      ((sigmaRegroup_left_fiber F B p α).trans
        (cell_cast_fiber_heq B (sigmaRegroupMap_comp F B p q)
          (sigmaRegroupMap_comp F B p r) _).symm)
private theorem cell_precast_fiber_heq {C : Type*} [Bicategory C] [Strict C] (H : Family C)
    {x y : Total H} {p p' q : x ⟶ y} (e : p = p') (α : p' ⟶ q) :
    HEq (eqToHom e ≫ α).fiber α.fiber := by
  cases e
  simp only [eqToHom_refl]
  rw [Category.id_comp α]

private theorem object_cast_right_fiber_heq {C : Type*} [Bicategory C] [Strict C]
    (H : Family C) {x x' y z : Total H} (e : x = x') {p q : x' ⟶ y}
    (α : p ⟶ q) (r : y ⟶ z) :
    HEq ((eqToHom e ◁ α) ▷ r).fiber (α ▷ r).fiber := by
  have h := Bicategory.whisker_assoc (eqToHom e) α r
  simp only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv] at h
  apply HEq.trans (congr_arg_heq (fun τ => τ.fiber) h)
  apply HEq.trans (cell_precast_fiber_heq H _ _)
  apply HEq.trans (cell_postcast_fiber_heq H _ _)
  exact object_cast_left_cell_fiber_heq H e (α ▷ r)

private theorem boundary_right_heq {C : Type*} [Bicategory C] [Strict C]
    {x y z t : C} (e : x = y) {p q : y ⟶ z} (α : p ⟶ q) (r : z ⟶ t) :
    HEq ((eqToHom e ◁ α) ▷ r) (α ▷ r) := by
  rw [Bicategory.whisker_assoc]
  simp only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv]
  apply HEq.trans (eqToHom_comp_heq _ _)
  apply HEq.trans (comp_eqToHom_heq _ _)
  exact eqToHom_left_heq _ _

private theorem right_fiber_heq {C : Type*} [Bicategory C] [Strict C]
    (H : Family C) {x y z : Total H} {p q : x ⟶ y} (α : p ⟶ q) (r : y ⟶ z) :
    HEq (α ▷ r).fiber ((H.map r.base).map₂ α.fiber ▷ r.fiber) := by
  change HEq (eqToHom _ ≫ (eqToHom _ ◁ (H.map r.base).map₂ α.fiber) ▷ r.fiber ≫ eqToHom _) _
  apply HEq.trans (eqToHom_comp_heq _ _)
  apply HEq.trans (comp_eqToHom_heq _ _)
  exact boundary_right_heq _ _ _

set_option maxHeartbeats 1200000 in
theorem sigmaWhiskerRight_second_heq {x y z : Total (sigmaFamily F B)}
    {p q : x ⟶ y} (α : p ⟶ q) (r : y ⟶ z) :
    HEq (α ▷ r).fiber.fiber
      (((fiberRestriction F z.base B).map r.fiber.base).map₂
        ((sigmaMap F B r.base).map₂ α.fiber).fiber ▷ r.fiber.fiber) := by
  change HEq ((eqToHom _ ≫
    (eqToHom _ ◁ (sigmaMap F B r.base).map₂ α.fiber) ▷ r.fiber ≫ eqToHom _).fiber) _
  apply HEq.trans (cell_precast_fiber_heq (fiberRestriction F z.base B) _ _)
  apply HEq.trans (cell_postcast_fiber_heq (fiberRestriction F z.base B) _ _)
  apply HEq.trans (object_cast_right_fiber_heq (fiberRestriction F z.base B) _ _ _)
  apply HEq.trans (right_fiber_heq (fiberRestriction F z.base B) _ _)
  rfl
theorem sigmaRegroup_right_target_heq {x y z : Total (sigmaFamily F B)}
    {p q : x ⟶ y} (α : p ⟶ q) (r : y ⟶ z) :
    HEq (sigmaRegroupCell F B α ▷ sigmaRegroupMap F B r).fiber
      ((B.map (sigmaRegroupMap F B r).base).map₂ (sigmaRegroupCell F B α).fiber ▷
        (sigmaRegroupMap F B r).fiber) := right_fiber_heq B _ _
end SquareKit.Internal.PathTransport.TwoFamily
