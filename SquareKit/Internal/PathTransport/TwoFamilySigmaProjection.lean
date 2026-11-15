import SquareKit.Internal.PathTransport.TwoFamilySigmaFamily
import SquareKit.Internal.PathTransport.TwoFamilySections

/-! The first dependent-pair projection preserves the full higher structure. -/
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

private theorem total_obj_eqToHom_base {C : Type*} [Bicategory C] [Strict C]
    (H : Family C) {x y : Total H} (e : x = y) :
    (eqToHom e).base = eqToHom (congrArg Total.base e) := by
  cases e
  rfl

def sigmaFirstObj (x : Total (sigmaFamily F B)) : Total F := ⟨x.base,x.fiber.base⟩
def sigmaFirstMap {x y : Total (sigmaFamily F B)} (p : x ⟶ y) :
    sigmaFirstObj F B x ⟶ sigmaFirstObj F B y := ⟨p.base,p.fiber.base⟩
def sigmaFirstCell {x y : Total (sigmaFamily F B)} {p q : x ⟶ y} (α : p ⟶ q) :
    sigmaFirstMap F B p ⟶ sigmaFirstMap F B q := ⟨α.base,α.fiber.base⟩

theorem sigmaFirstMap_id (x : Total (sigmaFamily F B)) :
    sigmaFirstMap F B (𝟙 x) = 𝟙 (sigmaFirstObj F B x) := by
  apply Pseudofunctor.CoGrothendieck.ext
  · rfl
  · change HEq (identity (sigmaFamily F B) x).fiber.base
      (identity F (sigmaFirstObj F B x)).fiber
    dsimp only [identity, TwoGroupoidHom.arrow]
    rw [total_obj_eqToHom_base]

theorem sigmaFirstMap_comp {x y z : Total (sigmaFamily F B)} (p : x ⟶ y) (q : y ⟶ z) :
    sigmaFirstMap F B (p ≫ q) = sigmaFirstMap F B p ≫ sigmaFirstMap F B q := by
  apply Pseudofunctor.CoGrothendieck.ext
  · rfl
  · change HEq (compose (sigmaFamily F B) p q).fiber.base
      (compose F (sigmaFirstMap F B p) (sigmaFirstMap F B q)).fiber
    dsimp only [compose, TwoGroupoidHom.arrow]
    change HEq ((eqToHom _ : (sigmaMap F B (p.base ≫ q.base)).obj _ ⟶ _).base ≫ _ ≫ _) _
    rw [total_obj_eqToHom_base]
    rfl

theorem sigmaFirstCell_id {x y : Total (sigmaFamily F B)} (p : x ⟶ y) :
    sigmaFirstCell F B (𝟙 p) = 𝟙 (sigmaFirstMap F B p) := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
  change (projectionHigher (fiberRestriction F y.base B)).map₂
    (eqToHom (rfl : p = p)).fiber = _
  rw [total_eqToHom_fiber, PrelaxFunctor.map₂_eqToHom]
  change eqToHom _ = (eqToHom (rfl : sigmaFirstMap F B p = _)).fiber ≫ eqToHom _
  rw [total_eqToHom_fiber, eqToHom_trans]

theorem sigmaFirstCell_comp {x y : Total (sigmaFamily F B)} {p q r : x ⟶ y}
    (α : p ⟶ q) (β : q ⟶ r) :
    sigmaFirstCell F B (α ≫ β) = sigmaFirstCell F B α ≫ sigmaFirstCell F B β := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
  change (projectionHigher (fiberRestriction F y.base B)).map₂ (α ≫ β).fiber = _
  rw [fiber_comp, PrelaxFunctor.map₂_comp, PrelaxFunctor.map₂_comp,
    PrelaxFunctor.map₂_eqToHom]
  rw [Pseudofunctor.map₂_whisker_left]
  simp only [(projectionHigher (fiberRestriction F y.base B)).mapComp_eq_eqToIso,
    eqToIso.hom, eqToIso.inv]
  change _ = (sigmaFirstCell F B α ≫ sigmaFirstCell F B β).fiber ≫ eqToHom _
  rw [fiber_comp]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

private theorem first_cell_cast_heq (H : Family Γ) {x y : Total H}
    {p p' q q' : x ⟶ y} (hp : p = p') (hq : q = q') (α : p' ⟶ q') :
    HEq (eqToHom hp ≫ α ≫ eqToHom hq.symm).fiber α.fiber := by
  cases hp
  cases hq
  simp only [eqToHom_refl]
  rw [Category.comp_id α, Category.id_comp α]

private theorem first_map_eqToHom {C D : Type*} [Bicategory C] [Bicategory D]
    (H : StrictPseudofunctor C D) {x y : C} (e : x = y) :
    H.map (eqToHom e) = eqToHom (congrArg H.obj e) := by
  cases e
  exact H.map_id x

private theorem mapped_boundary_whisker_heq {C D : Type*} [Bicategory C] [Bicategory D] [Strict D]
    (H : StrictPseudofunctor C D) {x y : C} (e : x = y) {z : D}
    {p q : H.obj y ⟶ z} (α : p ⟶ q) : HEq (H.map (eqToHom e) ◁ α) α := by
  rw [first_map_eqToHom]
  exact eqToHom_left_heq _ _

private theorem mapped_whiskerRight_heq {C D : Type*} [Bicategory C] [Bicategory D]
    (H : StrictPseudofunctor C D) {x y z : C} {p q : x ⟶ y} (α : p ⟶ q) (r : y ⟶ z) :
    HEq (H.map₂ (α ▷ r)) (H.map₂ α ▷ H.map r) := by
  rw [H.map₂_whisker_right, H.mapComp_eq_eqToIso, H.mapComp_eq_eqToIso]
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

private theorem first_boundary_right_heq {C : Type*} [Bicategory C] [Strict C]
    {x y z t : C} (e : x = y) {p q : y ⟶ z} (α : p ⟶ q) (r : z ⟶ t) :
    HEq ((eqToHom e ◁ α) ▷ r) (α ▷ r) := by
  rw [Bicategory.whisker_assoc]
  simp only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv]
  apply HEq.trans (eqToHom_comp_heq _ _)
  apply HEq.trans (comp_eqToHom_heq _ _)
  exact eqToHom_left_heq _ _

private theorem mapped_boundary_right_heq {C D : Type*} [Bicategory C] [Bicategory D] [Strict D]
    (H : StrictPseudofunctor C D) {x y : C} (e : x = y) {z t : D}
    {p q : H.obj y ⟶ z} (α : p ⟶ q) (r : z ⟶ t) :
    HEq ((H.map (eqToHom e) ◁ α) ▷ r) (α ▷ r) := by
  rw [first_map_eqToHom]
  exact first_boundary_right_heq _ _ _

private theorem mapped_whiskerLeft_heq {C D : Type*} [Bicategory C] [Bicategory D]
    (H : StrictPseudofunctor C D) {x y z : C} (p : x ⟶ y) {q r : y ⟶ z} (α : q ⟶ r) :
    HEq (H.map₂ (p ◁ α)) (H.map p ◁ H.map₂ α) := by
  rw [H.map₂_whisker_left, H.mapComp_eq_eqToIso, H.mapComp_eq_eqToIso]
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

/-- The first projection of a dependent pair retains every dimension. -/
def sigmaFirst : StrictPseudofunctor (Total (sigmaFamily F B)) (Total F) :=
  StrictPseudofunctor.mk'' {
    obj := sigmaFirstObj F B
    map := sigmaFirstMap F B
    map₂ := sigmaFirstCell F B
    map_id := sigmaFirstMap_id F B
    map_comp := sigmaFirstMap_comp F B
    map₂_id := sigmaFirstCell_id F B
    map₂_comp := sigmaFirstCell_comp F B
    map₂_whisker_left := by
      intro x y z p q r α
      refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
      · change p.base ◁ α.base = (projectionHigher F).map₂
          (eqToHom (sigmaFirstMap_comp F B p q) ≫
            sigmaFirstMap F B p ◁ sigmaFirstCell F B α ≫
              eqToHom (sigmaFirstMap_comp F B p r).symm)
        rw [PrelaxFunctor.map₂_comp, PrelaxFunctor.map₂_comp,
          PrelaxFunctor.map₂_eqToHom, PrelaxFunctor.map₂_eqToHom]
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl
      · apply eq_of_heq
        simp only [heq_comp_eqToHom_iff]
        change HEq ((projectionHigher (fiberRestriction F z.base B)).map₂
          (whiskerLeft (sigmaFamily F B) p α).fiber) _
        apply HEq.trans (b := (whiskerLeft F (sigmaFirstMap F B p) (sigmaFirstCell F B α)).fiber)
        · dsimp only [whiskerLeft, TwoGroupoidHom.cell]
          rw [PrelaxFunctor.map₂_comp, PrelaxFunctor.map₂_eqToHom]
          simp only [comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
          apply HEq.trans (mapped_whiskerLeft_heq _ _ _)
          simp only [compBoundary]
          apply HEq.trans (mapped_boundary_whisker_heq _ _ _)
          apply HEq.trans (mapped_whiskerLeft_heq _ _ _)
          exact (eqToHom_left_heq _ _).symm
        · exact (first_cell_cast_heq F (sigmaFirstMap_comp F B p q)
            (sigmaFirstMap_comp F B p r) _).symm
    map₂_whisker_right := by
      intro x y z p q α r
      refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
      · change α.base ▷ r.base = (projectionHigher F).map₂
          (eqToHom (sigmaFirstMap_comp F B p r) ≫
            sigmaFirstCell F B α ▷ sigmaFirstMap F B r ≫
              eqToHom (sigmaFirstMap_comp F B q r).symm)
        rw [PrelaxFunctor.map₂_comp, PrelaxFunctor.map₂_comp,
          PrelaxFunctor.map₂_eqToHom, PrelaxFunctor.map₂_eqToHom]
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl
      · apply eq_of_heq
        simp only [heq_comp_eqToHom_iff]
        change HEq ((projectionHigher (fiberRestriction F z.base B)).map₂
          (whiskerRight (sigmaFamily F B) α r).fiber) _
        apply HEq.trans (b := (whiskerRight F (sigmaFirstCell F B α) (sigmaFirstMap F B r)).fiber)
        · dsimp only [whiskerRight, TwoGroupoidHom.cell]
          rw [PrelaxFunctor.map₂_comp, PrelaxFunctor.map₂_comp,
            PrelaxFunctor.map₂_eqToHom, PrelaxFunctor.map₂_eqToHom]
          simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
            heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
          apply HEq.trans (mapped_whiskerRight_heq _ _ _)
          rw [Pseudofunctor.map₂_whisker_left]
          simp only [(projectionHigher (fiberRestriction F z.base B)).mapComp_eq_eqToIso,
            eqToIso.hom, eqToIso.inv, Bicategory.comp_whiskerRight,
            Bicategory.eqToHom_whiskerRight, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
          simp only [compBoundary]
          apply HEq.trans (mapped_boundary_right_heq _ _ _ _)
          exact (first_boundary_right_heq _ _ _).symm
        · exact (first_cell_cast_heq F (sigmaFirstMap_comp F B p r)
            (sigmaFirstMap_comp F B q r) _).symm
  }

/-- The first projection commutes with the ambient context projection. -/
theorem sigmaFirst_projection :
    (sigmaFirst F B).comp (projectionHigher F) = projectionHigher (sigmaFamily F B) :=
  StrictTwoTransformation.functor_ext rfl

/-- The first pair component is retained as an object of the earlier family. -/
theorem sigmaFirst_obj_fiber (x : Total (sigmaFamily F B)) :
    ((sigmaFirst F B).obj x).fiber = x.fiber.base := rfl

/-- The first fiber arrow is the supplied component, including its dependent boundary. -/
theorem sigmaFirst_map_fiber {x y : Total (sigmaFamily F B)} (p : x ⟶ y) :
    ((sigmaFirst F B).map p).fiber = p.fiber.base := rfl

/-- The first genuine fiber cell is retained by the projection. -/
theorem sigmaFirst_cell_fiber {x y : Total (sigmaFamily F B)} {p q : x ⟶ y} (α : p ⟶ q) :
    ((sigmaFirst F B).map₂ α).fiber = α.fiber.base := rfl

/-- Project an actual dependent-pair section in every dimension. -/
def Section.sigmaFirst (s : Section (sigmaFamily F B)) : Section F where
  lift := s.lift.comp (TwoFamily.sigmaFirst F B)
  over := by
    calc
      (s.lift.comp (TwoFamily.sigmaFirst F B)).comp (projectionHigher F) =
          s.lift.comp ((TwoFamily.sigmaFirst F B).comp (projectionHigher F)) :=
        StrictTwoTransformation.functor_ext rfl
      _ = s.lift.comp (projectionHigher (sigmaFamily F B)) :=
        congrArg (fun H => s.lift.comp H) (sigmaFirst_projection F B)
      _ = StrictPseudofunctor.id Γ := s.over

end SquareKit.Internal.PathTransport.TwoFamily
