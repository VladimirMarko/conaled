import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroupHorizontal
import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroupMapLaws
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ uB vB wB
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))
private theorem boundary_right_heq {C : Type*} [Bicategory C] [Strict C]
    {x y z t : C} (e : x = y) {p q : y ⟶ z} (α : p ⟶ q) (r : z ⟶ t) :
    HEq ((eqToHom e ◁ α) ▷ r) (α ▷ r) := by
  rw [Bicategory.whisker_assoc]
  simp only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv]
  apply HEq.trans (eqToHom_comp_heq _ _)
  apply HEq.trans (comp_eqToHom_heq _ _)
  exact eqToHom_left_heq _ _

private theorem cast_whiskerRight_heq {C : Type*} [Bicategory C]
    {x y z : C} {p p' q q' : x ⟶ y} (hp : p = p') (hq : q' = q)
    (α : p' ⟶ q') (r : y ⟶ z) :
    HEq ((eqToHom hp ≫ α ≫ eqToHom hq) ▷ r) (α ▷ r) := by
  cases hp; cases hq
  simp only [eqToHom_refl]
  rw [Category.comp_id α, Category.id_comp α]

private theorem mapped_postcast_right_heq {C D : Type*} [Bicategory C] [Bicategory D]
    (H : StrictPseudofunctor C D) {x y : C} {p q q' : x ⟶ y}
    (α : p ⟶ q) (e : q = q') {z : D} (r : H.obj y ⟶ z) :
    HEq (H.map₂ (α ≫ eqToHom e) ▷ r) (H.map₂ α ▷ r) := by
  cases e
  rw [eqToHom_refl, Category.comp_id α]

private theorem mapped_boundary_right_heq {C D : Type*} [Bicategory C] [Strict C]
    [Bicategory D] [Strict D] (H : StrictPseudofunctor C D)
    {x x' y : C} (e : x = x') {p q : x' ⟶ y} (α : p ⟶ q)
    {z : D} (r : H.obj y ⟶ z) :
    HEq (H.map₂ (eqToHom e ◁ α) ▷ r) (H.map₂ α ▷ r) := by
  rw [H.map₂_whisker_left]
  simp only [H.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv]
  apply HEq.trans (cast_whiskerRight_heq _ _ _ _)
  have he : H.map (eqToHom e) = eqToHom (congrArg H.obj e) := by
    cases e
    exact H.map_id _
  rw [he]
  exact boundary_right_heq _ _ _

private theorem mapped_component_right_heq {C D E : Type*}
    [Bicategory C] [Strict C] [Bicategory D] [Strict D] [Bicategory E] [Strict E]
    {H K : StrictPseudofunctor C D} (e : H = K) (x : C)
    {y : D} {p q : K.obj x ⟶ y} (α : p ⟶ q)
    (G : StrictPseudofunctor D E) {z : E} (r : G.obj y ⟶ z) :
    HEq (G.map₂ ((eqToHom e).app x ◁ α) ▷ r) (G.map₂ α ▷ r) := by
  rw [StrictTwoTransformation.Trans.eqToHom_app]
  exact mapped_boundary_right_heq _ _ _ _

private theorem totalRightCast_base {C : Type*} [Bicategory C] [Strict C] (H : Family C)
    {x y z : Total H} {p q : x ⟶ y} (α : p ⟶ q) (r : y ⟶ z)
    {s t : x ⟶ z} (hs : s = p ≫ r) (ht : t = q ≫ r) :
    (eqToHom hs ≫ α ▷ r ≫ eqToHom ht.symm).base =
      eqToHom (congrArg (fun v : x ⟶ z => v.base) hs) ≫ α.base ▷ r.base ≫
        eqToHom (congrArg (fun v : x ⟶ z => v.base) ht).symm := by
  change (projectionHigher H).map₂ (eqToHom hs ≫ α ▷ r ≫ eqToHom ht.symm) = _
  rw [PrelaxFunctor.map₂_comp, PrelaxFunctor.map₂_comp,
    PrelaxFunctor.map₂_eqToHom, PrelaxFunctor.map₂_eqToHom]
  rfl

private theorem map_right_paste_heq {C D : Type*} [Bicategory C] [Strict C]
    [Bicategory D] [Strict D] (H K : StrictPseudofunctor C D) (h : H = K)
    {x y : C} {p q : x ⟶ y} (α : p ⟶ q) {z : D} (r : K.obj y ⟶ z) :
    HEq (H.map₂ α ▷ (eqToHom (congrArg (fun L => L.obj y) h) ≫ r))
      (K.map₂ α ▷ r) := by
  cases h
  rw [eqToHom_refl, Category.id_comp r]

theorem sigmaRegroup_right_fiber {x y z : Total (sigmaFamily F B)}
    {p q : x ⟶ y} (α : p ⟶ q) (r : y ⟶ z) :
    HEq (α ▷ r).fiber.fiber
      (sigmaRegroupCell F B α ▷ sigmaRegroupMap F B r).fiber := by
  apply HEq.trans (sigmaWhiskerRight_second_heq F B α r)
  apply HEq.trans _ (sigmaRegroup_right_target_heq F B α r).symm
  change HEq
    ((B.map ((fiberInclusion F z.base).map r.fiber.base)).map₂
      ((eqToHom ((sigmaTransportComparison F B r.base).naturality p.fiber.base).symm).app
        ((sigmaMap F B p.base).obj x.fiber).fiber ◁
        (B.map (cartesianLift F r.base y.fiber.base)).map₂ α.fiber.fiber ≫ eqToHom _) ▷ r.fiber.fiber)
    ((B.map (sigmaRegroupBase F B r)).map₂
      (eqToHom _ ◁ α.fiber.fiber ≫ eqToHom _) ▷ (eqToHom _ ≫ r.fiber.fiber))
  apply HEq.trans (mapped_postcast_right_heq _ _ _ _)
  apply HEq.trans (mapped_component_right_heq _ _ _ _ _)
  apply HEq.trans _ (mapped_postcast_right_heq _ _ _ _).symm
  apply HEq.trans _ (mapped_boundary_right_heq _ _ _ _).symm
  exact (map_right_paste_heq _ _ (sigmaRegroupTransport F B r) α.fiber.fiber r.fiber.fiber).symm
set_option maxHeartbeats 400000 in
theorem sigmaRegroupCell_whiskerRight {x y z : Total (sigmaFamily F B)}
    {p q : x ⟶ y} (α : p ⟶ q) (r : y ⟶ z) :
    sigmaRegroupCell F B (α ▷ r) =
      eqToHom (sigmaRegroupMap_comp F B p r) ≫
        sigmaRegroupCell F B α ▷ sigmaRegroupMap F B r ≫
          eqToHom (sigmaRegroupMap_comp F B q r).symm := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · have h := (sigmaFirst F B).map₂_whisker_right α r
    simp only [(sigmaFirst F B).mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv] at h
    exact h.trans (totalRightCast_base B (sigmaRegroupCell F B α)
      (sigmaRegroupMap F B r) (sigmaRegroupMap_comp F B p r)
        (sigmaRegroupMap_comp F B q r)).symm
  · apply eq_of_heq
    simp only [heq_comp_eqToHom_iff]
    apply HEq.trans (sigmaRegroupCell_fiber_heq F B (α ▷ r))
    apply HEq.trans (sigmaRegroup_right_fiber F B α r)
    have castFiber {x y : Total B} {p p' q q' : x ⟶ y}
        (hp : p = p') (hq : q = q') (β : p' ⟶ q') :
        HEq (eqToHom hp ≫ β ≫ eqToHom hq.symm).fiber β.fiber := by
      cases hp; cases hq
      simp only [eqToHom_refl]
      rw [Category.comp_id β, Category.id_comp β]
    exact (castFiber (sigmaRegroupMap_comp F B p r)
      (sigmaRegroupMap_comp F B q r) _).symm
end SquareKit.Internal.PathTransport.TwoFamily
