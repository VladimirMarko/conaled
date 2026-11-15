import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroup
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

private theorem object_cast_fiber {C : Type*} [Bicategory C] [Strict C]
    (H : Family C) {x y : Total H} (e : x = y) :
    ∃ h : (H.map (eqToHom e).base).obj x.fiber = y.fiber,
      (eqToHom e).fiber = eqToHom h := by
  cases e
  exact ⟨congrArg (fun K => K.obj x.fiber) (H.map_id x.base),rfl⟩

theorem sigmaRegroupMap_id (x : Total (sigmaFamily F B)) :
    sigmaRegroupMap F B (𝟙 x) = 𝟙 (sigmaRegroupObj F B x) := by
  apply toUnderlyingHom_injective B
  fapply Grothendieck.ext _ _ (sigmaFirstMap_id F B x)
  let e := congrArg (fun H => H.obj x.fiber) ((sigmaFamily F B).map_id x.base)
  obtain ⟨h,hh⟩ := object_cast_fiber (fiberRestriction F x.base B) e
  change eqToHom _ ≫ (eqToHom _ ≫ (eqToHom e).fiber) =
    eqToHom (congrArg (fun K => K.obj x.fiber.fiber) (B.map_id (sigmaRegroupObj F B x).base))
  rw [hh, eqToHom_trans, eqToHom_trans]

private theorem object_cast_left_fiber_heq {C : Type*} [Bicategory C] [Strict C]
    (H : Family C) {x x' y : Total H} (e : x = x') (r : x' ⟶ y) :
    HEq (eqToHom e ≫ r).fiber r.fiber := by
  cases e
  rw [eqToHom_refl, Category.id_comp]

private theorem map_paste_heq {C D : Type*} [Bicategory C] [Strict C]
    [Bicategory D] [Strict D] (H K : StrictPseudofunctor C D) (h : H = K)
    {x y : C} (v : x ⟶ y) {z : D} (k : K.obj y ⟶ z) :
    HEq (H.map v ≫ eqToHom (congrArg (fun L => L.obj y) h) ≫ k) (K.map v ≫ k) := by
  cases h
  simp

theorem sigmaRegroupTransport {x y : Total (sigmaFamily F B)} (p : x ⟶ y) :
    B.map (sigmaRegroupBase F B p) =
      (B.map (cartesianLift F p.base x.fiber.base)).comp
        (B.map ((fiberInclusion F y.base).map p.fiber.base)) := by
  have e := cartesianLift_factorization F (sigmaRegroupBase F B p)
  exact (congrArg B.map e).symm.trans (B.map_comp _ _)

theorem sigmaRegroupMap_comp {x y z : Total (sigmaFamily F B)} (p : x ⟶ y) (q : y ⟶ z) :
    sigmaRegroupMap F B (p ≫ q) = sigmaRegroupMap F B p ≫ sigmaRegroupMap F B q := by
  apply toUnderlyingHom_injective B
  fapply Grothendieck.ext _ _ (sigmaFirstMap_comp F B p q)
  apply eq_of_heq
  simp only [eqToHom_comp_heq_iff]
  apply HEq.trans (sigmaRegroupMap_fiber_heq F B (p ≫ q))
  change HEq (eqToHom _ ≫ (sigmaMap F B q.base).map p.fiber ≫ q.fiber).fiber _
  apply HEq.trans (object_cast_left_fiber_heq (fiberRestriction F z.base B) _ _)
  change HEq (eqToHom _ ≫
    (B.map ((fiberInclusion F z.base).map q.fiber.base)).map
      ((eqToHom ((sigmaTransportComparison F B q.base).naturality p.fiber.base).symm).app
        ((sigmaMap F B p.base).obj x.fiber).fiber ≫
          (B.map (cartesianLift F q.base y.fiber.base)).map p.fiber.fiber) ≫ q.fiber.fiber) _
  rw [StrictTwoTransformation.Trans.eqToHom_app]
  change HEq (eqToHom _ ≫
    (B.map ((fiberInclusion F z.base).map q.fiber.base)).map
      (eqToHom _ ≫ (B.map (cartesianLift F q.base y.fiber.base)).map p.fiber.fiber) ≫
      q.fiber.fiber)
    (eqToHom _ ≫ (B.map (sigmaRegroupBase F B q)).map (eqToHom _ ≫ p.fiber.fiber) ≫
      eqToHom _ ≫ q.fiber.fiber)
  rw [(B.map ((fiberInclusion F z.base).map q.fiber.base)).map_comp,
    (B.map (sigmaRegroupBase F B q)).map_comp]
  simp only [StrongMap.map_eqToHom, Category.assoc, eqToHom_trans_assoc,
    eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
  exact (map_paste_heq _ _ (sigmaRegroupTransport F B q) p.fiber.fiber q.fiber.fiber).symm
def sigmaRegroupFunctor : Total (sigmaFamily F B) ⥤ Total B where
  obj := sigmaRegroupObj F B
  map := sigmaRegroupMap F B
  map_id := sigmaRegroupMap_id F B
  map_comp := sigmaRegroupMap_comp F B

theorem sigmaUngroupMap_id (x : Total B) :
    sigmaUngroupMap F B (𝟙 x) = 𝟙 (sigmaUngroupObj F B x) := by
  apply (sigmaRegroupArrowEquiv F B _ _).injective
  change sigmaRegroupMap F B (sigmaUngroupMap F B (𝟙 x)) = sigmaRegroupMap F B (𝟙 _)
  rw [sigmaRegroupMap_ungroup, sigmaRegroupMap_id]
  rfl

theorem sigmaUngroupMap_comp {x y z : Total B} (p : x ⟶ y) (q : y ⟶ z) :
    sigmaUngroupMap F B (p ≫ q) = sigmaUngroupMap F B p ≫ sigmaUngroupMap F B q := by
  apply (sigmaRegroupArrowEquiv F B _ _).injective
  change sigmaRegroupMap F B (sigmaUngroupMap F B (p ≫ q)) =
    sigmaRegroupMap F B (sigmaUngroupMap F B p ≫ sigmaUngroupMap F B q)
  rw [sigmaRegroupMap_ungroup, sigmaRegroupMap_comp,
    sigmaRegroupMap_ungroup, sigmaRegroupMap_ungroup]

def sigmaUngroupFunctor : Total B ⥤ Total (sigmaFamily F B) where
  obj := sigmaUngroupObj F B
  map := sigmaUngroupMap F B
  map_id := sigmaUngroupMap_id F B
  map_comp := sigmaUngroupMap_comp F B
end SquareKit.Internal.PathTransport.TwoFamily
