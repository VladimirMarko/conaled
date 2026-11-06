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
/-- A total cell is reconstructed from its two selected components by cartesian pasting. -/
def cartesianCellFactorization {x y : Total F} {p q : x ⟶ y} (α : p ⟶ q) : p ⟶ q :=
  eqToHom (cartesianLift_factorization F p).symm ≫
    cartesianLift F p.base x.fiber ◁ (fiberInclusion F y.base).map₂ α.fiber ≫
    eqToHom (by
      change cartesianLift F p.base x.fiber ≫ (fiberInclusion F y.base).map
        ((F.map₂ α.base).app x.fiber ≫ q.fiber) = _
      rw [(fiberInclusion F y.base).map_comp, Category.assoc]) ≫
    cartesianComparisonCell F α.base x.fiber ▷ (fiberInclusion F y.base).map q.fiber ≫
    eqToHom (cartesianLift_factorization F q)

private theorem cell_comp_base {x y : Total F} {p q r : x ⟶ y}
    (α : p ⟶ q) (β : q ⟶ r) : (α ≫ β).base = α.base ≫ β.base := rfl

private theorem cell_left_base {x y z : Total F} (p : x ⟶ y)
    {q r : y ⟶ z} (α : q ⟶ r) : (p ◁ α).base = p.base ◁ α.base := rfl
private theorem cell_right_base {x y z : Total F} {p q : x ⟶ y}
    (α : p ⟶ q) (r : y ⟶ z) : (α ▷ r).base = α.base ▷ r.base := rfl

theorem cartesianCellFactorization_base {x y : Total F} {p q : x ⟶ y} (α : p ⟶ q) :
    (cartesianCellFactorization F α).base = α.base := by
  simp only [cartesianCellFactorization,
    cell_comp_base F, total_eqToHom_base F, cell_left_base F, cell_right_base F]
  change eqToHom _ ≫ (p.base ◁ ((fiberInclusion F y.base).map₂ α.fiber).base) ≫
    eqToHom _ ≫ ((cartesianComparisonCell F α.base x.fiber).base ▷ 𝟙 y.base) ≫
    eqToHom _ = _
  rw [cartesianComparisonCell_base]
  change eqToHom _ ≫ (p.base ◁ 𝟙 (𝟙 y.base)) ≫ eqToHom _ ≫
    ((eqToHom _ ≫ α.base) ▷ 𝟙 y.base) ≫ eqToHom _ = α.base
  rw [Bicategory.whiskerLeft_id, Bicategory.whiskerRight_id]
  simp [Bicategory.Strict.rightUnitor_eqToIso, Category.assoc]

private theorem equalityFiber_comp_fiber_heq {x y : Total F} {p q r : x ⟶ y}
    (α : p ⟶ q) (β : q ⟶ r) (hβ : EqualityFiber F β) :
    HEq (α ≫ β).fiber α.fiber := by
  obtain ⟨h,hβ⟩ := hβ
  rw [fiber_comp, hβ, Bicategory.whiskerLeft_eqToHom]
  simp only [eqToHom_trans, comp_eqToHom_heq_iff]
  rfl

private theorem cartesian_vertical_fiber_heq {x y : Total F} {p q : x ⟶ y}
    (α : p ⟶ q) :
    HEq (cartesianLift F p.base x.fiber ◁
      (fiberInclusion F y.base).map₂ α.fiber).fiber α.fiber := by
  change HEq (compBoundary F p.base (𝟙 y.base) x.fiber ◁
    ((F.map (𝟙 y.base)).map (𝟙 _) ◁ ((fiberInclusion F y.base).map₂ α.fiber).fiber) ≫
      eqToHom _) α.fiber
  apply HEq.trans (comp_eqToHom_heq _ _)
  apply HEq.trans (eqToHom_left_heq _ _)
  rw [(F.map (𝟙 y.base)).map_id, Bicategory.id_whiskerLeft]
  simp only [Strict.leftUnitor_eqToIso, eqToIso.inv, eqToIso.hom]
  apply HEq.trans (eqToHom_comp_heq _ _)
  apply HEq.trans (comp_eqToHom_heq _ _)
  exact fiberInclusionCell_fiber_heq F y.base α.fiber

private theorem cast_left_fiber_heq {x y : Total F} {p p' q : x ⟶ y}
    (hp : p = p') (α : p' ⟶ q) : HEq (eqToHom hp ≫ α).fiber α.fiber := by
  cases hp
  rw [eqToHom_refl, Category.id_comp]

theorem cartesianCellFactorization_eq {x y : Total F} {p q : x ⟶ y} (α : p ⟶ q) :
    cartesianCellFactorization F α = α := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ (cartesianCellFactorization_base F α)
  apply eq_of_heq
  simp only [heq_comp_eqToHom_iff]
  unfold cartesianCellFactorization
  apply HEq.trans (cast_left_fiber_heq F _ _)
  apply HEq.trans (equalityFiber_comp_fiber_heq F _ _ ?_)
  · exact cartesian_vertical_fiber_heq F α
  · exact equalityFiber_comp F (equalityFiber_cast F _)
      (equalityFiber_comp F
        (equalityFiber_whiskerRight F (cartesianComparisonCell_equalityFiber F _ _) _)
        (equalityFiber_cast F _))
end SquareKit.Internal.PathTransport.TwoFamily
