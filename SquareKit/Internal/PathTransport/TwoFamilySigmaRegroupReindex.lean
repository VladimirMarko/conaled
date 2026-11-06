import SquareKit.Internal.PathTransport.TwoFamilySigmaFirstReindex
import SquareKit.Internal.PathTransport.TwoFamilySectionReindexLift
import SquareKit.Internal.PathTransport.TwoFamilySigmaPairing
import SquareKit.Internal.PathTransport.TwoFamilySigmaReindex
import SquareKit.Internal.PathTransport.TwoFamilyHigherReindexLaws
/-! Regrouping commutes with arbitrary substitution at objects, arrows, and genuine cells. The whole-functor equation retains the family comparison. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ uB vB wB
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) (σ : StrictPseudofunctor Δ Γ)
variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))
private abbrev substitutedSigma := sigmaFamily (reindex σ F) (reindex (reindexHigher F σ) B)
private abbrev pulledSigma := reindex σ (sigmaFamily F B)
private abbrev regroupAfterSubstitution := (sigmaRegroup (reindex σ F) (reindex (reindexHigher F σ) B)).comp (reindexHigher B (reindexHigher F σ))
private abbrev substitutionAfterRegroup := (reindexHigher (sigmaFamily F B) σ).comp (sigmaRegroup F B)

theorem sigmaRegroup_reindex_obj (x : Total (substitutedSigma F σ B)) (x' : Total (pulledSigma F σ B)) (hx : HEq x x') :
    HEq ((regroupAfterSubstitution F σ B).obj x) ((substitutionAfterRegroup F σ B).obj x') := by
  have hbase := sigmaFirst_reindex_obj F σ B x x' hx
  have hb := total_obj_base_heq_family (sigmaFamily_reindex F σ B) hx
  have hf := total_obj_fiber_heq_family (sigmaFamily_reindex F σ B) hx
  rcases x with ⟨a,b⟩; rcases x' with ⟨a',b'⟩
  change a = a' at hb
  cases hb
  apply heq_of_eq
  refine total_obj_hext B (x := (regroupAfterSubstitution F σ B).obj ⟨a,b⟩) (y := (substitutionAfterRegroup F σ B).obj ⟨a,b'⟩) (eq_of_heq hbase) ?_
  exact total_obj_fiber_heq_family (fiberRestriction_reindex F σ B a) hf

theorem sigmaRegroup_reindex_map {x y : Total (substitutedSigma F σ B)} {x' y' : Total (pulledSigma F σ B)}
    (hx : HEq x x') (hy : HEq y y') (p : x ⟶ y) (p' : x' ⟶ y') (hp : HEq p p') :
    HEq ((regroupAfterSubstitution F σ B).map p) ((substitutionAfterRegroup F σ B).map p') := by
  have hxb := total_obj_base_heq_family (sigmaFamily_reindex F σ B) hx
  have hyb := total_obj_base_heq_family (sigmaFamily_reindex F σ B) hy
  have hxf := total_obj_fiber_heq_family (sigmaFamily_reindex F σ B) hx
  have hyf := total_obj_fiber_heq_family (sigmaFamily_reindex F σ B) hy
  have hpb := total_hom_base_heq_family (sigmaFamily_reindex F σ B) hx hy hp
  have hpf := total_hom_fiber_heq_family (sigmaFamily_reindex F σ B) hx hy hp
  apply total_hom_hext B (eq_of_heq (sigmaRegroup_reindex_obj F σ B x x' hx))
    (eq_of_heq (sigmaRegroup_reindex_obj F σ B y y' hy))
  · exact sigmaFirst_reindex_map F σ B hx hy p p' hp
  · apply HEq.trans (sigmaRegroupMap_fiber_heq (reindex σ F) (reindex (reindexHigher F σ) B) p)
    apply HEq.trans _ (sigmaRegroupMap_fiber_heq F B ((reindexHigher (sigmaFamily F B) σ).map p')).symm
    rcases x with ⟨a,b⟩; rcases x' with ⟨a',b'⟩
    rcases y with ⟨c,d⟩; rcases y' with ⟨c',d'⟩
    change a = a' at hxb; change c = c' at hyb
    cases hxb; cases hyb
    rcases p with ⟨f,pf⟩; rcases p' with ⟨f',pf'⟩
    change HEq f f' at hpb
    cases eq_of_heq hpb
    exact total_hom_fiber_heq_family (fiberRestriction_reindex F σ B c)
      (sigmaMap_reindex_obj F σ B f b b' hxf) hyf hpf
private theorem sigmaSecond_cell_heq {x y : Total (substitutedSigma F σ B)} {x' y' : Total (pulledSigma F σ B)}
  (hx : HEq x x') (hy : HEq y y') {p q : x ⟶ y} {p' q' : x' ⟶ y'}
  (hp : HEq p p') (hq : HEq q q') (α : p ⟶ q) (β : p' ⟶ q') (hα : HEq α β) :
  HEq α.fiber.fiber β.fiber.fiber := by
  have hxb := total_obj_base_heq_family (sigmaFamily_reindex F σ B) hx
  have hyb := total_obj_base_heq_family (sigmaFamily_reindex F σ B) hy
  have hxf := total_obj_fiber_heq_family (sigmaFamily_reindex F σ B) hx
  have hyf := total_obj_fiber_heq_family (sigmaFamily_reindex F σ B) hy
  have hpb := total_hom_base_heq_family (sigmaFamily_reindex F σ B) hx hy hp
  have hqb := total_hom_base_heq_family (sigmaFamily_reindex F σ B) hx hy hq
  have hpf := total_hom_fiber_heq_family (sigmaFamily_reindex F σ B) hx hy hp
  have hqf := total_hom_fiber_heq_family (sigmaFamily_reindex F σ B) hx hy hq
  have hαb := total_cell_base_heq_family (sigmaFamily_reindex F σ B) hx hy hp hq hα
  have hαf := total_cell_fiber_heq_family (sigmaFamily_reindex F σ B) hx hy hp hq hα
  have hboundary := total_cell_boundary_heq_family (sigmaFamily_reindex F σ B) hx hy hp hq hα
  rcases x with ⟨a,b⟩; rcases x' with ⟨a',b'⟩
  rcases y with ⟨c,d⟩; rcases y' with ⟨c',d'⟩
  change a = a' at hxb; change c = c' at hyb
  cases hxb; cases hyb
  rcases p with ⟨f,pf⟩; rcases p' with ⟨f',pf'⟩
  change HEq f f' at hpb
  cases eq_of_heq hpb
  exact total_cell_fiber_heq_family (fiberRestriction_reindex F σ B c)
    (sigmaMap_reindex_obj F σ B f b b' hxf) hyf hpf hboundary hαf

theorem sigmaRegroup_reindex_cell {x y : Total (substitutedSigma F σ B)} {x' y' : Total (pulledSigma F σ B)}
    (hx : HEq x x') (hy : HEq y y') {p q : x ⟶ y} {p' q' : x' ⟶ y'}
    (hp : HEq p p') (hq : HEq q q') (α : p ⟶ q) (β : p' ⟶ q') (hα : HEq α β) :
    HEq ((regroupAfterSubstitution F σ B).map₂ α) ((substitutionAfterRegroup F σ B).map₂ β) := by
  have hxb := total_obj_base_heq_family (sigmaFamily_reindex F σ B) hx
  have hyb := total_obj_base_heq_family (sigmaFamily_reindex F σ B) hy
  have hxf := total_obj_fiber_heq_family (sigmaFamily_reindex F σ B) hx
  have hyf := total_obj_fiber_heq_family (sigmaFamily_reindex F σ B) hy
  have hpb := total_hom_base_heq_family (sigmaFamily_reindex F σ B) hx hy hp
  have hqb := total_hom_base_heq_family (sigmaFamily_reindex F σ B) hx hy hq
  have hpf := total_hom_fiber_heq_family (sigmaFamily_reindex F σ B) hx hy hp
  have hqf := total_hom_fiber_heq_family (sigmaFamily_reindex F σ B) hx hy hq
  have hαb := total_cell_base_heq_family (sigmaFamily_reindex F σ B) hx hy hp hq hα
  have hαf := total_cell_fiber_heq_family (sigmaFamily_reindex F σ B) hx hy hp hq hα
  have hboundary := total_cell_boundary_heq_family (sigmaFamily_reindex F σ B) hx hy hp hq hα
  apply total_cell_hext B (eq_of_heq (sigmaRegroup_reindex_obj F σ B x x' hx))
    (eq_of_heq (sigmaRegroup_reindex_obj F σ B y y' hy))
    (sigmaRegroup_reindex_map F σ B hx hy p p' hp) (sigmaRegroup_reindex_map F σ B hx hy q q' hq)
  · exact sigmaFirst_reindex_cell F σ B hx hy hp hq α β hα
  · apply HEq.trans (sigmaRegroupCell_fiber_heq (reindex σ F) (reindex (reindexHigher F σ) B) α)
    apply HEq.trans _ (sigmaRegroupCell_fiber_heq F B ((reindexHigher (sigmaFamily F B) σ).map₂ β)).symm
    exact sigmaSecond_cell_heq F σ B hx hy hp hq α β hα
theorem sigmaRegroup_reindex_heq : HEq (regroupAfterSubstitution F σ B) (substitutionAfterRegroup F σ B) :=
  total_functor_hext_source_family (sigmaFamily_reindex F σ B) _ _
    (sigmaRegroup_reindex_obj F σ B) (sigmaRegroup_reindex_map F σ B) (sigmaRegroup_reindex_cell F σ B)

theorem sigmaRegroup_reindex :
    (sigmaRegroup (reindex σ F) (reindex (reindexHigher F σ) B)).comp (reindexHigher B (reindexHigher F σ)) =
      (familyCast (sigmaFamily_reindex F σ B)).comp
        ((reindexHigher (sigmaFamily F B) σ).comp (sigmaRegroup F B)) :=
  (familyCast_precomp_eq_of_heq (sigmaFamily_reindex F σ B) _ _ (sigmaRegroup_reindex_heq F σ B)).symm
end SquareKit.Internal.PathTransport.TwoFamily
