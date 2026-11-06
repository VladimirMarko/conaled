import SquareKit.Internal.PathTransport.TwoFamilySourceHEq
import SquareKit.Internal.PathTransport.TwoFamilySectionReindexLift
import SquareKit.Internal.PathTransport.TwoFamilySigmaPairing
import SquareKit.Internal.PathTransport.TwoFamilySigmaReindex
import SquareKit.Internal.PathTransport.TwoFamilyHigherReindexLaws
/-! The first dependent-pair projection commutes with arbitrary substitution, with explicit transport across the Sigma-family equality. -/
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
private abbrev firstAfterSubstitution := (sigmaFirst (reindex σ F) (reindex (reindexHigher F σ) B)).comp (reindexHigher F σ)
private abbrev substitutionAfterFirst := (reindexHigher (sigmaFamily F B) σ).comp (sigmaFirst F B)

theorem sigmaFirst_reindex_obj (x : Total (substitutedSigma F σ B)) (x' : Total (pulledSigma F σ B)) (hx : HEq x x') :
    HEq ((firstAfterSubstitution F σ B).obj x) ((substitutionAfterFirst F σ B).obj x') := by
  have hb := total_obj_base_heq_family (sigmaFamily_reindex F σ B) hx
  have hf := total_obj_fiber_heq_family (sigmaFamily_reindex F σ B) hx
  rcases x with ⟨a,b⟩; rcases x' with ⟨a',b'⟩
  change a = a' at hb
  cases hb
  apply heq_of_eq
  refine total_obj_hext F (x := (firstAfterSubstitution F σ B).obj ⟨a,b⟩) (y := (substitutionAfterFirst F σ B).obj ⟨a,b'⟩) rfl ?_
  exact heq_of_eq (total_obj_base_heq_family (fiberRestriction_reindex F σ B a) hf)

theorem sigmaFirst_reindex_map {x y : Total (substitutedSigma F σ B)} {x' y' : Total (pulledSigma F σ B)}
    (hx : HEq x x') (hy : HEq y y') (p : x ⟶ y) (p' : x' ⟶ y') (hp : HEq p p') :
    HEq ((firstAfterSubstitution F σ B).map p) ((substitutionAfterFirst F σ B).map p') := by
  have hxb := total_obj_base_heq_family (sigmaFamily_reindex F σ B) hx
  have hyb := total_obj_base_heq_family (sigmaFamily_reindex F σ B) hy
  have hxf := total_obj_fiber_heq_family (sigmaFamily_reindex F σ B) hx
  have hyf := total_obj_fiber_heq_family (sigmaFamily_reindex F σ B) hy
  have hpb := total_hom_base_heq_family (sigmaFamily_reindex F σ B) hx hy hp
  have hpf := total_hom_fiber_heq_family (sigmaFamily_reindex F σ B) hx hy hp
  apply total_hom_hext F (eq_of_heq (sigmaFirst_reindex_obj F σ B x x' hx))
    (eq_of_heq (sigmaFirst_reindex_obj F σ B y y' hy))
  · rcases x with ⟨a,b⟩; rcases x' with ⟨a',b'⟩
    rcases y with ⟨c,d⟩; rcases y' with ⟨c',d'⟩
    change a = a' at hxb; change c = c' at hyb
    cases hxb; cases hyb
    exact congr_arg_heq σ.map (eq_of_heq hpb)
  · rcases x with ⟨a,b⟩; rcases x' with ⟨a',b'⟩
    rcases y with ⟨c,d⟩; rcases y' with ⟨c',d'⟩
    change a = a' at hxb; change c = c' at hyb
    cases hxb; cases hyb
    rcases p with ⟨f,pf⟩; rcases p' with ⟨f',pf'⟩
    change HEq f f' at hpb
    cases eq_of_heq hpb
    exact total_hom_base_heq_family (fiberRestriction_reindex F σ B c)
      (sigmaMap_reindex_obj F σ B f b b' hxf) hyf hpf
theorem sigmaFirst_reindex_cell {x y : Total (substitutedSigma F σ B)} {x' y' : Total (pulledSigma F σ B)}
    (hx : HEq x x') (hy : HEq y y') {p q : x ⟶ y} {p' q' : x' ⟶ y'}
    (hp : HEq p p') (hq : HEq q q') (α : p ⟶ q) (β : p' ⟶ q') (hα : HEq α β) :
    HEq ((firstAfterSubstitution F σ B).map₂ α) ((substitutionAfterFirst F σ B).map₂ β) := by
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
  apply total_cell_hext F (eq_of_heq (sigmaFirst_reindex_obj F σ B x x' hx))
    (eq_of_heq (sigmaFirst_reindex_obj F σ B y y' hy))
    (sigmaFirst_reindex_map F σ B hx hy p p' hp) (sigmaFirst_reindex_map F σ B hx hy q q' hq)
  · rcases x with ⟨a,b⟩; rcases x' with ⟨a',b'⟩
    rcases y with ⟨c,d⟩; rcases y' with ⟨c',d'⟩
    change a = a' at hxb; change c = c' at hyb
    cases hxb; cases hyb
    rcases p with ⟨f,pf⟩; rcases p' with ⟨f',pf'⟩
    rcases q with ⟨g,qf⟩; rcases q' with ⟨g',qf'⟩
    change HEq f f' at hpb; change HEq g g' at hqb
    cases eq_of_heq hpb; cases eq_of_heq hqb
    exact congr_arg_heq σ.map₂ (eq_of_heq hαb)
  · rcases x with ⟨a,b⟩; rcases x' with ⟨a',b'⟩
    rcases y with ⟨c,d⟩; rcases y' with ⟨c',d'⟩
    change a = a' at hxb; change c = c' at hyb
    cases hxb; cases hyb
    rcases p with ⟨f,pf⟩; rcases p' with ⟨f',pf'⟩
    change HEq f f' at hpb
    cases eq_of_heq hpb
    exact total_cell_base_heq_family (fiberRestriction_reindex F σ B c)
      (sigmaMap_reindex_obj F σ B f b b' hxf) hyf hpf hboundary hαf
theorem sigmaFirst_reindex_heq : HEq (firstAfterSubstitution F σ B) (substitutionAfterFirst F σ B) :=
  total_functor_hext_source_family (sigmaFamily_reindex F σ B) _ _
    (sigmaFirst_reindex_obj F σ B) (sigmaFirst_reindex_map F σ B) (sigmaFirst_reindex_cell F σ B)

theorem sigmaFirst_reindex :
    (sigmaFirst (reindex σ F) (reindex (reindexHigher F σ) B)).comp (reindexHigher F σ) =
      (familyCast (sigmaFamily_reindex F σ B)).comp
        ((reindexHigher (sigmaFamily F B) σ).comp (sigmaFirst F B)) :=
  (familyCast_precomp_eq_of_heq (sigmaFamily_reindex F σ B) _ _ (sigmaFirst_reindex_heq F σ B)).symm

private theorem cast_lift_recover {C : Type*} [Bicategory C] [Strict C]
    {H K : Family C} (e : H = K) (s : Section H) :
    (Section.cast e s).lift.comp (familyCast e.symm) = s.lift := by
  cases e
  exact strictFunctor_comp_id s.lift

theorem Section.sigmaFirst_reindex (s : Section (sigmaFamily F B)) :
    (Section.cast (sigmaFamily_reindex F σ B).symm (s.reindex _ σ)).sigmaFirst
        (TwoFamily.reindex σ F) (TwoFamily.reindex (reindexHigher F σ) B) =
      (s.sigmaFirst F B).reindex F σ := by
  apply Section.reindex_lift_injective F σ
  change (((Section.cast (sigmaFamily_reindex F σ B).symm (s.reindex _ σ)).lift.comp
    (TwoFamily.sigmaFirst (TwoFamily.reindex σ F) (TwoFamily.reindex (reindexHigher F σ) B))).comp
      (reindexHigher F σ)) = _
  rw [strictFunctor_comp_assoc, TwoFamily.sigmaFirst_reindex, ← strictFunctor_comp_assoc,
    cast_lift_recover, ← strictFunctor_comp_assoc, Section.reindex_lift, strictFunctor_comp_assoc,
    Section.reindex_lift]
  rfl
end SquareKit.Internal.PathTransport.TwoFamily
