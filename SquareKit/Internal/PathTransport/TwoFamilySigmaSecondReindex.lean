import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroupReindex
import SquareKit.Internal.PathTransport.TwoFamilySectionReindexReflection
/-! The selected second section commutes with substitution. Its dependent family comparison is explicit, and equality is reflected from recombined higher lifts. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ uB vB wB
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))
theorem Section.sigmaSecond_lift (s : Section (sigmaFamily F B)) :
    (s.sigmaSecond F B).lift.comp (reindexHigher B (s.sigmaFirst F B).lift) =
      s.lift.comp (sigmaRegroup F B) := by
  change pairLift B (s.sigmaFirst F B).lift
    (Section.cast (sigmaSecond_family F B s) (sectionOfLift B (s.lift.comp (sigmaRegroup F B)))) = _
  have e : factorBase B (s.lift.comp (sigmaRegroup F B)) = (s.sigmaFirst F B).lift := by
    change (s.lift.comp (sigmaRegroup F B)).comp (projectionHigher B) = _
    rw [strictFunctor_comp_assoc, sigmaRegroup_projection]
    rfl
  rw [pairLift_cast_base B e]
  exact factorHigher_reindex B (s.lift.comp (sigmaRegroup F B))

variable (σ : StrictPseudofunctor Δ Γ)
abbrev Section.sigmaReindex (s : Section (sigmaFamily F B)) :=
  Section.cast (sigmaFamily_reindex F σ B).symm (s.reindex _ σ)

theorem sigmaSecond_reindex_family (s : Section (sigmaFamily F B)) :
    reindex ((s.sigmaReindex F B σ).sigmaFirst (reindex σ F)
      (reindex (reindexHigher F σ) B)).lift (reindex (reindexHigher F σ) B) =
    reindex σ (reindex (s.sigmaFirst F B).lift B) := by
  rw [reindex_comp, reindex_comp]
  apply congrArg (fun k => reindex k B)
  rw [Section.sigmaFirst_reindex]
  exact Section.reindex_lift F (s.sigmaFirst F B) σ
private theorem cast_lift_recover {C : Type*} [Bicategory C] [Strict C]
    {H K : Family C} (e : H = K) (s : Section H) :
    (Section.cast e s).lift.comp (familyCast e.symm) = s.lift := by
  cases e
  exact strictFunctor_comp_id s.lift

private theorem sigmaSecond_reindex_lift (s : Section (sigmaFamily F B)) :
    ((((s.sigmaReindex F B σ).sigmaSecond (reindex σ F) (reindex (reindexHigher F σ) B)).lift.comp
      (reindexHigher (reindex (reindexHigher F σ) B)
        ((s.sigmaReindex F B σ).sigmaFirst (reindex σ F) (reindex (reindexHigher F σ) B)).lift)).comp
      (reindexHigher B (reindexHigher F σ))) = σ.comp (s.lift.comp (sigmaRegroup F B)) := by
  rw [Section.sigmaSecond_lift, strictFunctor_comp_assoc, sigmaRegroup_reindex]
  change (Section.cast (sigmaFamily_reindex F σ B).symm (s.reindex _ σ)).lift.comp
    ((familyCast (sigmaFamily_reindex F σ B)).comp
      ((reindexHigher (sigmaFamily F B) σ).comp (sigmaRegroup F B))) = _
  rw [← strictFunctor_comp_assoc, cast_lift_recover, ← strictFunctor_comp_assoc,
    Section.reindex_lift, strictFunctor_comp_assoc]

private theorem reindex_sigmaSecond_lift (s : Section (sigmaFamily F B)) :
    (((s.sigmaSecond F B).reindex _ σ).lift.comp
      (reindexHigher (reindex (s.sigmaFirst F B).lift B) σ)).comp
      (reindexHigher B (s.sigmaFirst F B).lift) = σ.comp (s.lift.comp (sigmaRegroup F B)) := by
  rw [Section.reindex_lift, strictFunctor_comp_assoc, Section.sigmaSecond_lift]

set_option backward.defeqAttrib.useBackward false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem Section.sigmaSecond_reindex_heq (s : Section (sigmaFamily F B)) :
    HEq ((s.sigmaReindex F B σ).sigmaSecond (TwoFamily.reindex σ F)
      (TwoFamily.reindex (reindexHigher F σ) B))
      ((s.sigmaSecond F B).reindex _ σ) := by
  let t := s.sigmaReindex F B σ
  let A := TwoFamily.reindex σ F
  let B' := TwoFamily.reindex (reindexHigher F σ) B
  with_reducible exact (Section.reindex_lifts_hext (C := Total F) (A := Total (TwoFamily.reindex σ F))
    (A' := Γ) (D := Δ) B (reindexHigher F σ) (t.sigmaFirst A B').lift
    (s.sigmaFirst F B).lift σ (t.sigmaSecond A B') ((s.sigmaSecond F B).reindex _ σ)
    (sigmaSecond_reindex_family F B σ s)
    ((sigmaSecond_reindex_lift F B σ s).trans (reindex_sigmaSecond_lift F B σ s).symm))

theorem Section.sigmaSecond_reindex (s : Section (sigmaFamily F B)) :
    Section.cast (sigmaSecond_reindex_family F B σ s)
      ((s.sigmaReindex F B σ).sigmaSecond (TwoFamily.reindex σ F)
        (TwoFamily.reindex (reindexHigher F σ) B)) =
      ((s.sigmaSecond F B).reindex _ σ) :=
  eq_of_heq ((Section.cast_heq _ _).trans (Section.sigmaSecond_reindex_heq F B σ s))
end SquareKit.Internal.PathTransport.TwoFamily
