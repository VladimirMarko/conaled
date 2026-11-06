import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroupHigher
import SquareKit.Internal.PathTransport.TwoFamilyPairLiftIdentities
import SquareKit.Internal.PathTransport.TwoFunctorComposition
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ uB vB wB
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))
theorem Section.ext_lift {H : Family Γ} (s t : Section H) (h : s.lift = t.lift) : s = t := by
  cases s; cases t; cases h; rfl

def Section.sigmaPair (a : Section F) (b : Section (TwoFamily.reindex a.lift B)) :
    Section (sigmaFamily F B) where
  lift := (pairLift B a.lift b).comp (sigmaUngroup F B)
  over := by
    rw [strictFunctor_comp_assoc, sigmaUngroup_projection, ← strictFunctor_comp_assoc,
      pairLift_projection]
    exact a.over

theorem Section.sigmaPair_first (a : Section F) (b : Section (TwoFamily.reindex a.lift B)) :
    (a.sigmaPair F B b).sigmaFirst F B = a := by
  apply Section.ext_lift
  change ((pairLift B a.lift b).comp (sigmaUngroup F B)).comp (TwoFamily.sigmaFirst F B) = a.lift
  rw [strictFunctor_comp_assoc, sigmaUngroup_first, pairLift_projection]

theorem sigmaSecond_family (s : Section (sigmaFamily F B)) :
    reindex (factorBase B (s.lift.comp (sigmaRegroup F B))) B =
      reindex (s.sigmaFirst F B).lift B := by
  apply congrArg (fun k => TwoFamily.reindex k B)
  change (s.lift.comp (sigmaRegroup F B)).comp (projectionHigher B) = _
  rw [strictFunctor_comp_assoc, sigmaRegroup_projection]
  rfl

def Section.sigmaSecond (s : Section (sigmaFamily F B)) :
    Section (TwoFamily.reindex (s.sigmaFirst F B).lift B) :=
  Section.cast (sigmaSecond_family F B s) (sectionOfLift B (s.lift.comp (sigmaRegroup F B)))

theorem Section.sigmaPair_regroup (a : Section F) (b : Section (TwoFamily.reindex a.lift B)) :
    (a.sigmaPair F B b).lift.comp (sigmaRegroup F B) = pairLift B a.lift b := by
  change ((pairLift B a.lift b).comp (sigmaUngroup F B)).comp (sigmaRegroup F B) = _
  rw [strictFunctor_comp_assoc, sigmaUngroup_regroup, strictFunctor_comp_id]

theorem Section.sigmaPair_second_heq (a : Section F) (b : Section (TwoFamily.reindex a.lift B)) :
    HEq ((a.sigmaPair F B b).sigmaSecond F B) b := by
  apply HEq.trans (Section.cast_heq _ _)
  apply HEq.trans (congr_arg_heq (fun h => sectionOfLift B h) (Section.sigmaPair_regroup F B a b))
  exact sectionOfLift_pairLift_heq B a.lift b

theorem Section.sigmaPair_eta (s : Section (sigmaFamily F B)) :
    (s.sigmaFirst F B).sigmaPair F B (s.sigmaSecond F B) = s := by
  apply Section.ext_lift
  change (pairLift B (s.sigmaFirst F B).lift
    (Section.cast (sigmaSecond_family F B s) (sectionOfLift B (s.lift.comp (sigmaRegroup F B))))).comp
      (sigmaUngroup F B) = s.lift
  have e : factorBase B (s.lift.comp (sigmaRegroup F B)) = (s.sigmaFirst F B).lift := by
    change (s.lift.comp (sigmaRegroup F B)).comp (projectionHigher B) = _
    rw [strictFunctor_comp_assoc, sigmaRegroup_projection]
    rfl
  rw [pairLift_cast_base B e]
  change ((factorHigher B (s.lift.comp (sigmaRegroup F B))).comp
    (reindexHigher B (factorBase B (s.lift.comp (sigmaRegroup F B))))).comp (sigmaUngroup F B) = _
  rw [factorHigher_reindex, strictFunctor_comp_assoc,
    sigmaRegroup_ungroup, strictFunctor_comp_id]

theorem Section.sigmaPair_second (a : Section F) (b : Section (TwoFamily.reindex a.lift B)) :
    Section.cast
      (congrArg (fun t : Section F => TwoFamily.reindex t.lift B) (Section.sigmaPair_first F B a b))
      ((a.sigmaPair F B b).sigmaSecond F B) = b := by
  apply eq_of_heq
  exact (Section.cast_heq _ _).trans (Section.sigmaPair_second_heq F B a b)
end SquareKit.Internal.PathTransport.TwoFamily
