import SquareKit.Internal.PathTransport.TwoFamilySigmaCapability
import SquareKit.Internal.PathTransport.TwoFamilyModelComparisons
import SquareKit.Internal.PathTransport.TwoFamilySigmaUngroupReindex
import SquareKit.Internal.DependentJudgments.Sigma.Stability
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u
variable (C D : Context.{u})
local notation "M" => structuralModel C D

theorem sigmaFormation_reindex {Γ Δ : Context.{u}} (A : Family Γ)
    (B : Family A.total) (σ : ULift.{u+1} (StrictPseudofunctor Δ Γ)) :
    (A.sigma B).reindex σ.down = (A.reindex σ.down).sigma
      (B.reindex (((M).lift A σ).down)) := by
  rw [lift_down_eq_reindexHigher]
  exact (Family.sigma_reindex A B σ.down).symm

private theorem sigmaPack_reindex {Γ Δ : Context.{u}} (A : Family Γ)
    (B : Family A.total) (σ : StrictPseudofunctor Δ Γ)
    (κ : StrictPseudofunctor (A.reindex σ).total A.total)
    (hκ : κ = TwoFamily.reindexHigher A.data σ)
    (e : (A.reindex σ).sigma (B.reindex κ) = (A.sigma B).reindex σ) :
    (TwoFamily.sigmaUngroup (A.reindex σ).data (B.reindex κ).data).comp
      ((TwoFamily.familyCast (congrArg Family.data e)).comp
        (TwoFamily.reindexHigher (A.sigma B).data σ)) =
    (TwoFamily.reindexHigher B.data κ).comp (TwoFamily.sigmaUngroup A.data B.data) := by
  subst κ
  exact (TwoFamily.sigmaUngroup_reindex A.data σ B.data).symm

private theorem modelSigmaPack {Γ Δ : Context.{u}} (A : Family Γ)
    (B : Family A.total) (σ : ULift.{u+1} (StrictPseudofunctor Δ Γ)) :
(TwoFamily.sigmaUngroup (A.reindex σ.down).data
      (B.reindex (((M).lift A σ).down)).data).comp
        (((M).familyComparison (sigmaFormation_reindex C D A B σ).symm).down.comp
          (((M).lift (A.sigma B) σ).down)) =
      (((M).lift B ((M).lift A σ)).down).comp (TwoFamily.sigmaUngroup A.data B.data) := by
  rw [familyComparison_eq_familyCast]
  rw [lift_eq_reindexHigher C D (A.sigma B) σ.down]
  have hs := @sigmaPack_reindex.{u} Γ Δ A B σ.down (((M).lift A σ).down)
    (lift_down_eq_reindexHigher C D A σ) (sigmaFormation_reindex C D A B σ).symm
  have hh := lift_down_eq_reindexHigher C D (Δ := (A.reindex σ.down).total) B ((M).lift A σ)
  have hcomp := congrArg (fun k : StrictPseudofunctor
    (B.reindex (((M).lift A σ).down)).total B.total =>
      k.comp (TwoFamily.sigmaUngroup A.data B.data)) hh
  set_option backward.dsimp.instances true in
    dsimp only [structuralModel, Family.total, Family.sigma, Family.reindex, instBicategoryCarrier, instStrictCarrier] at *
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      set_option backward.defeqAttrib.useBackward false in
        with_reducible exact hs.trans hcomp.symm

noncomputable def sigmaStable : DependentJudgments.Sigma.Stable M where
  toCapability := sigmaCapability C D
  sigma_sub A B σ := sigmaFormation_reindex C D A B σ
  pack_sub A B σ := ULift.ext (modelSigmaPack C D A B σ)
end SquareKit.Internal.PathTransport.HigherInterpretation
