import SquareKit.Internal.DependentJudgments.Sigma.Capability

/-! Stability requires formation and constructor naturality. Naturality of the
inverse and dependent eliminator follows from the comprehension isomorphism. -/
namespace SquareKit.Internal.DependentJudgments.Sigma
open PathTransport.Typed StructuralModel
universe u

structure Stable (M : StructuralModel.{u}) extends Capability M where
  sigma_sub : ∀ {Γ Δ} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (σ : M.Substitution Δ Γ),
    M.subTy (sigma A B) σ = sigma (M.subTy A σ) (M.subTy B (M.lift A σ))
  pack_sub : ∀ {Γ Δ} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (σ : M.Substitution Δ Γ),
    M.compSub (M.compSub (M.lift (sigma A B) σ)
      (M.familyComparison (sigma_sub A B σ).symm))
      (pack (M.subTy A σ) (M.subTy B (M.lift A σ))) =
    M.compSub (pack A B) (M.lift B (M.lift A σ))

namespace Stable
variable {M : StructuralModel.{u}} (S : Stable M)
variable {Γ Δ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
  (σ : M.Substitution Δ Γ)

def sumMap : M.Substitution
    (M.extend Δ (S.sigma (M.subTy A σ) (M.subTy B (M.lift A σ))))
    (M.extend Γ (S.sigma A B)) :=
  M.compSub (M.lift (S.sigma A B) σ) (M.familyComparison (S.sigma_sub A B σ).symm)

private theorem comp_comparison_heq {X Y : M.Context} {P Q : M.Family X}
    (h : P = Q) (f : M.Substitution (M.extend X Q) Y) :
    HEq (M.compSub f (M.familyComparison h)) f := by
  cases h
  exact heq_of_eq (M.comp_id_right f)

/-- Erasing the explicit comparison still retains equality of the arrow data;
its source contexts are related by `sigma_sub`. -/
theorem sumMap_heq : HEq (S.sumMap A B σ) (M.lift (S.sigma A B) σ) :=
  comp_comparison_heq (S.sigma_sub A B σ).symm _

theorem sumMap_over :
    M.compSub (M.weaken Γ (S.sigma A B)) (S.sumMap A B σ) =
      M.compSub σ (M.weaken Δ (S.sigma (M.subTy A σ) (M.subTy B (M.lift A σ)))) := by
  rw [sumMap, ← M.comp_assoc, M.weaken_lift, M.comp_assoc,
    M.familyComparison_projection]

theorem sumMap_variable :
    HEq (M.subTm (M.genericVariable Γ (S.sigma A B)) (S.sumMap A B σ))
      (M.genericVariable Δ (S.sigma (M.subTy A σ) (M.subTy B (M.lift A σ)))) := by
  apply (M.subTm_comp _ _ _).symm.trans
  apply (M.subTm_congr (M.weaken_lift_type _ _) (M.variable_lift _ _) _).trans
  exact M.familyComparison_variable _

theorem sumMap_variable_type :
    M.subTy (M.subTy (S.sigma A B) (M.weaken Γ (S.sigma A B))) (S.sumMap A B σ) =
      M.subTy (S.sigma (M.subTy A σ) (M.subTy B (M.lift A σ)))
        (M.weaken Δ (S.sigma (M.subTy A σ) (M.subTy B (M.lift A σ)))) := by
  rw [M.subTy_comp, S.sumMap_over, ← M.subTy_comp, S.sigma_sub]

theorem sigma_id :
    S.sigma (M.subTy A (M.idSub Γ)) (M.subTy B (M.lift A (M.idSub Γ))) = S.sigma A B :=
  (S.sigma_sub A B _).symm.trans (M.subTy_id _)

theorem sumMap_id : S.sumMap A B (M.idSub Γ) = M.familyComparison (S.sigma_id A B) := by
  apply M.pair_ext (S.sigma A B)
  · rw [S.sumMap_over, M.comp_id_left, M.familyComparison_projection]
  · exact (S.sumMap_variable A B _).trans (M.familyComparison_variable _).symm

theorem sigma_comp {Θ : M.Context} (τ : M.Substitution Θ Δ) :
    S.sigma (M.subTy (M.subTy A σ) τ)
      (M.subTy (M.subTy B (M.lift A σ)) (M.lift (M.subTy A σ) τ)) =
    S.sigma (M.subTy A (M.compSub σ τ)) (M.subTy B (M.lift A (M.compSub σ τ))) :=
  (S.sigma_sub _ _ τ).symm.trans
    ((congrArg (fun X => M.subTy X τ) (S.sigma_sub A B σ).symm).trans
      ((M.subTy_comp _ σ τ).trans (S.sigma_sub A B (M.compSub σ τ))))

/-- The comparison between iterated and composite reindexing is retained. -/
theorem sumMap_comp {Θ : M.Context} (τ : M.Substitution Θ Δ) :
    M.compSub (S.sumMap A B σ)
      (S.sumMap (M.subTy A σ) (M.subTy B (M.lift A σ)) τ) =
    M.compSub (S.sumMap A B (M.compSub σ τ))
      (M.familyComparison (S.sigma_comp A B σ τ)) := by
  apply M.pair_ext (S.sigma A B)
  · simp only [← M.comp_assoc, S.sumMap_over]
    simp only [M.comp_assoc, S.sumMap_over, M.familyComparison_projection]
  · apply (M.subTm_comp _ _ _).symm.trans
    apply (M.subTm_congr (S.sumMap_variable_type A B σ) (S.sumMap_variable A B σ) _).trans
    apply (S.sumMap_variable _ _ τ).trans
    apply (M.familyComparison_variable (S.sigma_comp A B σ τ)).symm.trans
    apply HEq.trans _ (M.subTm_comp _ _ _)
    exact (M.subTm_congr (S.sumMap_variable_type A B _) (S.sumMap_variable A B _) _).symm

theorem unpack_sub :
    M.compSub (S.unpack A B) (S.sumMap A B σ) =
      M.compSub (M.lift B (M.lift A σ))
        (S.unpack (M.subTy A σ) (M.subTy B (M.lift A σ))) := by
  calc
    _ = M.compSub (S.unpack A B) (M.compSub (S.sumMap A B σ)
        (M.compSub (S.pack (M.subTy A σ) (M.subTy B (M.lift A σ)))
          (S.unpack (M.subTy A σ) (M.subTy B (M.lift A σ))))) := by
      rw [S.pack_unpack, M.comp_id_right]
    _ = M.compSub (S.unpack A B) (M.compSub
        (M.compSub (S.pack A B) (M.lift B (M.lift A σ)))
        (S.unpack (M.subTy A σ) (M.subTy B (M.lift A σ)))) := by
      rw [← M.comp_assoc (S.sumMap A B σ), show M.compSub (S.sumMap A B σ) _ = _ from S.pack_sub A B σ]
    _ = _ := by rw [← M.comp_assoc, ← M.comp_assoc, S.unpack_pack, M.comp_id_left]

theorem branch_type (C : M.Family (M.extend Γ (S.sigma A B))) :
    M.subTy (M.subTy C (S.pack A B)) (M.lift B (M.lift A σ)) =
      M.subTy (M.subTy C (S.sumMap A B σ))
        (S.pack (M.subTy A σ) (M.subTy B (M.lift A σ))) := by
  rw [M.subTy_comp, M.subTy_comp, sumMap, S.pack_sub]

def branch (C : M.Family (M.extend Γ (S.sigma A B)))
    (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B))) :
    M.Section (M.extend (M.extend Δ (M.subTy A σ)) (M.subTy B (M.lift A σ)))
      (M.subTy (M.subTy C (S.sumMap A B σ))
        (S.pack (M.subTy A σ) (M.subTy B (M.lift A σ)))) :=
  cast (congrArg (M.Section _) (S.branch_type A B σ C))
    (M.subTm d (M.lift B (M.lift A σ)))

theorem split_sub (C : M.Family (M.extend Γ (S.sigma A B)))
    (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B))) :
    M.subTm (S.toCapability.split A B C d) (S.sumMap A B σ) =
      S.toCapability.split (M.subTy A σ) (M.subTy B (M.lift A σ))
        (M.subTy C (S.sumMap A B σ)) (S.branch A B σ C d) := by
  apply S.toCapability.split_unique
  apply (M.subTm_comp _ _ _).trans
  rw [show M.compSub (S.sumMap A B σ) _ = _ from S.pack_sub A B σ]
  apply (M.subTm_comp _ _ _).symm.trans
  apply (M.subTm_congr rfl (S.toCapability.split_beta A B C d) _).trans
  exact (cast_heq _ _).symm

/-- Iterated reindexing of the dependent eliminator follows the structural
composition law; no extra eliminator coherence is a capability field. -/
theorem split_sub_comp {Θ : M.Context} (τ : M.Substitution Θ Δ)
    (C : M.Family (M.extend Γ (S.sigma A B)))
    (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B))) :
    HEq (M.subTm (M.subTm (S.toCapability.split A B C d) (S.sumMap A B σ))
      (S.sumMap (M.subTy A σ) (M.subTy B (M.lift A σ)) τ))
      (M.subTm (S.toCapability.split A B C d)
        (M.compSub (S.sumMap A B (M.compSub σ τ))
          (M.familyComparison (S.sigma_comp A B σ τ)))) := by
  apply (M.subTm_comp _ _ _).trans
  rw [S.sumMap_comp]

end Stable
end SquareKit.Internal.DependentJudgments.Sigma
