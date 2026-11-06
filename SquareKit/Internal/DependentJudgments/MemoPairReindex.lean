import SquareKit.Internal.DependentJudgments.MemoPair

/-! Reindexing reconstructs the memo pair from the substituted selected value,
composite value, and certificate, including its varying identity family. -/
namespace SquareKit.Internal.DependentJudgments.MemoPair
open PathTransport.Typed StructuralModel
universe u
variable (M : StructuralModel.{u})
variable {Γ Δ : M.Context} (A : M.Family Γ) (c : M.Section Γ A)

theorem certificateFamily_reindex (σ : M.Substitution Δ Γ) :
    M.subTy (certificateFamily M A c) (M.lift A σ) =
      certificateFamily M (M.subTy A σ) (M.subTm c σ) := by
  unfold certificateFamily
  rw [M.identity_sub]
  apply M.identity_congr (M.weaken_lift_type A σ) (M.variable_lift A σ)
  apply (M.subTm_comp c (M.weaken Γ A) (M.lift A σ)).trans
  rw [M.weaken_lift]
  exact (M.subTm_comp c σ (M.weaken Δ (M.subTy A σ))).symm

private theorem pair_congr_family (S : Sigma.Capability M) {A : M.Family Γ}
    {B B' : M.Family (M.extend Γ A)} (e : B = B') (a : M.Section Γ A)
    (b : M.Section Γ (M.subTy B (M.sectionSub A a)))
    (b' : M.Section Γ (M.subTy B' (M.sectionSub A a))) (h : HEq b b') :
    HEq (S.pair A B a b) (S.pair A B' a b') := by
  cases e
  cases eq_of_heq h
  rfl

def reindexedCertificate (v : M.Section Γ A) (η : M.Section Γ (M.identity A v c))
    (σ : M.Substitution Δ Γ) :
    M.Section Δ (M.identity (M.subTy A σ) (M.subTm v σ) (M.subTm c σ)) :=
  cast (congrArg (M.Section Δ) (M.identity_sub A v c σ)) (M.subTm η σ)

theorem pair_reindex (S : Sigma.Stable M) (v : M.Section Γ A)
    (η : M.Section Γ (M.identity A v c)) (σ : M.Substitution Δ Γ) :
    HEq (M.subTm (pair M A c S.toCapability v η) σ)
      (pair M (M.subTy A σ) (M.subTm c σ) S.toCapability (M.subTm v σ)
        (reindexedCertificate M A c v η σ)) := by
  apply (pair_sub M A c S v η σ).trans
  apply pair_congr_family M S.toCapability (certificateFamily_reindex M A c σ)
  apply (cast_heq _ _).trans
  apply (M.subTm_congr (certificateFamily_at M A c v) (cast_heq _ _) σ).trans
  exact (cast_heq _ _).symm.trans (cast_heq _ _).symm

end SquareKit.Internal.DependentJudgments.MemoPair
