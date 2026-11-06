import SquareKit.Internal.DependentJudgments.Sigma.PairStability

/-! Package a selected value and its selected identity certificate as an object
sum. Substitution retains the actual second component and its dependent type. -/
namespace SquareKit.Internal.DependentJudgments.MemoPair
open PathTransport.Typed StructuralModel
universe u
variable (M : StructuralModel.{u})
variable {Γ : M.Context} (A : M.Family Γ) (c : M.Section Γ A)

def certificateFamily : M.Family (M.extend Γ A) :=
  M.identity (M.subTy A (M.weaken Γ A)) (M.genericVariable Γ A)
    (M.subTm c (M.weaken Γ A))

theorem certificateFamily_at (v : M.Section Γ A) :
    M.subTy (certificateFamily M A c) (M.sectionSub A v) = M.identity A v c := by
  unfold certificateFamily
  rw [M.identity_sub]
  exact M.identity_congr (M.weaken_section_type A v A)
    (M.variable_section A v) (M.weaken_section_term A v c)

def certificate (v : M.Section Γ A) (η : M.Section Γ (M.identity A v c)) :
    M.Section Γ (M.subTy (certificateFamily M A c) (M.sectionSub A v)) :=
  cast (congrArg (M.Section Γ) (certificateFamily_at M A c v).symm) η

variable (S : Sigma.Capability M)

def pair (v : M.Section Γ A) (η : M.Section Γ (M.identity A v c)) :
    M.Section Γ (S.sigma A (certificateFamily M A c)) :=
  S.pair A (certificateFamily M A c) v (certificate M A c v η)

/-- Unpacking recovers the selected value and certificate together. -/
theorem unpack_pair (v : M.Section Γ A) (η : M.Section Γ (M.identity A v c)) :
    M.compSub (S.unpack A (certificateFamily M A c))
      (M.sectionSub (S.sigma A (certificateFamily M A c)) (pair M A c S v η)) =
    M.pairSub (certificateFamily M A c) (M.sectionSub A v) (certificate M A c v η) := by
  unfold pair
  rw [S.section_pair]
  unfold Sigma.Capability.pairSubstitution
  rw [← M.comp_assoc, S.unpack_pack, M.comp_id_left]

variable (SS : Sigma.Stable M)

theorem pair_sub {Δ : M.Context} (v : M.Section Γ A)
    (η : M.Section Γ (M.identity A v c)) (σ : M.Substitution Δ Γ) :
    HEq (M.subTm (pair M A c SS.toCapability v η) σ)
      (SS.toCapability.pair (M.subTy A σ)
        (M.subTy (certificateFamily M A c) (M.lift A σ)) (M.subTm v σ)
        (Sigma.Stable.pairSecond A (certificateFamily M A c) v
          (certificate M A c v η) σ)) :=
  SS.pair_sub A (certificateFamily M A c) v (certificate M A c v η) σ

/-- Both substitutions retain the selected pair, with the dependent certificate
reindexed along their composite. -/
theorem pair_sub_twice {Δ Θ : M.Context} (v : M.Section Γ A)
    (η : M.Section Γ (M.identity A v c)) (σ : M.Substitution Δ Γ)
    (τ : M.Substitution Θ Δ) :
    HEq (M.subTm (M.subTm (pair M A c SS.toCapability v η) σ) τ)
      (SS.toCapability.pair (M.subTy A (M.compSub σ τ))
        (M.subTy (certificateFamily M A c) (M.lift A (M.compSub σ τ)))
        (M.subTm v (M.compSub σ τ))
        (Sigma.Stable.pairSecond A (certificateFamily M A c) v
          (certificate M A c v η) (M.compSub σ τ))) :=
  (M.subTm_comp _ σ τ).trans (pair_sub M A c SS v η (M.compSub σ τ))

end SquareKit.Internal.DependentJudgments.MemoPair
