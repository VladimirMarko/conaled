import SquareKit.Internal.DependentJudgments.Sigma.Stability
import SquareKit.Internal.DependentJudgments.Sigma.Pairing
import SquareKit.Internal.PathTransport.Binding

/-! Substitution of object pairs follows from constructor stability and the
existing comprehension square. The second component retains its dependent type. -/
namespace SquareKit.Internal.DependentJudgments.Sigma
open PathTransport.Typed StructuralModel
universe u
set_option backward.isDefEq.respectTransparency false

namespace Stable
variable {M : StructuralModel.{u}} (S : Stable M)
variable {Γ Δ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
  (a : M.Section Γ A) (b : M.Section Γ (M.subTy B (M.sectionSub A a)))
  (σ : M.Substitution Δ Γ)

theorem pairSecond_type :
    M.subTy (M.subTy B (M.sectionSub A a)) σ =
      M.subTy (M.subTy B (M.lift A σ)) (M.sectionSub (M.subTy A σ) (M.subTm a σ)) := by
  rw [M.subTy_comp, M.subTy_comp, M.section_lift]

def pairSecond : M.Section Δ
    (M.subTy (M.subTy B (M.lift A σ)) (M.sectionSub (M.subTy A σ) (M.subTm a σ))) :=
  cast (congrArg (M.Section Δ) (pairSecond_type A B a σ)) (M.subTm b σ)

theorem pairSubstitution_sub :
    M.compSub (S.sumMap A B σ)
      (S.toCapability.pairSubstitution (M.subTy A σ) (M.subTy B (M.lift A σ))
        (M.subTm a σ) (pairSecond A B a b σ)) =
    M.compSub (S.toCapability.pairSubstitution A B a b) σ := by
  unfold Capability.pairSubstitution
  rw [← M.comp_assoc (S.sumMap A B σ), show M.compSub (S.sumMap A B σ) _ = _ from S.pack_sub A B σ,
    M.comp_assoc]
  rw [M.lift_pair_square B (M.lift A σ) _ (pairSecond A B a b σ)
    (M.sectionSub A a) b σ (M.section_lift A a σ) (cast_heq _ _)]
  exact (M.comp_assoc _ _ _).symm

/-- Introduction commutes with substitution, including the dependent second
component cast. Formation comparison accounts for the result family. -/
theorem pair_sub :
    HEq (M.subTm (S.toCapability.pair A B a b) σ)
      (S.toCapability.pair (M.subTy A σ) (M.subTy B (M.lift A σ))
        (M.subTm a σ) (pairSecond A B a b σ)) := by
  apply (M.subTm_congr (S.toCapability.pair_type A B a b).symm
    (S.toCapability.pair_heq A B a b) σ).trans
  apply (M.subTm_comp _ _ _).trans
  rw [← S.pairSubstitution_sub A B a b σ]
  apply (M.subTm_comp _ _ _).symm.trans
  apply (M.subTm_congr (S.sumMap_variable_type A B σ) (S.sumMap_variable A B σ) _).trans
  exact (S.toCapability.pair_heq _ _ _ _).symm

end Stable
end SquareKit.Internal.DependentJudgments.Sigma
