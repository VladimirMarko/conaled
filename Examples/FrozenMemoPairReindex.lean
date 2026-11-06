import Examples.FrozenMemoPair
import SquareKit.Internal.DependentJudgments.MemoPairReindex
namespace Examples.FrozenMemoRealization.InputRealization
open SquareKit.Internal.DependentJudgments
universe u
variable {M : SquareKit.Internal.PathTransport.Typed.Model.{u}} {V : Type}
variable {Ω : List (Contextual.Judgment V)} {ρ : V → Value M.toStructuralModel}
variable {F : Contextual.Memo.Frozen.Input Ω}
variable (R : InputRealization M ρ F) (S : Sigma.Stable M.toStructuralModel)
theorem selectedPair_reindex {Δ : M.Context} (σ : M.Substitution Δ R.context) :
    HEq (M.subTm (R.selectedPair S.toCapability) σ)
      (MemoPair.pair M.toStructuralModel (M.subTy R.resultFamily σ)
        (M.subTm R.selectedComposite σ) S.toCapability (M.subTm R.selectedValue σ)
        (MemoPair.reindexedCertificate M.toStructuralModel R.resultFamily
          R.selectedComposite R.selectedValue R.selectedCertificate σ)) :=
  MemoPair.pair_reindex M.toStructuralModel _ _ S _ _ σ
end Examples.FrozenMemoRealization.InputRealization
