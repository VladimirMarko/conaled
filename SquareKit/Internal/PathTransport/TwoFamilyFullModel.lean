import SquareKit.Internal.PathTransport.TwoFamilyModelFromContractions
import SquareKit.Internal.PathTransport.TwoFamilyModelRootContraction
import SquareKit.Internal.PathTransport.TwoFamilySigmaStable

/-! The strict 2-groupoid interpretation supplies contextual J from its
constructed coherent contractions and retains the chosen dependent sums. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
universe u

noncomputable def fullModel (C D : Context.{u}) : Typed.Model.{u+1} :=
  modelFromContractions C D (rootContraction C D) (rootContraction_square C D)

noncomputable def fullSigma (C D : Context.{u}) :
    DependentJudgments.Sigma.Stable (fullModel C D).toStructuralModel :=
  sigmaStable C D

end SquareKit.Internal.PathTransport.HigherInterpretation
