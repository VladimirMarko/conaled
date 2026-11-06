import Examples.TwoFamilyFullModel
import SquareKit.Internal.DependentJudgments.PathFamilyConjugationSemantics
namespace Examples.TwoFamilyPathConjugation
open SquareKit.Internal.PathTransport
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open Examples.TwoFamilyFullModel Examples.TwoFamilyStructuralModel
noncomputable def selectedBeta := pathBetaSection completeModel display chosen
example : HEq (completeModel.subTm selectedBeta (completeModel.toStructuralModel.rootSub display chosen))
 (completeModel.reflexivity (completeModel.identity display chosen chosen) (completeModel.reflexivity display chosen)) :=
 pathBetaSection_root completeModel display chosen
end Examples.TwoFamilyPathConjugation
