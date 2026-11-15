import SquareKit.Internal.PathTransport.TwoFamilyPathConjugation
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

namespace Examples.TwoFamilyPathConjugation
open SquareKit.Internal.PathTransport HigherInterpretation TwoFamily
open Examples.TwoFamilyModelData Examples.TwoFamilyStructuralModel
open Examples.TwoFamilyEndpointSections Examples.TwoOpenIdentityHigher
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000

noncomputable section
def endpoint : Total display.data := ⟨totalPoint, point⟩
/-- The actual interpreted action, conjugated by the selected J comparison. -/
def conjugated (k : ℤ) : Multiplicative ℤ :=
 pathConjugated integerContext integerContext display chosen endpoint (a := arrow) (b := arrow) (Multiplicative.ofAdd k)
theorem conjugated_retained (k : ℤ) : conjugated k = Multiplicative.ofAdd k :=
 pathConjugated_eq integerContext integerContext display chosen endpoint (a := arrow) (b := arrow) (Multiplicative.ofAdd k)
theorem conjugated_one_ne_zero : conjugated 1 ≠ conjugated 0 := by
 rw [conjugated_retained, conjugated_retained]
 intro h
 exact Int.one_ne_zero (congrArg Multiplicative.toAdd h)
end
end Examples.TwoFamilyPathConjugation
