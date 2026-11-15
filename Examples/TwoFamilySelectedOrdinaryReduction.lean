import Examples.TwoFamilySelectedOrdinaryAction
import SquareKit.Internal.PathTransport.TwoFamilyOrdinarySourceReduction
namespace Examples.TwoFamilySelectedOrdinaryReduction
open CategoryTheory Bicategory SquareKit.Internal.PathTransport HigherInterpretation
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open Examples.FrozenMemoStages Examples.SelectedOrdinaryAction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) (R : SelectedPaths (structuralModel C D))
variable [∀γ, Subsingleton ((pathType (fullModel C D) R).data.obj γ)]
local notation "M" => fullModel C D
set_option linter.defProp false
def reduced := ordinaryApValue_reduced C D (pathType M R) (pathType M R)
 (transport M R) R.p R.p' R.h
end Examples.TwoFamilySelectedOrdinaryReduction
