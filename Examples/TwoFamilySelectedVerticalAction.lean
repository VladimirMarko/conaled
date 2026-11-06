import SquareKit.Internal.PathTransport.TwoFamilyOrdinarySourceAction
import Examples.TwoFamilySelectedOrdinaryAction
namespace Examples.TwoFamilySelectedOrdinaryAction
open CategoryTheory Bicategory SquareKit.Internal.PathTransport HigherInterpretation
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open Examples.FrozenMemoStages Examples.SelectedOrdinaryAction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) (R : SelectedPaths (structuralModel C D))
variable [∀γ, Subsingleton ((pathType (fullModel C D) R).data.obj γ)]
set_option linter.defProp false
def source_vertical_action := ordinaryApValue_vertical_action C D (pathType (fullModel C D) R)
 (transport (fullModel C D) R) R.p R.p' R.h
end Examples.TwoFamilySelectedOrdinaryAction
