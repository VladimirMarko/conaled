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
def SelectedVerticalAction : Prop := OrdinaryApVerticalAction C D (pathType (fullModel C D) R)
 (transport (fullModel C D) R) R.p R.p' R.h
theorem source_vertical_action : SelectedVerticalAction C D R :=
 ordinaryApValue_vertical_action C D (pathType (fullModel C D) R)
 (transport (fullModel C D) R) R.p R.p' R.h
end Examples.TwoFamilySelectedOrdinaryAction
