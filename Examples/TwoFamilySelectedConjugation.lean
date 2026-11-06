import SquareKit.Internal.PathTransport.TwoFamilyFixedPathConjugation
import Examples.TwoFamilySelectedOrdinaryAction
namespace Examples.TwoFamilySelectedOrdinaryAction
open CategoryTheory Bicategory SquareKit.Internal.PathTransport HigherInterpretation
open Examples.FrozenMemoStages
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) (R : SelectedPaths (structuralModel C D)) (γ : (show Context from R.context))
noncomputable def selectedConjugated :=
 fixedPathConjugated C D R.family R.x R.y γ
  (R.h.down.normalObj R.toParallel.identity.data γ).fiber.as.as
theorem selectedConjugated_eq : selectedConjugated C D R γ =
 (R.h.down.normalObj R.toParallel.identity.data γ).fiber.as.as :=
 fixedPathConjugated_eq C D R.family R.x R.y γ _
end Examples.TwoFamilySelectedOrdinaryAction
