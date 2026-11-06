import SquareKit.Internal.PathTransport.TwoFamilyStructuralModel
import Examples.TwoFamilyModelData
import Examples.TwoFamilyClosedIdentity
/-! The structural model retains the selected variable and its higher identity fiber. -/
noncomputable section
namespace Examples.TwoFamilyStructuralModel
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open HigherInterpretation
open Examples.TwoFamilyModelData Examples.TwoFamilyEndpointSections
open Examples.TwoFamilyClosedIdentity
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
abbrev model := structuralModel integerContext integerContext
abbrev chosen := model.genericVariable integerContext integers
abbrev display := model.subTy integers (model.weaken integerContext integers)
local instance : ∀ γ, IsGroupoid (displayed.obj γ) := display.groupoid
local instance : ∀ γ, IsLocallyGroupoid (displayed.obj γ) := display.locallyGroupoid

example : HEq (model.subTm (model.reflexivity display chosen)
    (model.weaken integers.total display))
    (model.reflexivity (model.subTy display (model.weaken integers.total display))
      (model.subTm chosen (model.weaken integers.total display))) :=
  model.refl_sub display chosen _

example : (model.identity display chosen chosen).data =
    TwoFamily.closedId displayed selected selected := rfl

def modelIdentityPoint : ((model.identity display chosen chosen).data.obj totalPoint) := ⟨Examples.TwoOpenIdentityHigher.arrow⟩
def modelHigherPath (h : ℤ) : modelIdentityPoint ⟶ modelIdentityPoint := ⟨Multiplicative.ofAdd h⟩

example : modelHigherPath 1 ≠ modelHigherPath 0 := by
  intro h
  have hi : Multiplicative.ofAdd (1:ℤ) = Multiplicative.ofAdd 0 := congrArg (fun p => p.as) h
  exact Int.one_ne_zero (congrArg Multiplicative.toAdd hi)
end Examples.TwoFamilyStructuralModel
