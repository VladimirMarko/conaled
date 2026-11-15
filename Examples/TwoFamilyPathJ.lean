import SquareKit.Internal.PathTransport.TwoFamilyPathJObjects
import Examples.TwoFamilyPathContraction
import SquareKit.Internal.PathTransport.TwoFamilyPathFaithful
import Examples.TwoFamilyPathContext
noncomputable section
namespace Examples.TwoFamilyPathJ
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyPathContext
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
local instance : IsGroupoid B where
  all_isIso f := by
    obtain ⟨g, h, k⟩ := DoubleDelooping.one_inverse (Multiplicative ℤ) f
    exact ⟨⟨g, h, k⟩⟩
local instance : ∀ x, IsGroupoid (integerFamily.obj x) := fun _ => inferInstanceAs (IsGroupoid B)
local instance : ∀ x, IsLocallyGroupoid (integerFamily.obj x) := fun _ =>
  inferInstanceAs (IsLocallyGroupoid B)


universe uE vE wE
/-- Arbitrary higher motives over the integer path context admit the constructed section. -/
def integerPathJ (E : TwoFamily.Family.{_,_,_,uE,vE,wE} (TwoFamily.PathContext integerFamily))
    (d : TwoFamily.Section (TwoFamily.reindex (TwoFamily.pathReflexivity integerFamily) E)) :
    TwoFamily.Section E := TwoFamily.pathJ integerFamily E d
/-- Object beta specializes in the context that retains arbitrary integer path arrows. -/
example (E : TwoFamily.Family.{_,_,_,uE,vE,wE} (TwoFamily.PathContext integerFamily))
    (d : TwoFamily.Section (TwoFamily.reindex (TwoFamily.pathReflexivity integerFamily) E)) :
    HEq (((integerPathJ E d).lift.obj
      ((TwoFamily.pathReflexivity integerFamily).obj sourceObject)).fiber)
      ((d.lift.obj sourceObject).fiber) := by
  exact TwoFamily.pathJ_obj_beta integerFamily E d sourceObject
end Examples.TwoFamilyPathJ
