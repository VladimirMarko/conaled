import SquareKit.Internal.PathTransport.TwoFamilyIdentitySectionValue
import SquareKit.Internal.PathTransport.TwoFamilyStructuralModel
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ : Context.{u}}
noncomputable def identitySectionCell (A : Family Γ) (x y : TwoFamily.Section A.data)
 (p q : TwoFamily.Section (A.identity x y).data)
 (h : TwoFamily.Section (closedId (A.identity x y).data p q)) (γ : Γ) :
 identitySectionValue A x y p γ ⟶ identitySectionValue A x y q γ :=
 (identitySectionValue (A.identity x y) p q h γ).as
theorem identitySectionCell_heq (A : Family Γ) (x y : TwoFamily.Section A.data)
 (p q : TwoFamily.Section (A.identity x y).data)
 (h : TwoFamily.Section (closedId (A.identity x y).data p q)) (γ : Γ) :
 HEq (identitySectionCell A x y p q h γ)
  (h.normalObj (closedId (A.identity x y).data p q) γ).fiber.as.as := HEq.rfl
end SquareKit.Internal.PathTransport.HigherInterpretation
