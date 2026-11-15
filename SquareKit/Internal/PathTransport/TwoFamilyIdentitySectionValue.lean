import SquareKit.Internal.PathTransport.TwoFamilyClosedComparisonComponent
import SquareKit.Internal.PathTransport.TwoFamilyModelData
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ : Context.{u}}
noncomputable def identitySectionValue (F : Family Γ) (p q : TwoFamily.Section F.data)
 (h : TwoFamily.Section (closedId F.data p q)) (γ : Γ) :
 (p.normalObj F.data γ).fiber ⟶ (q.normalObj F.data γ).fiber :=
 (h.normalObj (closedId F.data p q) γ).fiber.as
end SquareKit.Internal.PathTransport.HigherInterpretation
