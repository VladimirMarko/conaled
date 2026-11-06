import SquareKit.Internal.PathTransport.TwoFamilySectionValueFormula
import SquareKit.Internal.PathTransport.TwoFamilyRootedPath
import SquareKit.Internal.PathTransport.TwoFamilyFiber
/-! Compare a section value with a vertical action in its native rooted context. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ : Context.{u}}
def VerticalValueAt (F : Family Γ) (p : TwoFamily.Section F.data)
 (s : TwoFamily.Section (reindex (projectionHigher F.data) F.data))
 (k : StrictPseudofunctor Γ (Total (rootedPathFamily F.data p)))
 (G : Family Γ) (v : TwoFamily.Section G.data) : Prop :=
 SourceContraction.RightEndpointValueFormula k G v
  _ (fun z => (s.lift.map ((fiberInclusion F.data z.base.base).map z.fiber.as)).fiber)
end SquareKit.Internal.PathTransport.HigherInterpretation
