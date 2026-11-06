import SquareKit.Internal.PathTransport.TwoFamilyStructuralModel
import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroupHigher
import SquareKit.Internal.DependentJudgments.Sigma.Capability
/-! The constructed higher dependent sum supplies the source Sigma capability.
Both whole-functor inverse laws preserve all selected higher cells. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u})
noncomputable def sigmaCapability : DependentJudgments.Sigma.Capability (structuralModel C D) where
  sigma A B := A.sigma B
  pack A B := ⟨TwoFamily.sigmaUngroup A.data B.data⟩
  unpack A B := ⟨TwoFamily.sigmaRegroup A.data B.data⟩
  pack_over A B := ULift.ext (TwoFamily.sigmaUngroup_projection A.data B.data)
  unpack_pack A B := ULift.ext (TwoFamily.sigmaUngroup_regroup A.data B.data)
  pack_unpack A B := ULift.ext (TwoFamily.sigmaRegroup_ungroup A.data B.data)
end SquareKit.Internal.PathTransport.HigherInterpretation
