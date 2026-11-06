import SquareKit.Internal.PathTransport.TwoFamilyOrdinarySourceReduction
import SquareKit.Internal.PathTransport.TwoFamilySourceEndpointFiberAction
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) {Γ : Context.{u}}
local notation "M" => fullModel C D
noncomputable abbrev ordinaryActionFamily (A : Family Γ) (p q : TwoFamily.Section A.data)
 (s : TwoFamily.Section (reindex (projectionHigher A.data) A.data)) : Family Γ :=
 (M).identity A (ordinaryApply M A A ⟨s⟩ ⟨p⟩) (ordinaryApply M A A ⟨s⟩ ⟨q⟩)
end SquareKit.Internal.PathTransport.HigherInterpretation
