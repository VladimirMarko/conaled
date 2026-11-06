import Examples.FrozenMemoDisplayRealization
import Examples.TwoFamilyFrozenPoint
noncomputable section
namespace Examples.TwoFamilyFrozenPoint
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport HigherInterpretation
open Examples.TwoFamilyModelData Examples.TwoOpenIdentityHigher
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2000
abbrev full := fullModel integerContext integerContext
abbrev sigmaRealization := FrozenMemoStages.sigmaData full emptyA emptyB
abbrev tauRealization := FrozenMemoStages.tauData full emptyA emptyB
abbrev deltaContext : Context := sigmaRealization.display.total
abbrev thetaContext : Context := tauRealization.display.total
set_option maxHeartbeats 1000000 in
def deltaPoint (k : ℤ) : deltaContext :=
 ⟨⟨⟨⟨⟨⟨⟨⟨⟨PUnit.unit⟩⟩, point⟩, point⟩, ⟨arrow⟩⟩, ⟨arrow⟩⟩, ⟨⟨Multiplicative.ofAdd k⟩⟩⟩, ⟨arrow⟩⟩, ⟨arrow⟩⟩
set_option maxHeartbeats 1000000 in
def thetaPoint (k : ℤ) : thetaContext :=
 ⟨⟨⟨⟨⟨⟨⟨⟨PUnit.unit⟩⟩, point⟩, ⟨arrow⟩⟩, ⟨arrow⟩⟩, ⟨⟨Multiplicative.ofAdd k⟩⟩⟩, ⟨arrow⟩⟩, ⟨arrow⟩⟩
end Examples.TwoFamilyFrozenPoint
