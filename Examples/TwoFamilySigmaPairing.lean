import SquareKit.Internal.PathTransport.TwoFamilySigmaPairing
import SquareKit.Internal.PathTransport.TwoFamilySigmaReindex
import Examples.TwoFamilySigmaRegroup
namespace Examples.TwoFamilySigmaPairing
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport TwoFamily
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyFiber Examples.TwoFamilySigmaProjection
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
abbrev originalFamily := sigmaFamily integerFamily laterFamily
abbrev projection := projectionHigher originalFamily
abbrev firstFamily := reindex projection integerFamily
abbrev secondFamily := reindex (reindexHigher integerFamily projection) laterFamily
abbrev selected := Section.cast (sigmaFamily_reindex integerFamily projection laterFamily).symm
  (variableSection originalFamily)
abbrev first := selected.sigmaFirst firstFamily secondFamily
abbrev second := selected.sigmaSecond firstFamily secondFamily
abbrev rebuilt := first.sigmaPair firstFamily secondFamily second

theorem rebuild_eq : rebuilt = selected := Section.sigmaPair_eta _ _ _
example : rebuilt.sigmaFirst firstFamily secondFamily = first := Section.sigmaPair_first _ _ _ _
example : HEq (rebuilt.sigmaSecond firstFamily secondFamily) second := Section.sigmaPair_second_heq _ _ _ _

end Examples.TwoFamilySigmaPairing
