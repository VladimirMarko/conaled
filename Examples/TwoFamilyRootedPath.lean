import SquareKit.Internal.PathTransport.TwoFamilyRootedFamily
import Examples.TwoFamilyStructuralModel
/-! A fixed-endpoint path context retains the selected integer-family section.
Its variable endpoint is the original total-context projection. -/
namespace Examples.TwoFamilyRootedPath
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoFamilyEndpointSections Examples.TwoFamilyStructuralModel
open TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
local instance : ∀ γ, IsGroupoid (displayed.obj γ) := display.groupoid
local instance : ∀ γ, IsLocallyGroupoid (displayed.obj γ) := display.locallyGroupoid

example : (rootedPathEmbedding displayed selected).comp (pathFirst displayed) =
    ((projectionHigher (rootedPathFamily displayed selected)).comp
      (projectionHigher displayed)).comp selected.lift :=
  rootedPathEmbedding_first displayed selected

example : (rootedPathEmbedding displayed selected).comp (pathSecond displayed) =
    projectionHigher (rootedPathFamily displayed selected) :=
  rootedPathEmbedding_second displayed selected

example : rootedPathFamily displayed selected =
    reindex (rootedEndpoint displayed selected) (openIdHigher displayed) :=
  rootedPathFamily_direct displayed selected

example : (closedReflexivity displayed selected).lift.comp
    (closedPathEmbedding displayed selected selected) =
    selected.lift.comp (pathReflexivity displayed) :=
  closedReflexivity_embedding displayed selected
end Examples.TwoFamilyRootedPath
