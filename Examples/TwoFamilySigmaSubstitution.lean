import SquareKit.Internal.PathTransport.TwoFamilySigmaPairReindex
import Examples.TwoFamilySigmaPairing
namespace Examples.TwoFamilySigmaSubstitution
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport TwoFamily
open Examples.TwoFamilySigmaPairing
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
variable {Δ : Type*} [Bicategory Δ] [Strict Δ]
variable (σ : StrictPseudofunctor Δ (Total originalFamily))
/-- Substitution commutes with constructing the selected generic pair. -/
example : Section.cast (sigmaFamily_reindex firstFamily σ secondFamily)
    ((first.reindex firstFamily σ).sigmaPair (reindex σ firstFamily)
      (reindex (reindexHigher firstFamily σ) secondFamily)
      (first.sigmaPairReindexSecond firstFamily secondFamily σ second)) =
    rebuilt.reindex _ σ :=
  Section.sigmaPair_reindex firstFamily secondFamily σ first second

/-- The chosen second section is recovered after substitution and its dependent family cast. -/
example : Section.cast (sigmaSecond_reindex_family firstFamily secondFamily σ selected)
    ((selected.sigmaReindex firstFamily secondFamily σ).sigmaSecond
      (reindex σ firstFamily) (reindex (reindexHigher firstFamily σ) secondFamily)) =
    second.reindex _ σ :=
  Section.sigmaSecond_reindex firstFamily secondFamily σ selected
end Examples.TwoFamilySigmaSubstitution
