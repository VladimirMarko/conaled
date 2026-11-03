import SquareKit.Internal.PathTransport.UniversalTransfer
import SquareKit.Internal.PathTransport.TransferSoundness
import SquareKit.Internal.PathTransport.ConcatenationBeta

/-!
# Source identity proofs interpreted in ordinary groupoids

`Authoring` exposes named source operations and their generated computation
rules. `transport_concat` interprets the retained first-path source proof for
arbitrary groupoids and set-valued families, with independent universes.
See `docs/research/agda-transfer-interface.md` for the supported fragment.
-/
namespace SquareKit.GroupoidTransport

namespace Authoring
export Internal.PathTransport.Typed (CtxDeriv TyDeriv TmDeriv SubDeriv TyEqDeriv TmEqDeriv)
export Internal.PathTransport.Typed.Authoring
  (BasePoint Path FiberElement transport transport_beta concat concat_beta trConcat)
end Authoring

export Internal.PathTransport.GroupoidModel.TransferSoundness
  (basePathEquiv basePathEquiv_refl basePathEquiv_concat)

/-- The retained source `tr-concat` proof interpreted for an arbitrary groupoid
and set-valued family. Object, arrow, and fiber universes are independent. -/
abbrev transport_concat :=
  Internal.PathTransport.GroupoidModel.UniversalTransfer.transport_concat_universes

end SquareKit.GroupoidTransport
