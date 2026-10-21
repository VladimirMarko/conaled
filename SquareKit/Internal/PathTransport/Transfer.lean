import SquareKit.Internal.PathTransport.TransferAssembly
import SquareKit.Internal.PathTransport.ConcatReindexBeta
import SquareKit.Internal.PathTransport.TransferApplication

/-!
The first-path induction argument adapts agda-unimath `tr-concat` at revision
75518656f287c203b41cb7f71df46e02b987a084. The generalized tail retains z, q, and b;
the branch is reflexivity after generated computation. Source correspondence
and the upstream MIT notice are in docs/research/agda-transfer-source-notice.md.
-/
namespace SquareKit.Internal.PathTransport.Typed.Authoring
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace TransferFrame
variable (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ)

def left_beta : TmEqDeriv (contextRaw (branchContext hΓ x)) (contextCode (branchContext hΓ x))
    (.fiber (z hΓ x).raw) (fiberCode (z hΓ x).code)
    (leftRoot hΓ x).raw (leftRoot hΓ x).code (branchValue hΓ x).raw (branchValue hΓ x).code :=
  (transport_reindex_conversion (context hΓ x) (branchContext hΓ x)
    (concat (context hΓ x) (first hΓ x) (second hΓ x)) (element hΓ x) (root hΓ x)).trans
      (transport_congr (branchContext hΓ x) (concatRootPath hΓ x) (q hΓ x)
        (b hΓ x) (b hΓ x) (concat_root_normalized hΓ x) (.refl (b hΓ x).deriv))

def branch := branchFromComputations hΓ x (left_beta hΓ x)

def command : @PathCommand Γ γ .base x.raw (baseCode γ) x.code 3
    [(.fiber (ConcatFrame.fixed hΓ x).raw),
      (.identity .base (ConcatFrame.yAtZ hΓ x).raw (ConcatFrame.z hΓ x).raw), .base]
    (tailCode hΓ x) :=
  { context := hΓ
    type := .base hΓ
    point := x.deriv
    telescope := tail hΓ x
    motive :=
      { raw := .identity (.fiber (last hΓ x).raw) (left hΓ x).raw (right hΓ x).raw
        code := identityCode (fiberCode (last hΓ x).code) (left hΓ x).code (right hΓ x).code
        typing := motive hΓ x
        branch := .refl (branchValue hΓ x).raw
        branchCode := _
        branchTyping := branch hΓ x } }
end TransferFrame

/-- The complete first transfer: first-path J, generalized z/q/b, reflexivity.
Callers supply named typed paths and an element; no indices or model arguments. -/
def trConcat (hΓ : CtxDeriv Γ γ) {x y z : BasePoint Γ γ}
    (p : Path x y) (q : Path y z) (b : FiberElement x) :=
  (TransferApplication.applyCommand hΓ x y z p q b (TransferFrame.command hΓ x)).rawType
    (TransferApplication.motive_raw hΓ x y z p q b)

end SquareKit.Internal.PathTransport.Typed.Authoring
