import SquareKit.Internal.PathTransport.TransferRootBranch

namespace SquareKit.Internal.PathTransport.Typed.Authoring.TransferFrame
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ)

def leftRoot := (left hΓ x).reindex (root hΓ x)

def motiveNormalization := TyEqDeriv.trans
  (TyEqDeriv.identitySub (.fiber (last hΓ x).deriv) (left hΓ x).deriv (right hΓ x).deriv (root hΓ x))
  (TyEqDeriv.identityCongr (TyEqDeriv.fiberSub (last hΓ x).deriv (root hΓ x))
    (TmDeriv.sub (left hΓ x).deriv (root hΓ x)) (TmDeriv.sub (right hΓ x).deriv (root hΓ x)))

/-- Once both sides compute to the branch value, reflexivity has the required
source motive by generated type conversion. -/
def branchFromComputations
    (el : TmEqDeriv (contextRaw (branchContext hΓ x)) (contextCode (branchContext hΓ x))
      (.fiber (z hΓ x).raw) (fiberCode (z hΓ x).code)
      (leftRoot hΓ x).raw (leftRoot hΓ x).code (branchValue hΓ x).raw (branchValue hΓ x).code) :=
  ((TmDeriv.refl (.fiber (z hΓ x).deriv) (branchValue hΓ x).deriv).convert
    (TyEqDeriv.identity (.fiber (z hΓ x).deriv) el.symm (right_beta hΓ x).symm)).convert
      (motiveNormalization hΓ x).symm

end SquareKit.Internal.PathTransport.Typed.Authoring.TransferFrame
