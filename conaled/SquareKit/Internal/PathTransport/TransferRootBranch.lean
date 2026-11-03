import SquareKit.Internal.PathTransport.TransferRoot
import SquareKit.Internal.PathTransport.TransferBranch
import SquareKit.Internal.PathTransport.TransportNormalization

namespace SquareKit.Internal.PathTransport.Typed.Authoring.TransferFrame
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ)
def contextRaw {Γ γ} (_ : CtxDeriv Γ γ) : RawCtx := Γ
def contextCode {Γ γ} (_ : CtxDeriv Γ γ) : CtxCode := γ
def branchContext := CtxDeriv.branch hΓ (.base hΓ) x.deriv (tail hΓ x)
def a := (fixed hΓ x).reindex (root hΓ x)
def y := (moving hΓ x).reindex (root hΓ x)
def z := (last hΓ x).reindex (root hΓ x)
def b := (element hΓ x).reindex (root hΓ x)
def pOld := (first hΓ x).reindex (context hΓ x) (root hΓ x)
def qOld := (second hΓ x).reindex (context hΓ x) (root hΓ x)
def p := (pOld hΓ x).withEndpoints rfl (moving_root_raw hΓ x) rfl (moving_root_code hΓ x)
def q := (qOld hΓ x).withEndpoints (moving_root_raw hΓ x) rfl (moving_root_code hΓ x) rfl

def p_reflexive : TmEqDeriv (contextRaw (branchContext hΓ x)) (contextCode (branchContext hΓ x)) (.identity .base (a hΓ x).raw (a hΓ x).raw)
    (identityCode (baseCode _) (a hΓ x).code (a hΓ x).code)
    (p hΓ x).raw (p hΓ x).code (.refl (a hΓ x).raw) (reflCode (baseCode _) (a hΓ x).code) := by
  apply TmEqDeriv.native (p hΓ x).deriv (first_root_raw hΓ x)
  funext M
  exact eq_of_heq ((castCode_eval _ _ M).trans (first_root_eval hΓ x M))

def inner_beta : TmEqDeriv (contextRaw (branchContext hΓ x)) (contextCode (branchContext hΓ x)) (.fiber (a hΓ x).raw) (fiberCode (a hΓ x).code)
    (transport (branchContext hΓ x) (p hΓ x) (b hΓ x)).raw
    (transport (branchContext hΓ x) (p hΓ x) (b hΓ x)).code
    (b hΓ x).raw (b hΓ x).code :=
  (transport_congr (branchContext hΓ x) (p hΓ x) (Path.reflexivity (branchContext hΓ x) (a hΓ x))
    (b hΓ x) (b hΓ x) (p_reflexive hΓ x) (.refl (b hΓ x).deriv)).trans
      (transport_beta (branchContext hΓ x) (a hΓ x) (b hΓ x))
def innerOriginal := (transport (context hΓ x) (first hΓ x) (element hΓ x)).reindex (root hΓ x)
def inner := (innerOriginal hΓ x).withPoint (moving_root_raw hΓ x) (moving_root_code hΓ x)

def inner_original_beta : TmEqDeriv (contextRaw (branchContext hΓ x)) (contextCode (branchContext hΓ x))
    (.fiber (a hΓ x).raw) (fiberCode (a hΓ x).code)
    (inner hΓ x).raw (inner hΓ x).code (b hΓ x).raw (b hΓ x).code :=
  transport_reindex_beta (context hΓ x) (branchContext hΓ x) (first hΓ x) (element hΓ x)
    (root hΓ x) (moving_root_raw hΓ x) (moving_root_code hΓ x) (first_root_raw hΓ x)
    (first_root_eval hΓ x)

def rightRoot := (right hΓ x).reindex (root hΓ x)
def branchValue := transport (branchContext hΓ x) (q hΓ x) (b hΓ x)

def right_beta : TmEqDeriv (contextRaw (branchContext hΓ x)) (contextCode (branchContext hΓ x))
    (.fiber (z hΓ x).raw) (fiberCode (z hΓ x).code)
    (rightRoot hΓ x).raw (rightRoot hΓ x).code (branchValue hΓ x).raw (branchValue hΓ x).code :=
  transport_nested_reindex_beta (context hΓ x) (branchContext hΓ x) (first hΓ x) (second hΓ x)
    (element hΓ x) (root hΓ x) (moving_root_raw hΓ x) (moving_root_code hΓ x) (inner_original_beta hΓ x)

end SquareKit.Internal.PathTransport.Typed.Authoring.TransferFrame
