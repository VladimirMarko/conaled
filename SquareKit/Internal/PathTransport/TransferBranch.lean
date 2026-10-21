import SquareKit.Internal.PathTransport.TransferFrame
import SquareKit.Internal.PathTransport.TransportCongr

namespace SquareKit.Internal.PathTransport.Typed.Authoring
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Both nested computations are generated source conversion, following the
reflexive case of first-path induction. -/
def trConcatReflexiveEquality (hΓ : CtxDeriv Γ γ) (x z : BasePoint Γ γ)
    (q : Path x z) (b : FiberElement x) :
    TmEqDeriv Γ γ (.fiber z.raw) (fiberCode z.code)
      (transport hΓ (concat hΓ (Path.reflexivity hΓ x) q) b).raw
      (transport hΓ (concat hΓ (Path.reflexivity hΓ x) q) b).code
      (transport hΓ q (transport hΓ (Path.reflexivity hΓ x) b)).raw
      (transport hΓ q (transport hΓ (Path.reflexivity hΓ x) b)).code := by
  have left := transport_congr hΓ (concat hΓ (Path.reflexivity hΓ x) q) q
    b b (concat_beta hΓ x z q) (.refl b.deriv)
  have right := transport_congr hΓ q q (transport hΓ (Path.reflexivity hΓ x) b) b
    (.refl q.deriv) (transport_beta hΓ x b)
  exact left.trans right.symm

def trConcatReflexive (hΓ : CtxDeriv Γ γ) (x z : BasePoint Γ γ)
    (q : Path x z) (b : FiberElement x) :=
  (TmDeriv.refl (.fiber z.deriv) (transport hΓ (concat hΓ (Path.reflexivity hΓ x) q) b).deriv).convert
    (TyEqDeriv.identity (.fiber z.deriv)
      (.refl (transport hΓ (concat hΓ (Path.reflexivity hΓ x) q) b).deriv)
      (trConcatReflexiveEquality hΓ x z q b))

end SquareKit.Internal.PathTransport.Typed.Authoring
