import SquareKit.Internal.PathTransport.CommandCongruence
import SquareKit.Internal.PathTransport.ConcatenationBeta
import SquareKit.Internal.PathTransport.TransportCongr
import SquareKit.Internal.PathTransport.NativeNormalization

/-! Generated congruence for first-path concatenation. Adapted from the
framework-assisted #107 regression of the archived #106 partial proof. -/
namespace SquareKit.Internal.PathTransport.Typed.Authoring
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def concat_endpoints_congr (hΓ : CtxDeriv Γ γ) {x y z : BasePoint Γ γ}
    (p p' : Path x y) (q : Path y z)
    (ep : TmEqDeriv Γ γ (.identity .base x.raw y.raw)
      (identityCode (baseCode γ) x.code y.code) p.raw p.code p'.raw p'.code) := by
  let e0 := endpoint_congr hΓ x y p p' ep
  let ez := SubEqDeriv.pairingConverted (ConcatFrame.zType hΓ x) e0 rfl
    (baseSub_code _) (baseSub_code _) (.refl z.deriv)
  exact SubEqDeriv.pairingConverted (ConcatFrame.qType hΓ x) ez rfl
    (ConcatApplication.q_type_at hΓ x y z p)
    (ConcatApplication.q_type_at hΓ x y z p') (.refl q.deriv)
def concat_congr_first (hΓ : CtxDeriv Γ γ) {x y z : BasePoint Γ γ}
    (p p' : Path x y) (q : Path y z)
    (ep : TmEqDeriv Γ γ (.identity .base x.raw y.raw)
      (identityCode (baseCode γ) x.code y.code) p.raw p.code p'.raw p'.code) :
    TmEqDeriv Γ γ (.identity .base x.raw z.raw) (identityCode (baseCode γ) x.code z.code)
      (concat hΓ p q).raw (concat hΓ p q).code
      (concat hΓ p' q).raw (concat hΓ p' q).code := by
  let cmd := ConcatFrame.command hΓ x
  have es := concat_endpoints_congr hΓ p p' q ep
  have hraw : cmd.motive.raw.sub
      (eliminationSub y.raw p.raw (ConcatApplication.arguments y z q)) = .identity .base x.raw z.raw := by
    rw [ConcatApplication.endpoint_raw x y z p q]
    simp only [cmd, ConcatFrame.command, ConcatFrame.fixed, BasePoint.reindex,
      ConcatFrame.tailProjection, ConcatFrame.tail, pathProjection, ConcatFrame.zAtQ,
      ConcatFrame.z, BasePoint.variable, Expr.sub_comp, Expr.sub, consSub]
    exact congrArg (fun a => Expr.identity .base a z.raw) (Expr.sub_id x.raw)
  have e := cmd.argumentsCongr
    (args := ConcatApplication.arguments y z q) (args' := ConcatApplication.arguments y z q)
    (ρ := Expr.var) (ρ' := Expr.var)
    (y := y.raw) (y' := y.raw) (p := p.raw) (p' := p'.raw)
    (by convert es using 1 <;> first | rfl | simp only [← ConcatApplication.endpoint_raw, eliminationSub])
    hraw (ConcatApplication.motive_at hΓ x y z p q)
      (ConcatApplication.motive_at hΓ x y z p' q)
  simp only [Expr.liftSubN_var, Expr.sub_id] at e
  convert e using 1 <;> rfl

end SquareKit.Internal.PathTransport.Typed.Authoring
