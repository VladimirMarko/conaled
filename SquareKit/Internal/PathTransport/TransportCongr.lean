import SquareKit.Internal.PathTransport.Derived
import SquareKit.Internal.PathTransport.StructuralCongruence
namespace SquareKit.Internal.PathTransport.Typed.Authoring
open SquareKit.Internal.PathTransport
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def endpoint_congr (hΓ : CtxDeriv Γ γ) (x y : BasePoint Γ γ) (p q : Path x y)
    (e : TmEqDeriv Γ γ (.identity .base x.raw y.raw) (identityCode (baseCode γ) x.code y.code)
      p.raw p.code q.raw q.code) :
    SubEqDeriv Γ γ (pathCtx Γ .base x.raw) (pathCode (baseCode γ) x.code)
      (consSub p.raw (consSub y.raw Expr.var)) (endpointCode (baseCode γ) x.code y.code p.code)
      (consSub q.raw (consSub y.raw Expr.var)) (endpointCode (baseCode γ) x.code y.code q.code) := by
  exact SubEqDeriv.pairingConverted (.pathFamily hΓ (.base hΓ) x.deriv)
    (.refl (.section hΓ (.base hΓ) y.deriv)) (pathFamilyRaw_at .base x.raw y.raw)
    (pathFamilyAt_code (baseCode γ) x.code y.code)
    (pathFamilyAt_code (baseCode γ) x.code y.code) e

def transport_congr (hΓ : CtxDeriv Γ γ) {x y : BasePoint Γ γ}
    (p q : Path x y) (b c : FiberElement x)
    (ep : TmEqDeriv Γ γ (.identity .base x.raw y.raw) (identityCode (baseCode γ) x.code y.code)
      p.raw p.code q.raw q.code)
    (eb : TmEqDeriv Γ γ (.fiber x.raw) (fiberCode x.code) b.raw b.code c.raw c.code) :
    TmEqDeriv Γ γ (.fiber y.raw) (fiberCode y.code)
      (transport hΓ p b).raw (transport hΓ p b).code
      (transport hΓ q c).raw (transport hΓ q c).code := by
  let cmd := transportCommand hΓ x b
  let cmd' := transportCommand hΓ x c
  let hs := SubDeriv.rawTransport (argsSub_zero (genericArguments 0) _).symm
    (SubDeriv.endpoint hΓ (.base hΓ) x.deriv y.deriv p.deriv)
  let ht := SubDeriv.rawTransport (argsSub_zero (genericArguments 0) _).symm
    (SubDeriv.endpoint hΓ (.base hΓ) x.deriv y.deriv q.deriv)
  let l := cmd.motive.pathInduction hΓ (.base hΓ) x.deriv cmd.telescope y.deriv p.deriv hs
  let r := cmd'.motive.pathInduction hΓ (.base hΓ) x.deriv cmd'.telescope y.deriv q.deriv ht
  have branch := eb.annotateType (transportMotive_root hΓ x).symm
  have endpoints := endpoint_congr hΓ x y p q ep
  have eqn := TmEqDeriv.pathInductionAtCongr (Γ := Γ) (γ := γ) (A := .base) (x := x.raw) (a := baseCode γ) (ξ := x.code) (η' := cmd'.motive.branchCode) (n := 0) (args := genericArguments 0) (args' := genericArguments 0) (Δ := []) (T := telNil (pathCode (baseCode γ) x.code)) (.refl (transportMotive hΓ x)) branch endpoints
    (by simpa only [Expr.liftSubN_var, Expr.sub_id, cmd, cmd', transportCommand, moving, BasePoint.reindex, BasePoint.variable, Expr.sub, Expr.rename, Function.comp_apply, eliminationSub, argsSub_zero, consSub] using l)
    (by simpa only [Expr.liftSubN_var, Expr.sub_id, cmd, cmd', transportCommand, moving, BasePoint.reindex, BasePoint.variable, Expr.sub, Expr.rename, Function.comp_apply, eliminationSub, argsSub_zero, consSub] using r)
  have hm : (moving hΓ x).raw = .var 1 := rfl
  simp only [hm, Expr.liftSubN_var, Expr.sub_id, argsSub_zero, Expr.sub, consSub] at eqn
  have out := eqn.annotateType (transportMotive_at hΓ x y p)
  apply out.annotate
  · rfl
  · apply eq_of_heq
    exact (castCode_heq _ _).trans ((castCode_heq _ _).trans (castCode_heq _ _).symm)
end SquareKit.Internal.PathTransport.Typed.Authoring
