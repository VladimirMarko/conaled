import SquareKit.Internal.PathTransport.ConcatenationBeta
namespace SquareKit.Internal.PathTransport.Typed.Authoring
open SquareKit.Internal.PathTransport
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem transport_raw_explicit (hΓ : CtxDeriv Γ γ) {x y : BasePoint Γ γ}
    (p : Path x y) (b : FiberElement x) :
    (transport hΓ p b).raw = .pathInduction 0 .base x.raw (.fiber (.var 1))
      b.raw y.raw p.raw (genericArguments 0) := rfl

theorem transport_raw_reindex (hΓ : CtxDeriv Γ γ) (hΔ : CtxDeriv Δ δ)
    {x y : BasePoint Γ γ} (p : Path x y) (b : FiberElement x)
    (hs : SubDeriv Δ δ Γ γ σ s) :
    ((transport hΓ p b).raw).sub σ =
      (transport hΔ (p.reindex hΓ hs) (b.reindex hs)).raw := by
  simp only [transport_raw_explicit, Expr.sub, Expr.liftSubN, Expr.liftSub,
    BasePoint.reindex, Path.reindex, FiberElement.reindex]
  simp only [Expr.rename]
  congr 1
  funext i
  exact Fin.elim0 i

theorem concat_raw_explicit (hΓ : CtxDeriv Γ γ)
    {x y z : BasePoint Γ γ} (p : Path x y) (q : Path y z) :
    (concat hΓ p q).raw = .pathInduction 2 .base x.raw
      (.identity .base (x.raw.rename (fun i => i + 4)) (.var 1))
      (.var 0) y.raw p.raw (ConcatApplication.arguments y z q) := by
  simp only [concat, ConcatFrame.command, ConcatFrame.fixed, ConcatFrame.zAtQ,
    ConcatFrame.z, BasePoint.reindex, BasePoint.variable, ConcatFrame.tailProjection,
    ConcatFrame.tail, pathProjection, Expr.sub_comp, Expr.sub]
  congr 2
  exact Expr.sub_var_rename _ _

theorem concat_raw_reindex (hΓ : CtxDeriv Γ γ) (hΔ : CtxDeriv Δ δ)
    {x y z : BasePoint Γ γ} (p : Path x y) (q : Path y z)
    (hs : SubDeriv Δ δ Γ γ σ s) :
    ((concat hΓ p q).raw).sub σ =
      (concat hΔ (p.reindex hΓ hs) (q.reindex hΓ hs)).raw := by
  simp only [concat_raw_explicit, Expr.sub, Expr.sub_rename, Path.reindex,
    BasePoint.reindex, ConcatApplication.arguments]
  simp only [Expr.liftSubN, Expr.liftSub,
    Expr.rename, Expr.rename_sub]
  congr 2
  · congr 1
    funext n
    simp only [Function.comp_apply, Expr.liftSub, Expr.rename_comp]
    rfl
  · funext i
    change Expr.sub σ (if i.val = 0 then q.raw else z.raw) =
      (if i.val = 0 then Expr.sub σ q.raw else Expr.sub σ z.raw)
    split <;> rfl
end SquareKit.Internal.PathTransport.Typed.Authoring
