import SquareKit.Internal.PathTransport.NativeNormalization
import SquareKit.Internal.PathTransport.TransportCongr

namespace SquareKit.Internal.PathTransport.Typed.Authoring
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def transport_native (hΓ : CtxDeriv Γ γ) {x y x' y' : BasePoint Γ γ}
    (p : Path x y) (p' : Path x' y') (b : FiberElement x) (b' : FiberElement x')
    (hx : x.raw = x'.raw) (hy : y.raw = y'.raw) (hp : p.raw = p'.raw) (hb : b.raw = b'.raw)
    (hξ : x.code = x'.code) (hη : y.code = y'.code)
    (hπ : ∀ M, HEq (p.code M) (p'.code M)) (hβ : ∀ M, HEq (b.code M) (b'.code M)) :
    TmEqDeriv Γ γ (.fiber y'.raw) (fiberCode y'.code)
      (transport hΓ p b).raw ((transport hΓ p b).withPoint hy hη).code
      (transport hΓ p' b').raw (transport hΓ p' b').code := by
  apply TmEqDeriv.native ((transport hΓ p b).withPoint hy hη).deriv
  · simp only [FiberElement.withPoint, transport_raw_explicit]
    rw [hx, hy, hp, hb]
  · funext M
    apply eq_of_heq
    apply (castCode_eval _ _ M).trans
    apply (transport_model hΓ p b M).trans
    apply HEq.trans _ (transport_model hΓ p' b' M).symm
    exact M.transportApply_congr rfl (heq_of_eq (congrFun hξ M))
      (heq_of_eq (congrFun hη M)) (hπ M) rfl rfl (hβ M)

def transport_reindex_conversion (hΓ : CtxDeriv Γ γ) (hΔ : CtxDeriv Δ δ)
    {x y : BasePoint Γ γ} (p : Path x y) (b : FiberElement x)
    (hs : SubDeriv Δ δ Γ γ σ s) :
    TmEqDeriv Δ δ (.fiber (y.reindex hs).raw) (fiberCode (y.reindex hs).code)
      ((transport hΓ p b).reindex hs).raw ((transport hΓ p b).reindex hs).code
      (transport hΔ (p.reindex hΓ hs) (b.reindex hs)).raw
      (transport hΔ (p.reindex hΓ hs) (b.reindex hs)).code :=
  TmEqDeriv.native ((transport hΓ p b).reindex hs).deriv
    (transport_raw_reindex hΓ hΔ p b hs) (transport_code_reindex hΓ hΔ p b hs)

def transport_reindex_beta (hΓ : CtxDeriv Γ γ) (hΔ : CtxDeriv Δ δ)
    {x y : BasePoint Γ γ} (p : Path x y) (b : FiberElement x)
    (hs : SubDeriv Δ δ Γ γ σ s)
    (hy : (y.reindex hs).raw = (x.reindex hs).raw)
    (hη : (y.reindex hs).code = (x.reindex hs).code)
    (hp : (p.reindex hΓ hs).raw = .refl (x.reindex hs).raw)
    (hπ : ∀ M, HEq ((p.reindex hΓ hs).code M) (reflCode (baseCode δ) (x.reindex hs).code M)) :
    TmEqDeriv Δ δ (.fiber (x.reindex hs).raw) (fiberCode (x.reindex hs).code)
      ((transport hΓ p b).reindex hs).raw (((transport hΓ p b).reindex hs).withPoint hy hη).code
      (b.reindex hs).raw (b.reindex hs).code := by
  let p' := (p.reindex hΓ hs).withEndpoints rfl hy rfl hη
  let b' := b.reindex hs
  have ep : TmEqDeriv Δ δ (.identity .base (x.reindex hs).raw (x.reindex hs).raw)
      (identityCode (baseCode δ) (x.reindex hs).code (x.reindex hs).code)
      p'.raw p'.code (.refl (x.reindex hs).raw) (reflCode (baseCode δ) (x.reindex hs).code) := by
    apply TmEqDeriv.native p'.deriv hp
    funext M
    exact eq_of_heq ((Path.withEndpoints_eval (p.reindex hΓ hs) rfl hy rfl hη M).trans (hπ M))
  have eb := (transport_congr hΔ p' (Path.reflexivity hΔ (x.reindex hs)) b' b' ep (.refl b'.deriv)).trans
    (transport_beta hΔ (x.reindex hs) b')
  have e := transport_reindex_conversion hΓ hΔ p b hs
  have e' := (e.rawType (congrArg Expr.fiber hy)).annotateType (congrArg fiberCode hη)
  have en := transport_native hΔ (p.reindex hΓ hs) p' b' b' rfl hy rfl rfl rfl hη
    (fun M => (Path.withEndpoints_eval (p.reindex hΓ hs) rfl hy rfl hη M).symm) (fun _ => HEq.rfl)
  exact e'.trans (en.trans eb)

def transport_nested_reindex_beta (hΓ : CtxDeriv Γ γ) (hΔ : CtxDeriv Δ δ)
    {x y z : BasePoint Γ γ} (p : Path x y) (q : Path y z) (b : FiberElement x)
    (hs : SubDeriv Δ δ Γ γ σ s)
    (hy : (y.reindex hs).raw = (x.reindex hs).raw)
    (hη : (y.reindex hs).code = (x.reindex hs).code)
    (innerEq : TmEqDeriv Δ δ (.fiber (x.reindex hs).raw) (fiberCode (x.reindex hs).code)
      ((transport hΓ p b).reindex hs).raw (((transport hΓ p b).reindex hs).withPoint hy hη).code
      (b.reindex hs).raw (b.reindex hs).code) :
    TmEqDeriv Δ δ (.fiber (z.reindex hs).raw) (fiberCode (z.reindex hs).code)
      ((transport hΓ q (transport hΓ p b)).reindex hs).raw
      ((transport hΓ q (transport hΓ p b)).reindex hs).code
      (transport hΔ ((q.reindex hΓ hs).withEndpoints hy rfl hη rfl) (b.reindex hs)).raw
      (transport hΔ ((q.reindex hΓ hs).withEndpoints hy rfl hη rfl) (b.reindex hs)).code := by
  let q' := (q.reindex hΓ hs).withEndpoints hy rfl hη rfl
  let inner := ((transport hΓ p b).reindex hs).withPoint hy hη
  have e := transport_reindex_conversion hΓ hΔ q (transport hΓ p b) hs
  have en := transport_native hΔ (q.reindex hΓ hs) q'
    ((transport hΓ p b).reindex hs) inner hy rfl rfl rfl hη rfl
    (fun M => (Path.withEndpoints_eval (q.reindex hΓ hs) hy rfl hη rfl M).symm)
    (fun M => (FiberElement.withPoint_eval ((transport hΓ p b).reindex hs) hy hη M).symm)
  exact e.trans (en.trans (transport_congr hΔ q' q' inner (b.reindex hs) (.refl q'.deriv) innerEq))

end SquareKit.Internal.PathTransport.Typed.Authoring
