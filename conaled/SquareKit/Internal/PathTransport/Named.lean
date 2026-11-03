import SquareKit.Internal.PathTransport.Authoring

/-! Named typed values for the externally parameterized base and its family.
Every value retains a generated source derivation. Context changes use typed
simultaneous substitutions; interpretation annotations are internal bookkeeping. -/
namespace SquareKit.Internal.PathTransport.Typed.Authoring
open SquareKit.Internal.PathTransport
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def _root_.SquareKit.Internal.PathTransport.Typed.TmDeriv.rawType (h : A = B) (t : TmDeriv Γ γ A a x ξ) : TmDeriv Γ γ B a x ξ := h ▸ t

def BasePoint.reindex (x : BasePoint Γ γ) (hs : SubDeriv Δ δ Γ γ σ s) : BasePoint Δ δ where
  raw := x.raw.sub σ
  code := castCode (baseSub_code s) (subTmCode x.code s)
  deriv := (TmDeriv.sub x.deriv hs).convert (.baseSub hs)

structure Path {Γ : RawCtx} {γ : CtxCode.{u}} (x y : BasePoint Γ γ) where
  raw : Expr
  code : TmCode γ (identityCode (baseCode γ) x.code y.code)
  deriv : TmDeriv Γ γ (.identity .base x.raw y.raw)
    (identityCode (baseCode γ) x.code y.code) raw code

structure FiberElement {Γ : RawCtx} {γ : CtxCode.{u}} (x : BasePoint Γ γ) where
  raw : Expr
  code : TmCode γ (fiberCode x.code)
  deriv : TmDeriv Γ γ (.fiber x.raw) (fiberCode x.code) raw code

def Path.reflexivity (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) : Path x x :=
  ⟨.refl x.raw, _, .refl (.base hΓ) x.deriv⟩

def Path.type (hΓ : CtxDeriv Γ γ) {x y : BasePoint Γ γ} (_p : Path x y) :=
  TyDeriv.identity (.base hΓ) x.deriv y.deriv

def Path.reindex (hΓ : CtxDeriv Γ γ) {x y : BasePoint Γ γ} (p : Path x y)
    (hs : SubDeriv Δ δ Γ γ σ s) : Path (x.reindex hs) (y.reindex hs) := by
  let e := TyEqDeriv.trans (.identitySub (.base hΓ) x.deriv y.deriv hs)
    (TyEqDeriv.identityCongr (.baseSub hs) (.sub x.deriv hs) (.sub y.deriv hs))
  exact ⟨p.raw.sub σ, _, (TmDeriv.sub p.deriv hs).convert e⟩

def FiberElement.reindex {x : BasePoint Γ γ} (b : FiberElement x)
    (hs : SubDeriv Δ δ Γ γ σ s) : FiberElement (x.reindex hs) :=
  ⟨b.raw.sub σ, _, (TmDeriv.sub b.deriv hs).convert (.fiberSub x.deriv hs)⟩

/-- A bound path uses the same named endpoints, weakened into the extension. -/
def Path.variable (hΓ : CtxDeriv Γ γ) (x y : BasePoint Γ γ) :
    Path (x.reindex (.weaken hΓ (.identity (.base hΓ) x.deriv y.deriv)))
      (y.reindex (.weaken hΓ (.identity (.base hΓ) x.deriv y.deriv))) := by
  let A := TyDeriv.identity (.base hΓ) x.deriv y.deriv
  let s := SubDeriv.weaken hΓ A
  let t := TmDeriv.var hΓ A
  let ht := t.rawType (Expr.sub_var_rename (.identity .base x.raw y.raw) Nat.succ).symm
  let e := TyEqDeriv.trans (.identitySub (.base hΓ) x.deriv y.deriv s)
    (TyEqDeriv.identityCongr (.baseSub s) (.sub x.deriv s) (.sub y.deriv s))
  exact ⟨.var 0, _, ht.convert e⟩

def FiberElement.variable (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) :
    FiberElement (x.reindex (.weaken hΓ (.fiber x.deriv))) := by
  let A := TyDeriv.fiber x.deriv
  let s := SubDeriv.weaken hΓ A
  let ht := (TmDeriv.var hΓ A).rawType (Expr.sub_var_rename (.fiber x.raw) Nat.succ).symm
  exact ⟨.var 0, _, ht.convert (.fiberSub x.deriv s)⟩

end SquareKit.Internal.PathTransport.Typed.Authoring
