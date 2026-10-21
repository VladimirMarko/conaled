import SquareKit.Internal.PathTransport.SourceReindex

namespace SquareKit.Internal.PathTransport.Typed.Authoring
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def Path.withEndpoints {x y x' y' : BasePoint Γ γ} (p : Path x y)
    (hx : x.raw = x'.raw) (hy : y.raw = y'.raw)
    (hξ : x.code = x'.code) (hη : y.code = y'.code) : Path x' y' :=
  ⟨p.raw, _, (p.deriv.rawType (congrArg₂ (Expr.identity .base) hx hy)).annotateType
    (congrArg₂ (identityCode (baseCode γ)) hξ hη)⟩

theorem pathWitness_type (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) :
    subTyCode (pathFamilyCode (baseCode γ) x.code)
      (weakenCode _ (pathFamilyCode (baseCode γ) x.code)) =
      identityCode (baseCode _) (x.reindex (pathProjection hΓ x)).code (moving hΓ x).code := by
  funext M
  apply (M.identity_sub _ _ _ _).trans
  apply M.toStructuralModel.identity_congr ((M.subTy_comp _ _ _).trans (M.base_sub _))
  · apply (M.subTm_comp _ _ _).trans
    symm
    unfold BasePoint.reindex
    exact castCode_eval _ _ M
  · symm
    unfold moving BasePoint.reindex BasePoint.variable
    exact (castCode_eval _ _ M).trans (subTm_cast_eval _ _ _ M)

def pathWitness (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) :
    Path (x.reindex (pathProjection hΓ x)) (moving hΓ x) := by
  let t := TmDeriv.var (.ext hΓ (.base hΓ)) (TyDeriv.pathFamily hΓ (.base hΓ) x.deriv)
  have hr : (Expr.identity .base (x.raw.rename Nat.succ) (.var 0)).rename Nat.succ =
      .identity .base (x.reindex (pathProjection hΓ x)).raw (moving hΓ x).raw := by
    simp only [Expr.rename, BasePoint.reindex, pathProjection, moving, BasePoint.variable,
      Expr.sub, Expr.rename_comp, Function.comp_def]
    exact congrArg (fun a => Expr.identity .base a (.var 1))
      (Expr.sub_var_rename x.raw (fun n => n+1+1)).symm
  exact ⟨.var 0, _, (t.rawType hr).annotateType (pathWitness_type hΓ x)⟩

namespace TransferFrame
variable (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ)
def beforeB := ConcatFrame.withQ hΓ x
def bType := TyDeriv.fiber (ConcatFrame.fixed hΓ x).deriv
def context := CtxDeriv.ext (beforeB hΓ x) (bType hΓ x)
def forgetB := SubDeriv.weaken (beforeB hΓ x) (bType hΓ x)
def fixed := (ConcatFrame.fixed hΓ x).reindex (forgetB hΓ x)
def moving := (ConcatFrame.yAtQ hΓ x).reindex (forgetB hΓ x)
def last := (ConcatFrame.zAtQ hΓ x).reindex (forgetB hΓ x)
def element := FiberElement.variable (beforeB hΓ x) (ConcatFrame.fixed hΓ x)
def second := (ConcatFrame.q hΓ x).reindex (beforeB hΓ x) (forgetB hΓ x)
def firstBeforeB : Path (ConcatFrame.fixed hΓ x) (ConcatFrame.yAtQ hΓ x) := by
  let p := (pathWitness hΓ x).reindex (ConcatFrame.paths hΓ x) (ConcatFrame.tailProjection hΓ x)
  exact p.withEndpoints rfl rfl rfl (ConcatFrame.y_projection hΓ x).symm

def first := (firstBeforeB hΓ x).reindex (beforeB hΓ x) (forgetB hΓ x)
def left := transport (context hΓ x) (concat (context hΓ x) (first hΓ x) (second hΓ x)) (element hΓ x)
def right := transport (context hΓ x) (second hΓ x)
  (transport (context hΓ x) (first hΓ x) (element hΓ x))
def motive := TyDeriv.identity (.fiber (last hΓ x).deriv) (left hΓ x).deriv (right hΓ x).deriv

def tail := TelDeriv.cons (ConcatFrame.zType hΓ x)
  (.cons (ConcatFrame.qType hΓ x) (.cons (bType hΓ x) (.nil (context hΓ x))))
def root := SubDeriv.rootTail hΓ (.base hΓ) x.deriv (tail hΓ x)
end TransferFrame
end SquareKit.Internal.PathTransport.Typed.Authoring
