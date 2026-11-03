import SquareKit.Internal.PathTransport.Binding

/-! First-path concatenation, derived by J while retaining the second path.
This follows agda-unimath's concatenation at revision
75518656f287c203b41cb7f71df46e02b987a084. Source correspondence and the MIT notice
are retained in docs/research/agda-transfer-source-notice.md. -/
namespace SquareKit.Internal.PathTransport.Typed.Authoring
open SquareKit.Internal.PathTransport
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace ConcatFrame
variable (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ)
def paths := CtxDeriv.path hΓ (.base hΓ) x.deriv
def zType := TyDeriv.base (paths hΓ x)
def withZ := CtxDeriv.ext (paths hΓ x) (zType hΓ x)
def z := BasePoint.variable (paths hΓ x)
def yAtZ := (moving hΓ x).reindex (.weaken (paths hΓ x) (zType hΓ x))
def qType := TyDeriv.identity (.base (withZ hΓ x)) (yAtZ hΓ x).deriv (z hΓ x).deriv
def withQ := CtxDeriv.ext (withZ hΓ x) (qType hΓ x)
def q := Path.variable (withZ hΓ x) (yAtZ hΓ x) (z hΓ x)
def zAtQ := (z hΓ x).reindex (.weaken (withZ hΓ x) (qType hΓ x))
def yAtQ := (yAtZ hΓ x).reindex (.weaken (withZ hΓ x) (qType hΓ x))
def tail := TelDeriv.cons (zType hΓ x) (.cons (qType hΓ x) (.nil (withQ hΓ x)))
def tailProjection := SubDeriv.projection (paths hΓ x) (tail hΓ x)
def fixed := (x.reindex (pathProjection hΓ x)).reindex (tailProjection hΓ x)
def motive := TyDeriv.identity (.base (withQ hΓ x)) (fixed hΓ x).deriv (zAtQ hΓ x).deriv
def root := SubDeriv.rootTail hΓ (.base hΓ) x.deriv (tail hΓ x)
def tailCode : TelCode (pathCode (baseCode γ) x.code) 2 :=
  telCons (baseCode _) (telCons
    (identityCode (baseCode _) (yAtZ hΓ x).code (z hΓ x).code) (telNil _))

theorem y_projection : (yAtQ hΓ x).code =
    baseReindexCode (moving hΓ x).code (projectionCode (tailCode hΓ x)) := by
  exact (baseReindex_comp _ _ _).trans
    (congrArg (baseReindexCode (moving hΓ x).code)
      (congrArg (compCode _) (compCode_id_right _)).symm)

theorem y_root : baseReindexCode (yAtQ hΓ x).code (rootTailCode (baseCode γ) x.code (tailCode hΓ x)) =
    baseReindexCode (fixed hΓ x).code (rootTailCode (baseCode γ) x.code (tailCode hΓ x)) := by
  exact (congrArg (fun t => baseReindexCode t _) (y_projection hΓ x)).trans
    ((baseReindex_lift _ _ _).trans
      ((congrArg (fun t => baseReindexCode t _) (moving_at_root hΓ x)).trans
        ((congrArg (fun t => baseReindexCode t _) (fixed_at_root hΓ x)).symm.trans
          (baseReindex_lift _ _ _).symm)))

theorem branch_type :
    subTyCode (identityCode (baseCode _) (yAtQ hΓ x).code (zAtQ hΓ x).code)
      (rootTailCode (baseCode γ) x.code (tailCode hΓ x)) =
    subTyCode (identityCode (baseCode _) (fixed hΓ x).code (zAtQ hΓ x).code)
      (rootTailCode (baseCode γ) x.code (tailCode hΓ x)) :=
  (identityBaseSub_code _ _ _).trans
    ((congrArg (fun y => identityCode (baseCode _) y _) (y_root hΓ x)).trans
      (identityBaseSub_code _ _ _).symm)

theorem branch_raw :
    (Expr.identity .base (yAtQ hΓ x).raw (zAtQ hΓ x).raw).sub (Expr.liftSubN 2 (reflexiveSub x.raw)) =
    (Expr.identity .base (fixed hΓ x).raw (zAtQ hΓ x).raw).sub (Expr.liftSubN 2 (reflexiveSub x.raw)) := by
  simp only [yAtQ, yAtZ, fixed, moving, BasePoint.reindex, BasePoint.variable,
    tailProjection, tail, pathProjection, Expr.sub_comp, Expr.sub, Expr.liftSubN,
    Expr.liftSub, reflexiveSub, consSub, Expr.rename, Expr.rename_comp, Function.comp_def]
  exact congrArg (fun a => Expr.identity .base a _) (Expr.sub_var_rename x.raw (fun n => n+1+1)).symm

def branch := ((TmDeriv.sub (q hΓ x).deriv (root hΓ x)).rawType (branch_raw hΓ x)).annotateType
  (branch_type hΓ x)

def command :
    @PathCommand Γ γ .base x.raw (baseCode γ) x.code 2
      [(.identity .base (yAtZ hΓ x).raw (z hΓ x).raw), .base] (tailCode hΓ x) :=
  { context := hΓ
    type := .base hΓ
    point := x.deriv
    telescope := tail hΓ x
    motive :=
      { raw := .identity .base (fixed hΓ x).raw (zAtQ hΓ x).raw
        code := identityCode (baseCode _) (fixed hΓ x).code (zAtQ hΓ x).code
        typing := motive hΓ x
        branch := .var 0
        branchCode := _
        branchTyping := branch hΓ x } }

end ConcatFrame

namespace ConcatApplication
variable (hΓ : CtxDeriv Γ γ) (x y z : BasePoint Γ γ) (p : Path x y) (q : Path y z)

def endpointZ := bindBase (ConcatFrame.paths hΓ x)
  (SubDeriv.endpoint hΓ (.base hΓ) x.deriv y.deriv p.deriv) z

theorem y_at_z : baseReindexCode (ConcatFrame.yAtZ hΓ x).code
    (pairCode (baseCode _) (endpointCode (baseCode γ) x.code y.code p.code)
      (castCode (baseSub_code _).symm z.code)) = y.code :=
  (baseReindex_weaken_pair _ _ _ _).trans (moving_at hΓ x y p)

theorem q_type_at : subTyCode (identityCode (baseCode _)
    (ConcatFrame.yAtZ hΓ x).code (ConcatFrame.z hΓ x).code)
    (pairCode (baseCode _) (endpointCode (baseCode γ) x.code y.code p.code)
      (castCode (baseSub_code _).symm z.code)) =
    identityCode (baseCode γ) y.code z.code :=
  (identityBaseSub_code _ _ _).trans (congrArg₂ (identityCode (baseCode γ))
    (y_at_z hΓ x y z p)
    (variable_bindBase (ConcatFrame.paths hΓ x) (SubDeriv.endpoint hΓ (.base hΓ) x.deriv y.deriv p.deriv) z))

def endpoint := SubDeriv.pair (ConcatFrame.qType hΓ x) (endpointZ hΓ x y z p)
  (q.deriv.annotateType (q_type_at hΓ x y z p).symm)

theorem tail_endpoint : compCode (projectionCode (ConcatFrame.tailCode hΓ x))
    (substitutionCode (endpoint hΓ x y z p q)) = endpointCode (baseCode γ) x.code y.code p.code := by
  funext M
  exact (M.comp_assoc _ _ _).trans
    ((congrArg (M.compSub _) ((M.comp_assoc _ _ _).trans
      ((congrArg (M.compSub _) (M.comp_id_left _)).trans (M.weaken_pair _ _ _)))).trans
        (M.weaken_pair _ _ _))

theorem fixed_at : baseReindexCode (ConcatFrame.fixed hΓ x).code
    (substitutionCode (endpoint hΓ x y z p q)) = x.code :=
  (baseReindex_comp _ _ _).trans
    ((congrArg (baseReindexCode _) (tail_endpoint hΓ x y z p q)).trans
      ((baseReindex_comp _ _ _).trans
        ((congrArg (baseReindexCode x.code) (pathProjection_endpoint hΓ x y p)).trans (baseReindex_id _))))

theorem z_at : baseReindexCode (ConcatFrame.zAtQ hΓ x).code
    (substitutionCode (endpoint hΓ x y z p q)) = z.code :=
  (baseReindex_weaken_pair _ _ _ _).trans
    (variable_bindBase (ConcatFrame.paths hΓ x) (SubDeriv.endpoint hΓ (.base hΓ) x.deriv y.deriv p.deriv) z)

theorem y_at : baseReindexCode (ConcatFrame.yAtQ hΓ x).code
    (substitutionCode (endpoint hΓ x y z p q)) = y.code :=
  (baseReindex_weaken_pair _ _ _ _).trans (y_at_z hΓ x y z p)

theorem q_at (M : Model) : HEq (M.subTm ((ConcatFrame.q hΓ x).code M)
    (substitutionCode (endpoint hΓ x y z p q) M)) (q.code M) :=
  (subTm_cast_eval _ _ _ M).trans ((M.variable_pair _ _ _).trans (castCode_eval _ _ M))

theorem motive_at : subTyCode (identityCode (baseCode _)
    (ConcatFrame.fixed hΓ x).code (ConcatFrame.zAtQ hΓ x).code)
    (substitutionCode (endpoint hΓ x y z p q)) = identityCode (baseCode γ) x.code z.code :=
  (identityBaseSub_code _ _ _).trans
    (congrArg₂ (identityCode (baseCode γ)) (fixed_at hΓ x y z p q) (z_at hΓ x y z p q))

def arguments : Fin 2 → Expr := fun i => if i.val = 0 then q.raw else z.raw

theorem endpoint_raw : eliminationSub y.raw p.raw (arguments y z q) =
    consSub q.raw (consSub z.raw (consSub p.raw (consSub y.raw Expr.var))) := by
  funext n
  rcases n with _ | (_ | n)
  · rfl
  · rfl
  · simp [eliminationSub, argsSub, arguments, consSub]; omega

end ConcatApplication

/-- Concatenation eliminates its first path and retains its second path. -/
def concat (hΓ : CtxDeriv Γ γ) {x y z : BasePoint Γ γ}
    (p : Path x y) (q : Path y z) : Path x z := by
  let cmd := ConcatFrame.command hΓ x
  let hs := SubDeriv.rawTransport (ConcatApplication.endpoint_raw x y z p q).symm
    (ConcatApplication.endpoint hΓ x y z p q)
  let t := cmd.motive.pathInduction hΓ (.base hΓ) x.deriv cmd.telescope y.deriv p.deriv hs
  have hraw : (Expr.identity .base (ConcatFrame.fixed hΓ x).raw (ConcatFrame.zAtQ hΓ x).raw).sub
      (eliminationSub y.raw p.raw (ConcatApplication.arguments y z q)) = .identity .base x.raw z.raw := by
    rw [ConcatApplication.endpoint_raw x y z p q]
    simp only [ConcatFrame.fixed, BasePoint.reindex, ConcatFrame.tailProjection, ConcatFrame.tail,
      pathProjection, ConcatFrame.zAtQ, ConcatFrame.z, BasePoint.variable, Expr.sub_comp, Expr.sub, consSub]
    exact congrArg (fun a => Expr.identity .base a z.raw) (Expr.sub_id x.raw)
  exact ⟨_, _, (t.rawType hraw).annotateType (ConcatApplication.motive_at hΓ x y z p q)⟩


end SquareKit.Internal.PathTransport.Typed.Authoring
