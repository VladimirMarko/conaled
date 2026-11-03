import SquareKit.Internal.PathTransport.Concatenation

namespace SquareKit.Internal.PathTransport.Typed.Authoring
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace ConcatBeta
variable (hΓ : CtxDeriv Γ γ) (x z : BasePoint Γ γ) (q : Path x z)
def root := SubDeriv.root hΓ (.base hΓ) x.deriv
def zType := TyDeriv.sub (ConcatFrame.zType hΓ x) (root hΓ x)
def withZ := CtxDeriv.ext hΓ (zType hΓ x)
def liftRoot := liftSubstitution hΓ (ConcatFrame.zType hΓ x) (root hΓ x)
def qType := TyDeriv.sub (ConcatFrame.qType hΓ x) (liftRoot hΓ x)
def zArgs := SubDeriv.pair (zType hΓ x) (.id hΓ)
  (z.deriv.annotateType ((subTyId_code _).trans (baseSub_code (rootCode (baseCode γ) x.code))).symm)

theorem z_endpoint : compCode (substitutionCode (liftRoot hΓ x)) (substitutionCode (zArgs hΓ x z)) =
    substitutionCode (ConcatApplication.endpointZ hΓ x x z (Path.reflexivity hΓ x)) := by
  funext M
  apply M.toStructuralModel.lift_pair_congr
  · exact (M.comp_id_right _).trans (congrFun (endpointCode_root (baseCode γ) x.code) M).symm
  · exact (castCode_eval _ _ M).trans
      (castCode_eval (baseSub_code (endpointCode (baseCode γ) x.code x.code
        (reflCode (baseCode γ) x.code))).symm z.code M).symm

theorem q_type_at : subTyCode (subTyCode
    (identityCode (baseCode _) (ConcatFrame.yAtZ hΓ x).code (ConcatFrame.z hΓ x).code)
    (substitutionCode (liftRoot hΓ x))) (substitutionCode (zArgs hΓ x z)) =
    identityCode (baseCode γ) x.code z.code :=
  (subTyComp_code _ _ _).trans
    ((congrArg (subTyCode _) (z_endpoint hΓ x z)).trans
      (ConcatApplication.q_type_at hΓ x x z (Path.reflexivity hΓ x)))

theorem q_raw_at :
    ((Expr.identity .base (ConcatFrame.yAtZ hΓ x).raw (ConcatFrame.z hΓ x).raw).sub
      (Expr.liftSub (reflexiveSub x.raw))).sub (consSub z.raw Expr.var) =
      .identity .base x.raw z.raw := by
  simp only [ConcatFrame.yAtZ, ConcatFrame.z, moving, BasePoint.reindex, BasePoint.variable,
    Expr.sub, Expr.liftSub, reflexiveSub, consSub, Function.comp_def, Expr.sub_rename, Expr.rename]
  exact congrArg (fun a => Expr.identity .base a z.raw) (Expr.sub_id x.raw)

def args := SubDeriv.pair (qType hΓ x) (zArgs hΓ x z)
  ((q.deriv.rawType (q_raw_at hΓ x z).symm).annotateType (q_type_at hΓ x z).symm)
theorem endpoint_eq : compCode (rootTailCode (baseCode γ) x.code (ConcatFrame.tailCode hΓ x))
    (substitutionCode (args hΓ x z q)) =
    substitutionCode (ConcatApplication.endpoint hΓ x x z (Path.reflexivity hΓ x) q) := by
  funext M
  apply M.toStructuralModel.lift_pair_congr
  · exact congrFun (z_endpoint hΓ x z) M
  · exact (castCode_eval _ _ M).trans
      (castCode_eval (ConcatApplication.q_type_at hΓ x x z (Path.reflexivity hΓ x)).symm q.code M).symm

theorem args_raw : argsSub (ConcatApplication.arguments x z q) Expr.var =
    consSub q.raw (consSub z.raw Expr.var) := by
  funext n
  rcases n with _ | (_ | n)
  · rfl
  · rfl
  · simp [argsSub, ConcatApplication.arguments, consSub]; omega

end ConcatBeta

/-- The first-path reflexive equation is generated contextual beta. -/
def concat_beta (hΓ : CtxDeriv Γ γ) (x z : BasePoint Γ γ) (q : Path x z) :
    TmEqDeriv Γ γ (.identity .base x.raw z.raw) (identityCode (baseCode γ) x.code z.code)
      (concat hΓ (Path.reflexivity hΓ x) q).raw (concat hΓ (Path.reflexivity hΓ x) q).code
      q.raw q.code := by
  let cmd := ConcatFrame.command hΓ x
  let hs := SubDeriv.rawTransport (ConcatBeta.args_raw x z q).symm (ConcatBeta.args hΓ x z q)
  have e := TmEqDeriv.contextualBeta hΓ (.base hΓ) x.deriv cmd.telescope
    cmd.motive.typing cmd.motive.branchTyping hs
  have hraw : (Expr.identity .base (ConcatFrame.fixed hΓ x).raw (ConcatFrame.zAtQ hΓ x).raw).sub
      (eliminationSub x.raw (.refl x.raw) (ConcatApplication.arguments x z q)) = .identity .base x.raw z.raw := by
    have hr := ConcatApplication.endpoint_raw x x z (Path.reflexivity hΓ x) q
    simp only [Path.reflexivity] at hr
    rw [hr]
    simp only [ConcatFrame.fixed, BasePoint.reindex, ConcatFrame.tailProjection, ConcatFrame.tail,
      pathProjection, ConcatFrame.zAtQ, ConcatFrame.z, BasePoint.variable, Expr.sub_comp, Expr.sub, consSub]
    exact congrArg (fun a => Expr.identity .base a z.raw) (Expr.sub_id x.raw)
  have eraw := hraw ▸ e
  have hcomp := ConcatBeta.endpoint_eq hΓ x z q
  have hty := (congrArg (subTyCode cmd.motive.code) hcomp).trans
    (ConcatApplication.motive_at hΓ x x z (Path.reflexivity hΓ x) q)
  apply (eraw.annotateType hty).annotate
  · exact eq_of_heq ((castCode_heq _ _).trans
      ((subTmCode_substitution_heq _ hcomp).trans (castCode_heq _ _).symm))
  · funext M
    apply eq_of_heq
    apply (castCode_eval _ _ M).trans
    apply (castCode_eval _ _ M).trans
    apply (subTm_cast_eval _ _ _ M).trans
    apply (M.subTm_comp _ _ _).trans
    apply (subTm_substitution_heq M _ (congrFun hcomp M)).trans
    apply (subTm_cast_eval _ _ _ M).trans
    exact (M.variable_pair _ _ _).trans (castCode_eval _ _ M)

end SquareKit.Internal.PathTransport.Typed.Authoring
