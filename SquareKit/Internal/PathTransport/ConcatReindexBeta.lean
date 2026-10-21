import SquareKit.Internal.PathTransport.TransferRoot
import SquareKit.Internal.PathTransport.NativeNormalization

/-!
Concatenation's first-path J computes after an arbitrary substitution when its
first path becomes reflexivity. The proof constructs typed arguments in the
original dependent tail and invokes the generated `jBetaReindex` rule. The
transfer-frame specialization retains the actual reindexed source operations.
-/

namespace SquareKit.Internal.PathTransport.Typed.Authoring
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace ConcatReindexBeta
variable (hΓ : CtxDeriv Γ γ) (hΔ : CtxDeriv Δ δ)
variable (x y z : BasePoint Γ γ) (p : Path x y) (q : Path y z)
variable (hs : SubDeriv Δ δ Γ γ σ s)
variable (hE : compCode (rootCode (baseCode γ) x.code) s =
  compCode (endpointCode (baseCode γ) x.code y.code p.code) s)

def zArgs := SubDeriv.pair (ConcatBeta.zType hΓ x) hs
  ((z.reindex hs).deriv.annotateType ((subTyComp_code _ _ _).trans (baseSub_code _)).symm)

include hE in
theorem z_endpoint : compCode (substitutionCode (ConcatBeta.liftRoot hΓ x))
    (substitutionCode (zArgs hΓ x z hs)) =
    compCode (substitutionCode (ConcatApplication.endpointZ hΓ x y z p)) s := by
  funext M
  apply M.toStructuralModel.lift_pair_square
  · exact congrFun hE M
  · exact (castCode_eval _ _ M).trans
      ((castCode_eval _ _ M).trans (subTm_cast_eval _ _ _ M).symm)

include hE in
theorem q_type_at : subTyCode
    (subTyCode (identityCode (baseCode _) (ConcatFrame.yAtZ hΓ x).code (ConcatFrame.z hΓ x).code)
      (substitutionCode (ConcatBeta.liftRoot hΓ x)))
    (substitutionCode (zArgs hΓ x z hs)) =
    subTyCode (identityCode (baseCode γ) y.code z.code) s := by
  apply (subTyComp_code _ _ _).trans
  apply (congrArg (subTyCode _) (z_endpoint hΓ x y z p hs hE)).trans
  apply (subTyComp_code _ _ _).symm.trans
  exact congrArg (fun a => subTyCode a s) (ConcatApplication.q_type_at hΓ x y z p)

theorem q_raw_at (hy : y.raw.sub σ = x.raw.sub σ) :
    ((Expr.identity .base (ConcatFrame.yAtZ hΓ x).raw (ConcatFrame.z hΓ x).raw).sub
      (Expr.liftSub (reflexiveSub x.raw))).sub (consSub (z.raw.sub σ) σ) =
      (Expr.identity .base y.raw z.raw).sub σ := by
  have h := congrArg (Expr.sub σ) (ConcatBeta.q_raw_at hΓ x z)
  have hσ : (fun n => Expr.sub σ (consSub z.raw Expr.var n)) = consSub (z.raw.sub σ) σ := by
    funext n; cases n <;> rfl
  simp only [Expr.sub_comp] at h
  rw [hσ] at h
  simpa only [Expr.sub_comp, Expr.sub, hy] using h

def args (hy : y.raw.sub σ = x.raw.sub σ) :=
  SubDeriv.pair (ConcatBeta.qType hΓ x) (zArgs hΓ x z hs)
    (((TmDeriv.sub q.deriv hs).rawType (q_raw_at hΓ x y z hy).symm).annotateType
      (q_type_at hΓ x y z p hs hE).symm)

theorem endpoint_eq (hy : y.raw.sub σ = x.raw.sub σ) :
    compCode (rootTailCode (baseCode γ) x.code (ConcatFrame.tailCode hΓ x))
      (substitutionCode (args hΓ x y z p q hs hE hy)) =
      compCode (substitutionCode (ConcatApplication.endpoint hΓ x y z p q)) s := by
  funext M
  apply M.toStructuralModel.lift_pair_square
  · exact congrFun (z_endpoint hΓ x y z p hs hE) M
  · exact (castCode_eval _ _ M).trans (subTm_cast_eval _ _ _ M).symm

def arguments : Fin 2 → Expr := fun i => (ConcatApplication.arguments y z q i).sub σ

theorem args_raw : argsSub (arguments (σ := σ) y z q) σ =
    consSub (q.raw.sub σ) (consSub (z.raw.sub σ) σ) := by
  funext n
  rcases n with _ | (_ | n)
  · rfl
  · rfl
  · simp [argsSub, arguments, ConcatApplication.arguments, consSub]; omega

theorem left_raw (hy : y.raw.sub σ = x.raw.sub σ)
    (hp : p.raw.sub σ = .refl (x.raw.sub σ)) :
    (concat hΓ p q).raw.sub σ =
      .pathInduction 2 (Expr.base.sub σ) (x.raw.sub σ)
        ((ConcatFrame.command hΓ x).motive.raw.sub (Expr.liftSubN 4 σ))
        ((ConcatFrame.command hΓ x).motive.branch.sub (Expr.liftSubN 2 σ))
        (x.raw.sub σ) (.refl (x.raw.sub σ)) (arguments (σ := σ) y z q) := by
  change Expr.pathInduction 2 _ _ _ _ (y.raw.sub σ) (p.raw.sub σ) _ = _
  rw [hy, hp]
  rfl

theorem motive_raw : (ConcatFrame.command hΓ x).motive.raw.sub
    (argsSub (arguments (σ := σ) y z q) (consSub (.refl (x.raw.sub σ)) (consSub (x.raw.sub σ) σ))) =
      (Expr.identity .base x.raw z.raw).sub σ := by
  simp only [ConcatFrame.command, ConcatFrame.fixed, ConcatFrame.zAtQ, ConcatFrame.z,
    BasePoint.reindex, BasePoint.variable, ConcatFrame.tailProjection, ConcatFrame.tail,
    pathProjection, Expr.sub_comp, Expr.sub, argsSub, arguments, ConcatApplication.arguments,
    consSub, Function.comp_def]
  rfl

theorem result_type (hy : y.raw.sub σ = x.raw.sub σ) :
    subTyCode (ConcatFrame.command hΓ x).motive.code
      (compCode (rootTailCode (baseCode γ) x.code (ConcatFrame.tailCode hΓ x))
        (substitutionCode (args hΓ x y z p q hs hE hy))) =
    subTyCode (identityCode (baseCode γ) x.code z.code) s :=
  (congrArg (subTyCode _) (endpoint_eq hΓ x y z p q hs hE hy)).trans
    ((subTyComp_code _ _ _).symm.trans
      (congrArg (fun a => subTyCode a s) (ConcatApplication.motive_at hΓ x y z p q)))

theorem left_code (hy : y.raw.sub σ = x.raw.sub σ) :
    castCode (result_type hΓ x y z p q hs hE hy)
      (subTmCode (jCode (baseCode γ) x.code (ConcatFrame.tailCode hΓ x)
        (ConcatFrame.command hΓ x).motive.code (ConcatFrame.command hΓ x).motive.branchCode)
        (compCode (rootTailCode (baseCode γ) x.code (ConcatFrame.tailCode hΓ x))
          (substitutionCode (args hΓ x y z p q hs hE hy)))) =
      subTmCode (concat hΓ p q).code s := by
  funext M
  apply eq_of_heq
  apply (castCode_eval _ _ M).trans
  apply (subTm_substitution_heq M _ (congrFun (endpoint_eq hΓ x y z p q hs hE hy) M)).trans
  apply (M.subTm_comp _ _ _).symm.trans
  symm
  exact subTm_cast_eval (ConcatApplication.motive_at hΓ x y z p q) _ s M

theorem right_code (hy : y.raw.sub σ = x.raw.sub σ)
    (hQ : subTyCode (identityCode (baseCode γ) y.code z.code) s =
      subTyCode (identityCode (baseCode γ) x.code z.code) s) :
    castCode (result_type hΓ x y z p q hs hE hy)
      (castCode (subTyComp_code (ConcatFrame.command hΓ x).motive.code
        (rootTailCode (baseCode γ) x.code (ConcatFrame.tailCode hΓ x))
        (substitutionCode (args hΓ x y z p q hs hE hy)))
        (subTmCode (ConcatFrame.command hΓ x).motive.branchCode
          (substitutionCode (args hΓ x y z p q hs hE hy)))) =
      castCode hQ (subTmCode q.code s) := by
  funext M
  apply eq_of_heq
  apply (castCode_eval _ _ M).trans
  apply (castCode_eval _ _ M).trans
  apply (subTm_cast_eval _ _ _ M).trans
  apply (M.subTm_comp _ _ _).trans
  apply (subTm_substitution_heq M _ (congrFun (endpoint_eq hΓ x y z p q hs hE hy) M)).trans
  apply (M.subTm_comp _ _ _).symm.trans
  have hqt : subTyCode (identityCode (baseCode _) (ConcatFrame.yAtQ hΓ x).code
      (ConcatFrame.zAtQ hΓ x).code)
      (substitutionCode (ConcatApplication.endpoint hΓ x y z p q)) =
      identityCode (baseCode γ) y.code z.code :=
    (identityBaseSub_code _ _ _).trans
      (congrArg₂ (identityCode (baseCode γ)) (ConcatApplication.y_at hΓ x y z p q)
        (ConcatApplication.z_at hΓ x y z p q))
  apply (M.toStructuralModel.subTm_congr
    (congrFun hqt M)
    (ConcatApplication.q_at hΓ x y z p q M) (s M)).trans
  exact (castCode_eval hQ (subTmCode q.code s) M).symm

/-- Generated J beta after an arbitrary ambient substitution whose first path
has become reflexivity. The branch arguments remain typed in the original tail. -/
def beta (hy : y.raw.sub σ = x.raw.sub σ)
    (hp : p.raw.sub σ = .refl (x.raw.sub σ))
    (hQ : subTyCode (identityCode (baseCode γ) y.code z.code) s =
      subTyCode (identityCode (baseCode γ) x.code z.code) s) :
    TmEqDeriv Δ δ ((Expr.identity .base x.raw z.raw).sub σ)
      (subTyCode (identityCode (baseCode γ) x.code z.code) s)
      ((concat hΓ p q).raw.sub σ) (subTmCode (concat hΓ p q).code s)
      (q.raw.sub σ) (castCode hQ (subTmCode q.code s)) := by
  let cmd := ConcatFrame.command hΓ x
  let ha := SubDeriv.rawTransport (args_raw (σ := σ) y z q).symm (args hΓ x y z p q hs hE hy)
  have t := (TmDeriv.sub (concat hΓ p q).deriv hs).rawType (motive_raw (σ := σ) hΓ x y z q).symm
  have t' := (left_raw (σ := σ) hΓ x y z p q hy hp) ▸ t
  have t'' := t'.annotateType (result_type hΓ x y z p q hs hE hy).symm
  have hc : castCode (result_type hΓ x y z p q hs hE hy).symm
      (subTmCode (concat hΓ p q).code s) =
      subTmCode (jCode (baseCode γ) x.code (ConcatFrame.tailCode hΓ x)
        cmd.motive.code cmd.motive.branchCode)
        (compCode (rootTailCode (baseCode γ) x.code (ConcatFrame.tailCode hΓ x))
          (substitutionCode (args hΓ x y z p q hs hE hy))) := by
    exact eq_of_heq ((castCode_heq _ _).trans
      ((heq_of_eq (left_code hΓ x y z p q hs hE hy).symm).trans (castCode_heq _ _)))
  have t''' := hc ▸ t''
  have e := TmEqDeriv.jBetaReindex t''' cmd.motive.branchTyping ha
  have eraw := (motive_raw (σ := σ) hΓ x y z q) ▸ e
  have e' := eraw.annotateType (result_type hΓ x y z p q hs hE hy)
  have e'' := e'.annotate (left_code hΓ x y z p q hs hE hy) (right_code hΓ x y z p q hs hE hy hQ)
  exact e''.rawLeft (left_raw (σ := σ) hΓ x y z p q hy hp).symm

end ConcatReindexBeta

theorem endpoint_is_root (M : StructuralModel) {G : M.Context} (A : M.Family G)
    (a b : M.Section G A) (p : M.Section G (M.identity A a b))
    (hab : b = a) (hp : HEq p (M.reflexivity A a)) :
    M.endpointSub A a b p = M.rootSub A a := by
  cases hab
  cases hp
  rfl

theorem endpoint_root_sub (M : StructuralModel) {G H : M.Context} (A : M.Family G)
    (a b : M.Section G A) (p : M.Section G (M.identity A a b)) (s : M.Substitution H G)
    (hab : M.subTm b s = M.subTm a s)
    (hp : HEq (M.subTm p s) (M.reflexivity (M.subTy A s) (M.subTm a s))) :
    M.compSub (M.rootSub A a) s = M.compSub (M.endpointSub A a b p) s := by
  have he := endpoint_is_root M (M.subTy A s) (M.subTm a s) (M.subTm b s)
    (cast (congrArg (M.Section H) (M.identity_sub A a b s)) (M.subTm p s)) hab
    ((cast_heq _ _).trans hp)
  exact (M.pathSub_root A a s).symm.trans
    ((congrArg (M.compSub (M.pathSub A a s)) he.symm).trans (M.endpoint_sub A a b p s))

namespace TransferFrame
variable (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ)

theorem concat_root_endpoint :
    compCode (rootCode (baseCode _) (fixed hΓ x).code) (substitutionCode (root hΓ x)) =
      compCode (endpointCode (baseCode _) (fixed hΓ x).code (moving hΓ x).code (first hΓ x).code)
        (substitutionCode (root hΓ x)) := by
  funext M
  rw [compCode, compCode, endpointCode_eval]
  apply endpoint_root_sub M.toStructuralModel
  · apply eq_of_heq
    exact (castCode_eval (baseSub_code _) (subTmCode (moving hΓ x).code _) M).symm.trans
      ((heq_of_eq (congrFun (moving_root_code hΓ x) M)).trans
        (castCode_eval (baseSub_code _) (subTmCode (fixed hΓ x).code _) M))
  · have hf : HEq (((first hΓ x).reindex (context hΓ x) (root hΓ x)).code M)
        (M.subTm ((first hΓ x).code M) (substitutionCode (root hΓ x) M)) := by
      unfold Path.reindex
      exact castCode_eval _ _ M
    apply hf.symm.trans (first_root_eval hΓ x M |>.trans ?_)
    symm
    apply refl_heq M (M.base_sub _)
    exact (castCode_eval (baseSub_code _) (subTmCode (fixed hΓ x).code _) M).symm

theorem concat_root_type :
    subTyCode (identityCode (baseCode _) (moving hΓ x).code (last hΓ x).code)
      (substitutionCode (root hΓ x)) =
      subTyCode (identityCode (baseCode _) (fixed hΓ x).code (last hΓ x).code)
        (substitutionCode (root hΓ x)) := by
  rw [identityBaseSub_code, identityBaseSub_code]
  exact congrArg (fun a => identityCode (baseCode _) a _ ) (moving_root_code hΓ x)

def concat_root_beta := ConcatReindexBeta.beta (context hΓ x)
  (fixed hΓ x) (moving hΓ x) (last hΓ x) (first hΓ x) (second hΓ x)
  (root hΓ x) (concat_root_endpoint hΓ x) (moving_root_raw hΓ x)
  (first_root_raw hΓ x) (concat_root_type hΓ x)

def concatRootPath := (concat (context hΓ x) (first hΓ x) (second hΓ x)).reindex
  (context hΓ x) (root hΓ x)

def secondRootPath := ((second hΓ x).reindex (context hΓ x) (root hΓ x)).withEndpoints
  (moving_root_raw hΓ x) rfl (moving_root_code hΓ x) rfl

theorem concat_root_left_annotation :
    castCode (identityBaseSub_code (fixed hΓ x).code (last hΓ x).code (substitutionCode (root hΓ x)))
      (subTmCode (concat (context hΓ x) (first hΓ x) (second hΓ x)).code
        (substitutionCode (root hΓ x))) = (concatRootPath hΓ x).code := by
  unfold concatRootPath Path.reindex
  exact eq_of_heq ((castCode_heq _ _).trans (castCode_heq _ _).symm)

theorem concat_root_right_annotation :
    castCode (identityBaseSub_code (fixed hΓ x).code (last hΓ x).code (substitutionCode (root hΓ x)))
      (castCode (concat_root_type hΓ x)
        (subTmCode (second hΓ x).code (substitutionCode (root hΓ x)))) =
      (secondRootPath hΓ x).code := by
  unfold secondRootPath Path.withEndpoints Path.reindex
  exact eq_of_heq ((castCode_heq _ _).trans ((castCode_heq _ _).trans
    ((castCode_heq _ _).symm.trans (castCode_heq _ _).symm)))

/-- A source conversion between the actual reindexed concatenation and retained
second path, with both endpoints normalized in the reflexive branch. -/
def concat_root_normalized :=
  ((concat_root_beta hΓ x).annotateType
    (identityBaseSub_code (fixed hΓ x).code (last hΓ x).code (substitutionCode (root hΓ x)))).annotate
      (concat_root_left_annotation hΓ x) (concat_root_right_annotation hΓ x)

end TransferFrame
end SquareKit.Internal.PathTransport.Typed.Authoring
