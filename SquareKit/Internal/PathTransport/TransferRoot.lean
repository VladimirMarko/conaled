import SquareKit.Internal.PathTransport.TransferFrame
namespace SquareKit.Internal.PathTransport.Typed.Authoring.TransferFrame
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ)
def tailCode : TelCode (pathCode (baseCode γ) x.code) 3 :=
  telCons (baseCode _) (telCons
    (identityCode (baseCode _) (ConcatFrame.yAtZ hΓ x).code (ConcatFrame.z hΓ x).code)
    (telCons (fiberCode (ConcatFrame.fixed hΓ x).code) (telNil _)))

theorem moving_projection : (moving hΓ x).code =
    baseReindexCode (Authoring.moving hΓ x).code (projectionCode (tailCode hΓ x)) := by
  change baseReindexCode (ConcatFrame.yAtQ hΓ x).code _ = _
  rw [ConcatFrame.y_projection, baseReindex_comp]
  congr 1
  funext M
  simp only [projectionCode, tailCode, ConcatFrame.tailCode, telCons, telNil,
    StructuralModel.Telescope.projection, compCode, M.comp_id_right, M.comp_assoc]
  rfl

theorem fixed_projection : (fixed hΓ x).code =
    baseReindexCode (x.reindex (pathProjection hΓ x)).code (projectionCode (tailCode hΓ x)) := by
  change baseReindexCode (baseReindexCode _ (projectionCode (ConcatFrame.tailCode hΓ x))) _ = _
  rw [baseReindex_comp]
  congr 1
  funext M
  simp only [projectionCode, tailCode, ConcatFrame.tailCode, telCons, telNil,
    StructuralModel.Telescope.projection, compCode, M.comp_id_right, M.comp_assoc]

  rfl

theorem moving_root_code : ((moving hΓ x).reindex (root hΓ x)).code =
    ((fixed hΓ x).reindex (root hΓ x)).code := by
  change baseReindexCode _ (rootTailCode (baseCode γ) x.code (tailCode hΓ x)) =
    baseReindexCode _ (rootTailCode (baseCode γ) x.code (tailCode hΓ x))
  rw [moving_projection, fixed_projection]
  exact (baseReindex_lift _ _ _).trans
    ((congrArg (fun t => baseReindexCode t _) (moving_at_root hΓ x)).trans
      ((congrArg (fun t => baseReindexCode t _) (fixed_at_root hΓ x)).symm.trans
        (baseReindex_lift _ _ _).symm))

theorem moving_root_raw : ((moving hΓ x).reindex (root hΓ x)).raw =
    ((fixed hΓ x).reindex (root hΓ x)).raw := by
  simp only [moving, fixed, root, tail, forgetB, ConcatFrame.yAtQ, ConcatFrame.yAtZ,
    ConcatFrame.fixed, Authoring.moving, BasePoint.reindex, BasePoint.variable,
    ConcatFrame.tailProjection, ConcatFrame.tail, pathProjection, Expr.sub_comp, Expr.sub,
    Expr.liftSubN, Expr.liftSub, reflexiveSub, consSub, Expr.rename, Expr.rename_comp, Function.comp_def]
  exact (Expr.sub_var_rename x.raw (fun n => n+1+1+1)).symm

theorem first_root_raw : ((first hΓ x).reindex (context hΓ x) (root hΓ x)).raw =
    .refl (((fixed hΓ x).reindex (root hΓ x)).raw) := by
  simp only [first, firstBeforeB, Path.reindex, Path.withEndpoints, pathWitness,
    fixed, root, tail, forgetB, ConcatFrame.fixed, BasePoint.reindex,
    ConcatFrame.tailProjection, ConcatFrame.tail, pathProjection, Expr.sub_comp, Expr.sub,
    Expr.liftSubN, Expr.liftSub, reflexiveSub, consSub, Expr.rename, Expr.rename_comp, Function.comp_def]
  exact congrArg Expr.refl (Expr.sub_var_rename x.raw (fun n => n+1+1+1)).symm

theorem first_projection (M : Model) : HEq ((first hΓ x).code M)
    (M.subTm ((pathWitness hΓ x).code M) (projectionCode (tailCode hΓ x) M)) := by
  unfold first Path.reindex firstBeforeB Path.withEndpoints
  apply (castCode_eval _ _ M).trans
  apply (subTm_cast_eval _ _ _ M).trans
  apply (subTm_cast_eval _ _ _ M).trans
  apply (M.subTm_comp _ _ _).trans
  apply subTm_substitution_heq
  simp only [projectionCode, tailCode,
    telCons, telNil, StructuralModel.Telescope.projection,
    M.comp_id_right, M.comp_assoc]
  rfl

theorem first_projection_type :
    identityCode (baseCode _) (fixed hΓ x).code (moving hΓ x).code =
      subTyCode (identityCode (baseCode _) (x.reindex (pathProjection hΓ x)).code
        (Authoring.moving hΓ x).code) (projectionCode (tailCode hΓ x)) := by
  rw [identityBaseSub_code, fixed_projection, moving_projection]
  rfl

theorem witness_root_type : subTyCode
    (identityCode (baseCode _) (x.reindex (pathProjection hΓ x)).code (Authoring.moving hΓ x).code)
    (rootCode (baseCode γ) x.code) = identityCode (baseCode γ) x.code x.code := by
  rw [identityBaseSub_code, fixed_at_root, moving_at_root]

theorem witness_root (M : Model) :
    HEq (M.subTm ((pathWitness hΓ x).code M) (rootCode (baseCode γ) x.code M))
      (M.reflexivity (M.base (γ M)) (x.code M)) := by
  unfold pathWitness
  apply (subTm_cast_eval _ _ _ M).trans
  exact M.toStructuralModel.variable_root _ _

theorem refl_heq (M : Model) {G : M.Context} {A A' : M.Family G} (h : A = A')
    {a : M.Section G A} {a' : M.Section G A'} (ha : HEq a a') :
    HEq (M.reflexivity A a) (M.reflexivity A' a') := by
  cases h
  cases eq_of_heq ha
  rfl

theorem first_root_eval (M : Model) :
    HEq (((first hΓ x).reindex (context hΓ x) (root hΓ x)).code M)
      (M.reflexivity (M.base _) (((fixed hΓ x).reindex (root hΓ x)).code M)) := by
  let P := projectionCode (telPullback (tailCode hΓ x) (rootCode (baseCode γ) x.code))
  unfold Path.reindex
  apply (castCode_eval _ _ M).trans
  apply (M.subTm_congr (congrArg (fun a => a M) (first_projection_type hΓ x))
    (first_projection hΓ x M) _).trans
  apply (M.subTm_comp _ _ _).trans
  apply (subTm_substitution_heq M _ (congrArg (fun s => s M)
    (projectionLift_code (tailCode hΓ x) (rootCode (baseCode γ) x.code)))).trans
  apply (M.subTm_comp _ _ _).symm.trans
  apply (M.subTm_congr (congrArg (fun a => a M) (witness_root_type hΓ x))
    (witness_root hΓ x M) (P M)).trans
  apply (M.refl_sub _ _ _).trans
  have hf : ((fixed hΓ x).reindex (root hΓ x)).code = baseReindexCode x.code P := by
    change baseReindexCode (fixed hΓ x).code _ = _
    rw [fixed_projection]
    exact (baseReindex_lift _ _ _).trans
      (congrArg (fun t => baseReindexCode t P) (fixed_at_root hΓ x))
  rw [hf]
  exact refl_heq M (M.base_sub (P M)) (castCode_eval (baseSub_code P) (subTmCode x.code P) M).symm

theorem first_root_code :
    HEq (((first hΓ x).reindex (context hΓ x) (root hΓ x)).code)
      (reflCode (baseCode _) (((fixed hΓ x).reindex (root hΓ x)).code)) := by
  let p := (first hΓ x).reindex (context hΓ x) (root hΓ x)
  let a := (fixed hΓ x).reindex (root hΓ x)
  have ht := congrArg (identityCode (baseCode _) a.code) (moving_root_code hΓ x)
  have he : castCode ht p.code = reflCode (baseCode _) a.code := by
    funext M
    exact eq_of_heq ((castCode_eval ht p.code M).trans (first_root_eval hΓ x M))
  exact (castCode_heq ht p.code).symm.trans (heq_of_eq he)
end SquareKit.Internal.PathTransport.Typed.Authoring.TransferFrame
