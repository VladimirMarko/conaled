import SquareKit.Internal.PathTransport.Derived

/-! Structural normalization used by the derived author operations. -/
namespace SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.PathTransport
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace StructuralModel
variable (M : StructuralModel.{u})
theorem Telescope.projection_liftSub {Γ Δ : M.Context} {n}
    (T : Telescope M Γ n) (s : M.Substitution Δ Γ) :
    M.compSub (Telescope.projection M T) (Telescope.liftSub M T s) =
      M.compSub s (Telescope.projection M (Telescope.pullback M T s)) :=
  match T with
  | .nil => (M.comp_id_left _).trans (M.comp_id_right _).symm
  | .cons A tail =>
    let P := Telescope.projection M (Telescope.pullback M tail (M.lift A s))
    (M.comp_assoc _ _ _).trans
      ((congrArg (M.compSub (M.weaken _ A)) (Telescope.projection_liftSub tail (M.lift A s))).trans
        ((M.comp_assoc (M.weaken _ A) (M.lift A s) P).symm.trans
          ((congrArg (fun k => M.compSub k P) (M.weaken_lift A s)).trans (M.comp_assoc _ _ _))))
termination_by sizeOf T
end StructuralModel

def baseReindexCode (ξ : TmCode γ (baseCode γ)) (s : SubCode δ γ) : TmCode δ (baseCode δ) :=
  castCode (baseSub_code s) (subTmCode ξ s)

theorem baseReindex_comp (ξ : TmCode γ (baseCode γ)) (s : SubCode δ γ) (t : SubCode θ δ) :
    baseReindexCode (baseReindexCode ξ s) t = baseReindexCode ξ (compCode s t) := by
  funext M
  apply eq_of_heq
  exact (castCode_eval _ _ M).trans ((Authoring.subTm_cast_eval _ _ _ M).trans
    ((M.subTm_comp _ _ _).trans
      (castCode_eval (baseSub_code (compCode s t)) (subTmCode ξ (compCode s t)) M).symm))

theorem baseReindex_id (ξ : TmCode γ (baseCode γ)) : baseReindexCode ξ (idCode γ) = ξ := by
  funext M
  exact eq_of_heq ((castCode_eval _ _ M).trans (M.subTm_id _))

theorem identityBaseSub_code (ξ η : TmCode γ (baseCode γ)) (s : SubCode δ γ) :
    subTyCode (identityCode (baseCode γ) ξ η) s =
      identityCode (baseCode δ) (baseReindexCode ξ s) (baseReindexCode η s) := by
  funext M
  apply (M.identity_sub _ _ _ _).trans
  exact M.toStructuralModel.identity_congr (M.base_sub (s M))
    (castCode_eval (baseSub_code s) (subTmCode ξ s) M).symm
    (castCode_eval (baseSub_code s) (subTmCode η s) M).symm

theorem projectionLift_code (T : TelCode γ n) (s : SubCode δ γ) :
    compCode (projectionCode T)
      (fun M => StructuralModel.Telescope.liftSub M.toStructuralModel (T M) (s M)) =
      compCode s (projectionCode (telPullback T s)) := by
  funext M
  exact StructuralModel.Telescope.projection_liftSub M.toStructuralModel _ _

theorem compCode_id_right (s : SubCode δ γ) : compCode s (idCode δ) = s :=
  funext fun M => M.comp_id_right _

theorem compCode_id_left (s : SubCode δ γ) : compCode (idCode γ) s = s :=
  funext fun M => M.comp_id_left _

theorem compCode_assoc (s : SubCode δ γ) (t : SubCode θ δ) (v : SubCode χ θ) :
    compCode (compCode s t) v = compCode s (compCode t v) :=
  funext fun M => M.comp_assoc _ _ _

theorem baseReindex_lift (ξ : TmCode γ (baseCode γ)) (T : TelCode γ n) (s : SubCode δ γ) :
    baseReindexCode (baseReindexCode ξ (projectionCode T))
      (fun M => StructuralModel.Telescope.liftSub M.toStructuralModel (T M) (s M)) =
      baseReindexCode (baseReindexCode ξ s) (projectionCode (telPullback T s)) :=
  (baseReindex_comp _ _ _).trans
    ((congrArg (baseReindexCode ξ) (projectionLift_code T s)).trans (baseReindex_comp _ _ _).symm)

namespace Authoring

theorem pathProjection_endpoint (_hΓ : CtxDeriv Γ γ) (x y : BasePoint Γ γ) (p : Path x y) :
    compCode (compCode (weakenCode γ (baseCode γ))
      (weakenCode (extendCode γ (baseCode γ)) (pathFamilyCode (baseCode γ) x.code)))
      (endpointCode (baseCode γ) x.code y.code p.code) = idCode γ := by
  funext M
  exact (M.comp_assoc _ _ _).trans
    ((congrArg (M.compSub _) (M.weaken_pair _ _ _)).trans (M.weaken_pair _ _ _))

theorem fixed_at_root (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) :
    baseReindexCode (x.reindex (pathProjection hΓ x)).code (rootCode (baseCode γ) x.code) = x.code := by
  have h := (pathProjection_endpoint hΓ x x (Path.reflexivity hΓ x))
  have hr := endpointCode_root (baseCode γ) x.code
  have h' : compCode (compCode (weakenCode γ (baseCode γ))
      (weakenCode (extendCode γ (baseCode γ)) (pathFamilyCode (baseCode γ) x.code)))
      (rootCode (baseCode γ) x.code) = idCode γ :=
    (congrArg (compCode _) hr).symm.trans h
  exact (baseReindex_comp _ _ _).trans ((congrArg (baseReindexCode x.code) h').trans (baseReindex_id _))

theorem moving_at_root (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) :
    baseReindexCode (moving hΓ x).code (rootCode (baseCode γ) x.code) = x.code :=
  (congrArg (baseReindexCode (moving hΓ x).code) (endpointCode_root _ _).symm).trans
    (moving_at hΓ x x (Path.reflexivity hΓ x))

end Authoring

end SquareKit.Internal.PathTransport.Typed
