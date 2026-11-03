import SquareKit.Internal.PathTransport.ReindexCoherence
import SquareKit.Internal.PathTransport.RawReindex

namespace SquareKit.Internal.PathTransport.Typed.Authoring
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

 theorem moving_model (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) (M : Model) :
    (moving hΓ x).code M = M.toStructuralModel.baseMoving (M.base (γ M)) (x.code M) rfl := by
  apply eq_of_heq
  exact (castCode_eval _ _ M).trans ((subTm_cast_eval _ _ _ M).trans
    ((cast_heq _ _).symm.trans (cast_heq _ _).symm))

theorem transport_model_type (hΓ : CtxDeriv Γ γ) {x y : BasePoint Γ γ}
    (p : Path x y) (M : Model) :
    M.subTy (M.fiber (M.toStructuralModel.baseMoving (M.base (γ M)) (x.code M) rfl))
      (M.toStructuralModel.endpointSub (M.base (γ M)) (x.code M) (y.code M) (p.code M)) =
      M.fiber (y.code M) := by
  have h := congrFun (transportMotive_at hΓ x y p) M
  have he := endpointCode_eval (baseCode γ) x.code y.code p.code M
  exact (congrArg (fun t => M.subTy (M.fiber t) _) (moving_model hΓ x M).symm).trans
    ((congrArg (M.subTy _) he.symm).trans h)

theorem transport_model (hΓ : CtxDeriv Γ γ) {x y : BasePoint Γ γ}
    (p : Path x y) (b : FiberElement x) (M : Model) :
    HEq ((transport hΓ p b).code M)
      (M.transportApply (M.base (γ M)) (x.code M) (y.code M) (p.code M) rfl (b.code M)) := by
  apply (castCode_eval _ _ M).trans
  apply (subTm_substitution_heq M _ (endpointCode_eval _ _ _ _ M)).trans
  apply M.toStructuralModel.subTm_congr (congrArg M.fiber (moving_model hΓ x M))
  apply M.j_heq rfl HEq.rfl HEq.rfl HEq.rfl
    (heq_of_eq (congrArg M.fiber (moving_model hΓ x M)))
  exact (castCode_eval _ _ M).trans (cast_heq _ _).symm

theorem transport_code_reindex (hΓ : CtxDeriv Γ γ) (hΔ : CtxDeriv Δ δ)
    {x y : BasePoint Γ γ} (p : Path x y) (b : FiberElement x)
    (hs : SubDeriv Δ δ Γ γ σ s) :
    ((transport hΓ p b).reindex hs).code =
      (transport hΔ (p.reindex hΓ hs) (b.reindex hs)).code := by
  funext M
  apply eq_of_heq
  apply (castCode_eval _ _ M).trans
  apply (M.toStructuralModel.subTm_congr (transport_model_type hΓ p M).symm
    (transport_model hΓ p b M) (s M)).trans
  apply (M.transportApply_sub (x.code M) (y.code M) (p.code M) (b.code M) (s M)).trans
  apply HEq.trans _ (transport_model hΔ (p.reindex hΓ hs) (b.reindex hs) M).symm
  apply M.transportApply_congr (M.base_sub (s M))
    (castCode_eval (baseSub_code s) (subTmCode x.code s) M).symm
    (castCode_eval (baseSub_code s) (subTmCode y.code s) M).symm
  · apply (cast_heq _ _).trans
    symm
    unfold Path.reindex
    exact castCode_eval _ _ M
  · apply (cast_heq _ _).trans
    symm
    unfold FiberElement.reindex
    exact castCode_eval _ _ M

end SquareKit.Internal.PathTransport.Typed.Authoring
