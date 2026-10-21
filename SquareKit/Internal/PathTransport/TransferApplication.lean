import SquareKit.Internal.PathTransport.TransferRoot
namespace SquareKit.Internal.PathTransport.Typed.Authoring.TransferApplication
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (hΓ : CtxDeriv Γ γ) (x y z : BasePoint Γ γ)
  (p : Path x y) (q : Path y z) (b : FiberElement x)

theorem fiber_type_at : subTyCode (fiberCode (ConcatFrame.fixed hΓ x).code)
    (substitutionCode (ConcatApplication.endpoint hΓ x y z p q)) = fiberCode x.code :=
  (fiberSub_code _ _).trans (congrArg fiberCode (ConcatApplication.fixed_at hΓ x y z p q))

theorem fixed_at_raw : (ConcatFrame.fixed hΓ x).raw.sub
    (consSub q.raw (consSub z.raw (consSub p.raw (consSub y.raw Expr.var)))) = x.raw := by
  simp only [ConcatFrame.fixed, BasePoint.reindex, ConcatFrame.tailProjection, ConcatFrame.tail,
    pathProjection, Expr.sub_comp, Expr.sub, consSub]
  exact Expr.sub_id x.raw

def endpoint := SubDeriv.pair (TransferFrame.bType hΓ x)
  (ConcatApplication.endpoint hΓ x y z p q)
  ((b.deriv.rawType (congrArg Expr.fiber (fixed_at_raw hΓ x y z p q)).symm).annotateType
    (fiber_type_at hΓ x y z p q).symm)

def arguments : Fin 3 → Expr := fun i => if i.val = 0 then b.raw else if i.val = 1 then q.raw else z.raw

theorem endpoint_raw : eliminationSub y.raw p.raw (arguments x y z q b) =
    consSub b.raw (consSub q.raw (consSub z.raw (consSub p.raw (consSub y.raw Expr.var)))) := by
  funext n
  rcases n with _ | (_ | (_ | n))
  · rfl
  · rfl
  · rfl
  · simp [eliminationSub, argsSub, arguments, consSub]; omega

def sourceEndpoint := SubDeriv.rawTransport (endpoint_raw x y z p q b).symm (endpoint hΓ x y z p q b)

theorem fixed_at : baseReindexCode (TransferFrame.fixed hΓ x).code
    (substitutionCode (endpoint hΓ x y z p q b)) = x.code :=
  (baseReindex_weaken_pair _ _ _ _).trans (ConcatApplication.fixed_at hΓ x y z p q)

theorem moving_at : baseReindexCode (TransferFrame.moving hΓ x).code
    (substitutionCode (endpoint hΓ x y z p q b)) = y.code :=
  (baseReindex_weaken_pair _ _ _ _).trans (ConcatApplication.y_at hΓ x y z p q)

theorem last_at : baseReindexCode (TransferFrame.last hΓ x).code
    (substitutionCode (endpoint hΓ x y z p q b)) = z.code :=
  (baseReindex_weaken_pair _ _ _ _).trans (ConcatApplication.z_at hΓ x y z p q)

theorem element_at (M : Model) :
    HEq (M.subTm ((TransferFrame.element hΓ x).code M)
      (substitutionCode (endpoint hΓ x y z p q b) M)) (b.code M) :=
  (subTm_cast_eval _ _ _ M).trans ((M.variable_pair _ _ _).trans (castCode_eval _ _ M))

theorem second_at (M : Model) :
    HEq (M.subTm ((TransferFrame.second hΓ x).code M)
      (substitutionCode (endpoint hΓ x y z p q b) M)) (q.code M) := by
  unfold TransferFrame.second Path.reindex
  apply (subTm_cast_eval _ _ _ M).trans
  apply (M.subTm_comp _ _ _).trans
  apply (subTm_substitution_heq M _ (M.weaken_pair _ _ _)).trans
  exact ConcatApplication.q_at hΓ x y z p q M

theorem tail_endpoint : compCode (projectionCode (TransferFrame.tailCode hΓ x))
    (substitutionCode (endpoint hΓ x y z p q b)) = endpointCode (baseCode γ) x.code y.code p.code := by
  funext M
  simp only [projectionCode, TransferFrame.tailCode, telCons, telNil,
    StructuralModel.Telescope.projection, compCode, M.comp_id_right]
  change M.compSub (M.compSub _ (M.compSub _ _)) (M.pairSub _ _ _) = _
  rw [M.comp_assoc, M.comp_assoc, M.weaken_pair]
  simp only [pairCode, M.weaken_pair]

theorem first_at (M : Model) :
    HEq (M.subTm ((TransferFrame.first hΓ x).code M)
      (substitutionCode (endpoint hΓ x y z p q b) M)) (p.code M) := by
  apply (M.subTm_congr (congrArg (fun a => a M) (TransferFrame.first_projection_type hΓ x))
    (TransferFrame.first_projection hΓ x M) _).trans
  apply (M.subTm_comp _ _ _).trans
  apply (subTm_substitution_heq M _ (congrArg (fun s => s M) (tail_endpoint hΓ x y z p q b))).trans
  unfold pathWitness
  apply (subTm_cast_eval _ _ _ M).trans
  exact (M.variable_pair _ _ _).trans (castCode_eval _ _ M)

def targetSub := consSub b.raw (consSub q.raw (consSub z.raw (consSub p.raw (consSub y.raw Expr.var))))

theorem fixed_raw : (TransferFrame.fixed hΓ x).raw.sub (targetSub x y z p q b) = x.raw := by
  simp only [TransferFrame.fixed, TransferFrame.forgetB, BasePoint.reindex, Expr.sub_comp,
    targetSub, Expr.sub]
  exact fixed_at_raw hΓ x y z p q

theorem moving_raw : (TransferFrame.moving hΓ x).raw.sub (targetSub x y z p q b) = y.raw := rfl

theorem last_raw : (TransferFrame.last hΓ x).raw.sub (targetSub x y z p q b) = z.raw := rfl

theorem first_raw : (TransferFrame.first hΓ x).raw.sub (targetSub x y z p q b) = p.raw := rfl

theorem second_raw : (TransferFrame.second hΓ x).raw.sub (targetSub x y z p q b) = q.raw := rfl

theorem element_raw : (TransferFrame.element hΓ x).raw.sub (targetSub x y z p q b) = b.raw := rfl

theorem transport_raw_congr {Γ Δ : RawCtx} {γ δ : CtxCode}
    (hΓ : CtxDeriv Γ γ) (hΔ : CtxDeriv Δ δ)
    {x y : BasePoint Γ γ} {x' y' : BasePoint Δ δ}
    (p : Path x y) (p' : Path x' y') (b : FiberElement x) (b' : FiberElement x')
    (hx : x.raw = x'.raw) (hy : y.raw = y'.raw) (hp : p.raw = p'.raw) (hb : b.raw = b'.raw) :
    (transport hΓ p b).raw = (transport hΔ p' b').raw := by
  simp only [transport_raw_explicit]
  rw [hx, hy, hp, hb]

theorem concat_raw_congr {Γ Δ : RawCtx} {γ δ : CtxCode}
    (hΓ : CtxDeriv Γ γ) (hΔ : CtxDeriv Δ δ)
    {x y z : BasePoint Γ γ} {x' y' z' : BasePoint Δ δ}
    (p : Path x y) (p' : Path x' y') (q : Path y z) (q' : Path y' z')
    (hx : x.raw = x'.raw) (hy : y.raw = y'.raw) (hz : z.raw = z'.raw)
    (hp : p.raw = p'.raw) (hq : q.raw = q'.raw) :
    (concat hΓ p q).raw = (concat hΔ p' q').raw := by
  simp only [concat_raw_explicit]
  rw [hx, hy, hp]
  congr 1
  funext i
  change (if i.val = 0 then q.raw else z.raw) = (if i.val = 0 then q'.raw else z'.raw)
  rw [hz, hq]

theorem left_raw : (TransferFrame.left hΓ x).raw.sub (targetSub x y z p q b) =
    (transport hΓ (concat hΓ p q) b).raw := by
  change (transport (TransferFrame.context hΓ x) _ _).raw.sub _ = _
  apply (transport_raw_reindex (TransferFrame.context hΓ x) hΓ _ _ (endpoint hΓ x y z p q b)).trans
  refine transport_raw_congr hΓ hΓ _ _ _ _ ?_ ?_ ?_ ?_
  · exact fixed_raw hΓ x y z p q b
  · exact last_raw hΓ x y z p q b
  · change (concat (TransferFrame.context hΓ x) _ _).raw.sub _ = _
    apply (concat_raw_reindex (TransferFrame.context hΓ x) hΓ _ _ (endpoint hΓ x y z p q b)).trans
    refine concat_raw_congr hΓ hΓ _ _ _ _ ?_ ?_ ?_ ?_ ?_
    · exact fixed_raw hΓ x y z p q b
    · exact moving_raw hΓ x y z p q b
    · exact last_raw hΓ x y z p q b
    · exact first_raw hΓ x y z p q b
    · exact second_raw hΓ x y z p q b
  · exact element_raw hΓ x y z p q b

theorem right_raw : (TransferFrame.right hΓ x).raw.sub (targetSub x y z p q b) =
    (transport hΓ q (transport hΓ p b)).raw := by
  change (transport (TransferFrame.context hΓ x) _ _).raw.sub _ = _
  apply (transport_raw_reindex (TransferFrame.context hΓ x) hΓ _ _ (endpoint hΓ x y z p q b)).trans
  refine transport_raw_congr hΓ hΓ _ _ _ _ ?_ ?_ ?_ ?_
  · exact moving_raw hΓ x y z p q b
  · exact last_raw hΓ x y z p q b
  · exact second_raw hΓ x y z p q b
  change (transport (TransferFrame.context hΓ x) _ _).raw.sub _ = _
  apply (transport_raw_reindex (TransferFrame.context hΓ x) hΓ _ _ (endpoint hΓ x y z p q b)).trans
  refine transport_raw_congr hΓ hΓ _ _ _ _ ?_ ?_ ?_ ?_
  · exact fixed_raw hΓ x y z p q b
  · exact moving_raw hΓ x y z p q b
  · exact first_raw hΓ x y z p q b
  · exact element_raw hΓ x y z p q b

theorem motive_raw : (Expr.identity (.fiber (TransferFrame.last hΓ x).raw)
    (TransferFrame.left hΓ x).raw (TransferFrame.right hΓ x).raw).sub
      (eliminationSub y.raw p.raw (arguments x y z q b)) =
    .identity (.fiber z.raw) (transport hΓ (concat hΓ p q) b).raw
      (transport hΓ q (transport hΓ p b)).raw := by
  rw [endpoint_raw]
  change Expr.identity (.fiber ((TransferFrame.last hΓ x).raw.sub (targetSub x y z p q b)))
    ((TransferFrame.left hΓ x).raw.sub (targetSub x y z p q b))
    ((TransferFrame.right hΓ x).raw.sub (targetSub x y z p q b)) = _
  rw [last_raw, left_raw, right_raw]

/-- Instantiate a generated command with all named dependent arguments. -/
def applyCommand
    (cmd : @PathCommand Γ γ .base x.raw (baseCode γ) x.code 3
      [(.fiber (ConcatFrame.fixed hΓ x).raw),
        (.identity .base (ConcatFrame.yAtZ hΓ x).raw (ConcatFrame.z hΓ x).raw), .base]
      (TransferFrame.tailCode hΓ x)) :=
  cmd.motive.pathInduction hΓ (.base hΓ) x.deriv cmd.telescope y.deriv p.deriv
    (sourceEndpoint hΓ x y z p q b)

end SquareKit.Internal.PathTransport.Typed.Authoring.TransferApplication
