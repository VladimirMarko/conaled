import CachedLambdaComposition
/-! Experimental positive pending-value composition at the actual cached fuel.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedPendingRunComposition
open ConLeche ConLeche.Cached CachedTransitionComposition
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
def pendingOps (ops : CoreFnsI) (sort : Nat → Expr → CheckCM Level)
    (guards : ConstantVal → Expr → CheckCM Unit) (vg : ValueGroup) : CheckCM Unit := do
  flushC
  let jsty ← ops.infer 0 vg.cv.type
  let u ← sort 0 jsty
  if vg.kind = .thm then do
    unless (← liftFueled "level comparison" (Level.isEquiv u .zero)) do
      throw (.invalid s!"type of theorem {vg.cv.name} is not a proposition")
    guards vg.cv vg.jv
  let jvt ← ops.infer 0 vg.jv
  unless ← ops.defeq 0 jvt vg.cv.type do
    throw (.invalid s!"type mismatch in {vg.kind.word} {vg.cv.name}")
theorem pending_eq (fe : FEnv) (pc : PendingCheck) :
    checkPending .verified fe pc = pendingOps
      (coreKnotI .verified (fe.restrictTo pc.vis) checkFuel)
      (opSIxC .verified (fe.restrictTo pc.vis))
      (installValueGuardsC (fe.restrictTo pc.vis)) pc.vg := by
  rfl
abbrev defnOps (ops : CoreFnsI) (sort : Nat → Expr → CheckCM Level)
    (cv : ConstantVal) (value : Expr) :=
  pendingOps ops sort (fun _ _ => pure ()) ⟨.defn,cv,value⟩

theorem ops_run (ops : CoreFnsI) (sort : Nat → Expr → CheckCM Level)
    (guards : ConstantVal → Expr → CheckCM Unit)
    (cv : ConstantVal) (value ty vty : Expr) (u : Level) (s1 s2 s3 out : CState)
    (hi : ops.infer 0 cv.type {} = .ok (ty,s1))
    (hs : sort 0 ty s1 = .ok (u,s2))
    (hv : ops.infer 0 value s2 = .ok (vty,s3))
    (he : ops.defeq 0 vty cv.type s3 = .ok (true,out)) :
    pendingOps ops sort guards ⟨.defn,cv,value⟩ {} = .ok ((),out) := by
  unfold pendingOps
  refine bind_ok _ _ {} {} out _ _ rfl ?_
  refine bind_ok _ _ {} s1 out _ _ hi ?_
  refine bind_ok _ _ s1 s2 out _ _ hs ?_
  refine bind_ok _ _ s2 s3 out _ _ hv ?_
  exact bind_ok _ _ s3 out out _ _ he rfl
theorem defn_run (fe view : FEnv) (ops : CoreFnsI)
    (hop : coreKnotI .verified view checkFuel = ops)
    (cv : ConstantVal) (value : Expr) (pos vis : Nat)
    (hv : fe.restrictTo vis = view) (ty vty : Expr) (u : Level) (s1 s2 s3 out : CState)
    (hi : ops.infer 0 cv.type {} = .ok (ty,s1))
    (hs : opSIxC .verified view 0 ty s1 = .ok (u,s2))
    (hb : ops.infer 0 value s2 = .ok (vty,s3))
    (he : ops.defeq 0 vty cv.type s3 = .ok (true,out)) :
    checkPending .verified fe ⟨⟨.defn,cv,value⟩,pos,vis⟩ {} = .ok ((),out) := by
  rw [pending_eq]
  change pendingOps _ _ _ _ {} = _
  rw [hv, hop]
  exact ops_run _ _ _ _ _ _ _ _ _ _ _ _ hi hs hb he
end CachedPendingRunComposition
#audit_graph_module
