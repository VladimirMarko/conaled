import AcceptanceMeasurement
import ConLeche.Verify.Cached.KnotC

/-! Experimental #417 state-transition composition.
See [artifact scope](../../docs/research/relative-emitted-acceptance.md). -/
namespace CachedTransitionComposition
open ConLeche ConLeche.Cached
set_option maxRecDepth 2000
set_option maxHeartbeats 200000
set_option pp.deepTerms.threshold 4

measured_theorem memo_miss : ∀ (get' : CState → Std.HashMap Expr Expr)
    (set' : CState → Std.HashMap Expr Expr → CState)
    (f : Nat → Expr → CheckCM Expr) (d : Nat) (e r : Expr) (s s' : CState),
    (get' s)[e]? = none → f d e s = .ok (r,s') →
    memoEI get' set' f d e s =
      .ok (r, set' (set' s' ∅) ((get' s').insert e r)) := by
  intro get' set' f d e r s s' hm hr
  unfold memoEI
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, Except.pure, Except.bind]
  rw [hm]
  dsimp only [StateT.bind]
  rw [hr]
  rfl

end CachedTransitionComposition
#audit_graph_module
