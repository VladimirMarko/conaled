import CachedTransitionComposition

/-! Experimental #417 positive cached binder-run composition.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedBinderComposition
open ConLeche ConLeche.Cached CachedTransitionComposition
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
set_option pp.deepTerms.threshold 4

measured_theorem pis_step : ∀ (r : CoreFnsI) (d fuel k : Nat)
    (ty body tyo result : Expr) (fvs : Array Expr) (stk : List Level) (u : Level)
    (s s1 s2 s3 s4 : CState),
    instListRevM ty fvs 0 s = .ok (tyo,s1) →
    r.infer (d + k) tyo s1 = .ok (.sort u,s2) →
    r.whnf (d + k) (.sort u) s2 = .ok (.sort u,s3) →
    inferPisI r d fuel body (k + 1) (fvs.push (.fvar (d + k) tyo)) (u :: stk) s3 =
      .ok (result,s4) →
    inferPisI r d (fuel + 1) (.forallE ty body) k fvs stk s = .ok (result,s4) := by
  intro r d fuel k ty body tyo result fvs stk u s s1 s2 s3 s4 hi ht hw hn
  unfold inferPisI
  refine bind_ok _ _ s s1 s4 _ _ hi ?_
  refine bind_ok _ _ s1 s2 s4 _ _ ht ?_
  refine bind_ok _ _ s2 s3 s4 _ _ hw ?_
  refine bind_ok _ _ s3 s3 s4 _ _ rfl ?_
  exact hn

measured_theorem pis_leaf : ∀ (r : CoreFnsI) (d k : Nat)
    (body ob : Expr) (fvs : Array Expr) (stk : List Level) (u out : Level)
    (s s1 s2 s3 s4 : CState),
    instListRevM body fvs 0 s = .ok (ob,s1) →
    r.infer (d + k) ob s1 = .ok (.sort u,s2) →
    r.whnf (d + k) (.sort u) s2 = .ok (.sort u,s3) →
    inferPisOutI stk u s3 = .ok (out,s4) →
    inferPisLeafI r d body k fvs stk s = .ok (.sort out,s4) := by
  intro r d k body ob fvs stk u out s s1 s2 s3 s4 hi ht hw ho
  unfold inferPisLeafI
  refine bind_ok _ _ s s1 s4 _ _ hi ?_
  refine bind_ok _ _ s1 s2 s4 _ _ ht ?_
  refine bind_ok _ _ s2 s3 s4 _ _ hw ?_
  exact bind_ok _ _ s3 s4 s4 _ _ ho rfl

measured_theorem forall_body : ∀ (r : CoreFnsI) (fe : FEnv) (d : Nat)
    (ty body result : Expr) (u : Level) (s s1 s2 s3 : CState),
    r.infer d ty s = .ok (.sort u,s1) →
    r.whnf d (.sort u) s1 = .ok (.sort u,s2) →
    inferPisI r d peelFuel body 1 #[.fvar d ty] [u] s2 = .ok (result,s3) →
    inferBodyI r fe d (.forallE ty body) s = .ok (result,s3) := by
  intro r fe d ty body result u s s1 s2 s3 hi hw ht
  unfold inferBodyI
  refine bind_ok _ _ s s1 s3 _ _ hi ?_
  refine bind_ok _ _ s1 s2 s3 _ _ hw ?_
  refine bind_ok _ _ s2 s2 s3 _ _ rfl ?_
  refine bind_ok _ _ s2 s2 s3 _ _ rfl ?_
  exact ht

measured_theorem inst_sort : ∀ (u : Level) (vs : Array Expr) (s : CState),
    instListRevM (.sort u) vs 0 s = .ok (.sort u,s) := by
  intro u vs s
  unfold instListRevM Expr.instantiateRev
  simp [Expr.bvarB, Expr.bvarBRaw_sort, satRange]
  rfl

measured_theorem spine_step : ∀ (r : CoreFnsI) (fe : FEnv) (d : Nat)
    (dom body dom' a ta result : Expr) (acc : Array Expr) (args : List Expr)
    (s s1 s2 s3 s4 : CState),
    instListRevM dom acc 0 s = .ok (dom',s1) →
    r.infer d a s1 = .ok (ta,s2) →
    defeqArgI r d a ta dom' s2 = .ok (true,s3) →
    inferSpineI r fe d body (acc.push a) args s3 = .ok (result,s4) →
    inferSpineI r fe d (.forallE dom body) acc (a :: args) s = .ok (result,s4) := by
  intro r fe d dom body dom' a ta result acc args s s1 s2 s3 s4 hd hi he hn
  unfold inferSpineI
  refine bind_ok _ _ s s1 s4 _ _ hd ?_
  refine bind_ok _ _ s1 s2 s4 _ _ hi ?_
  refine bind_ok _ _ s2 s3 s4 _ _ he ?_
  exact hn

measured_theorem app_body : ∀ (r : CoreFnsI) (fe : FEnv) (d : Nat)
    (a b head ty result : Expr) (args : List Expr) (s s1 s2 : CState),
    Expr.getAppFn (.app a b) = head → Expr.getAppArgsC (.app a b) = args →
    r.infer d head s = .ok (ty,s1) →
    inferSpineI r fe d ty #[] args s1 = .ok (result,s2) →
    inferBodyI r fe d (.app a b) s = .ok (result,s2) := by
  intro r fe d a b head ty result args s s1 s2 hh ha hi hs
  unfold inferBodyI
  rw [hh, ha]
  refine bind_ok _ _ s s s2 _ _ rfl ?_
  refine bind_ok _ _ s s s2 _ _ rfl ?_
  exact bind_ok _ _ s s1 s2 _ _ hi hs

measured_theorem pis_app : ∀ (r : CoreFnsI) (d fuel : Nat) (a b : Expr)
    (k : Nat) (fvs : Array Expr) (stk : List Level),
    inferPisI r d fuel (.app a b) k fvs stk = inferPisLeafI r d (.app a b) k fvs stk := by
  intro r d fuel a b k fvs stk
  cases fuel <;> rfl

end CachedBinderComposition
#audit_graph_module
