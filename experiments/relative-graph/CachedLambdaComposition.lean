import CachedDefeqComposition
/-! Experimental positive cached lambda-inference composition for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedLambdaComposition
open ConLeche ConLeche.Cached CachedTransitionComposition
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
theorem infer_miss (mode : CheckMode) (fe : FEnv) (f d : Nat) (e ty : Expr) (s out : CState)
    (hm : s.inferC[e]? = none)
    (hb : inferBodyI (coreKnotI mode fe f) fe d e s = .ok (ty,out)) :
    (coreKnotI mode fe (f+1)).infer d e s =
      .ok (ty,{out with inferC := out.inferC.insert e ty}) := by
  rw [CachedReductionEquations.infer]
  exact memo_miss _ _ _ d e ty s out hm hb

theorem step (r : CoreFnsI) (d fuel k : Nat) (ty body tyo tty result : Expr)
    (fvs : Array Expr) (stk : List Expr) (u : Level) (s s1 s2 out : CState)
    (hi : instListRevM ty fvs 0 s = .ok (tyo,s))
    (ht : r.infer (d+k) tyo s = .ok (tty,s1))
    (hw : r.whnf (d+k) tty s1 = .ok (.sort u,s2))
    (hn : inferLamsI r d fuel body (k+1) (fvs.push (.fvar (d+k) tyo)) (tyo::stk) s2 = .ok (result,out)) :
    inferLamsI r d (fuel+1) (.lam ty body) k fvs stk s = .ok (result,out) := by
  unfold inferLamsI
  refine bind_ok _ _ s s out _ _ hi ?_
  refine bind_ok _ _ s s1 out _ _ ht ?_
  refine bind_ok _ _ s1 s2 out _ _ hw ?_
  exact bind_ok _ _ s2 s2 out _ _ rfl hn

theorem leaf (r : CoreFnsI) (d k : Nat) (body ob bt abs result : Expr)
    (fvs : Array Expr) (stk : List Expr) (s s1 out : CState)
    (hi : instListRevM body fvs 0 s = .ok (ob,s))
    (hb : r.infer (d+k) ob s = .ok (bt,s1))
    (ha : abstractRangeM bt d k s1 = .ok (abs,s1))
    (ho : inferLamsOutI d stk (k-1) abs s1 = .ok (result,out)) :
    inferLamsLeafI r d body k fvs stk s = .ok (result,out) := by
  unfold inferLamsLeafI
  refine bind_ok _ _ s s out _ _ hi ?_
  refine bind_ok _ _ s s1 out _ _ hb ?_
  exact bind_ok _ _ s1 s1 out _ _ ha ho

theorem body (r : CoreFnsI) (fe : FEnv) (d : Nat) (ty body tty result : Expr)
    (u : Level) (s s1 s2 out : CState)
    (hi : r.infer d ty s = .ok (tty,s1))
    (hw : r.whnf d tty s1 = .ok (.sort u,s2))
    (ht : inferLamsI r d peelFuel body 1 #[.fvar d ty] [ty] s2 = .ok (result,out)) :
    inferBodyI r fe d (.lam ty body) s = .ok (result,out) := by
  unfold inferBodyI
  refine bind_ok _ _ s s1 out _ _ hi ?_
  refine bind_ok _ _ s1 s2 out _ _ hw ?_
  refine bind_ok _ _ s2 s2 out _ _ rfl ?_
  exact bind_ok _ _ s2 s2 out _ _ rfl ht
end CachedLambdaComposition
#audit_graph_module
