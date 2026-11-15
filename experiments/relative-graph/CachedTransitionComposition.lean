import AcceptanceMeasurement
import ConLeche.Verify.Cached.KnotC

/-! Experimental #417 state-transition composition.
See [artifact scope](../../docs/research/relative-emitted-acceptance.md). -/
namespace CachedTransitionComposition
open ConLeche ConLeche.Cached
set_option maxRecDepth 2000
set_option maxHeartbeats 200000
set_option pp.deepTerms.threshold 4

theorem bind_ok {α β : Type} (x : CheckCM α) (k : α → CheckCM β)
    (s s' s'' : CState) (a : α) (b : β)
    (hx : x s = .ok (a,s')) (hk : k a s' = .ok (b,s'')) :
    (x >>= k) s = .ok (b,s'') := by
  change (Except.bind (x s) fun p => k p.1 p.2) = _
  rw [hx]
  exact hk

measured_theorem memo_miss : ∀ (get' : CState → Std.HashMap Expr Expr)
    (set' : CState → Std.HashMap Expr Expr → CState)
    (f : Nat → Expr → CheckCM Expr) (d : Nat) (e r : Expr) (s s' : CState),
    (get' s)[e]? = none → f d e s = .ok (r,s') →
    memoEI get' set' f d e s =
      .ok (r, set' (set' s' ∅) ((get' s').insert e r)) := by
  intro get' set' f d e r s s' hm hr
  unfold memoEI
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, Except.pure, Except.bind]
  rw [hm]
  dsimp only [StateT.bind]
  rw [hr]
  rfl

measured_theorem memo_hit : ∀ (get' : CState → Std.HashMap Expr Expr)
    (set' : CState → Std.HashMap Expr Expr → CState)
    (f : Nat → Expr → CheckCM Expr) (d : Nat) (e r : Expr) (s : CState),
    (get' s)[e]? = some r → memoEI get' set' f d e s = .ok (r,s) := by
  intro get' set' f d e r s h
  unfold memoEI
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, Except.pure, Except.bind]
  rw [h]
  rfl

measured_theorem whnf_core_sort_body : ∀ (mode : CheckMode) (r : CoreFnsI)
    (fe : FEnv) (cheap : Bool) (d : Nat) (u : Level),
    whnfCoreBodyI mode r fe cheap d (.sort u) = pure (.sort u) := by
  intro mode r fe cheap d u
  unfold whnfCoreBodyI whnfCoreLoopFuel
  rfl

measured_theorem whnf_sort_body : ∀ (r : CoreFnsI) (fe : FEnv) (d : Nat)
    (u : Level) (s s' : CState),
    r.whnfCore false d (.sort u) s = .ok (.sort u,s') →
    whnfBodyI r fe d (.sort u) s = .ok (.sort u,s') := by
  intro r fe d u s s' h
  unfold whnfBodyI whnfLoopFuel
  change (r.whnfCore false d (.sort u) >>= _) s = _
  simp only [bind, StateT.bind]
  rw [h]
  rfl

measured_theorem infer_pis_sort : ∀ (r : CoreFnsI) (d fuel : Nat)
    (u : Level) (k : Nat) (fvs : Array Expr) (stk : List Level),
    inferPisI r d fuel (.sort u) k fvs stk =
      inferPisLeafI r d (.sort u) k fvs stk := by
  intro r d fuel u k fvs stk
  cases fuel <;> rfl

def insertCoreSort (s : CState) (u : Level) : CState :=
  { s with whnfCoreC := s.whnfCoreC.insert (.sort u) (.sort u) }

def insertWhnfSort (s : CState) (u : Level) : CState :=
  { s with whnfC := s.whnfC.insert (.sort u) (.sort u) }

measured_theorem core_sort_miss : ∀ (env : Env) (f d : Nat) (u : Level) (s : CState),
    s.whnfCoreC[Expr.sort u]? = none →
    (coreKnotI .verified (mkFEnv env) (f + 1)).whnfCore false d (.sort u) s =
      .ok (.sort u, insertCoreSort s u) := by
  intro env f d u s hm
  rw [coreKnotI_whnfCore_succ]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply memo_miss (s' := s)
  · exact hm
  · rw [whnf_core_sort_body]
    rfl

measured_theorem whnf_sort_miss : ∀ (env : Env) (f d : Nat) (u : Level) (s : CState),
    s.whnfC[Expr.sort u]? = none → s.whnfCoreC[Expr.sort u]? = none →
    (coreKnotI .verified (mkFEnv env) ((f + 1) + 1)).whnf d (.sort u) s =
      .ok (.sort u, insertWhnfSort (insertCoreSort s u) u) := by
  intro env f d u s hm hc
  rw [coreKnotI_whnf_succ]
  apply memo_miss (s' := insertCoreSort s u)
  · exact hm
  · apply whnf_sort_body
    exact core_sort_miss env f d u s hc

measured_theorem ensure_sort_of_whnf : ∀ (r : CoreFnsI) (d : Nat) (u : Level) (s s' : CState),
    r.whnf d (.sort u) s = .ok (.sort u,s') →
    ensureSortI r d (.sort u) s = .ok (u,s') := by
  intro r d u s s' h
  unfold ensureSortI
  exact bind_ok _ _ s s' s' _ _ h rfl

measured_theorem constant_of_facts : ∀ (ops : CheckerOps CheckCM) (fe : FEnv)
    (cv : ConstantVal) (stype : Expr) (u : Level) (s s' s'' : CState),
    fe.find? cv.name = none → reservedBasisNames.contains cv.name = false →
    Name.nodup cv.levelParams = true → cv.type.looseBVarsBounded 0 = true →
    cv.type.hasFvar = false → cv.type.allLevelParamsDefined cv.levelParams = true →
    cv.type.constsResolveF fe = true →
    ops.inferType fe.env 0 cv.type s = .ok (stype,s') →
    ops.ensureSort fe.env 0 stype s' = .ok (u,s'') →
    checkConstantValF ops fe cv s = .ok ((),s'') := by
  intro ops fe cv stype u s s' s'' hf hr hn hb hv hl hc hi hs
  simp only [checkConstantValF, hf, hr, hn, hb, hv, hl, hc, Option.isSome_none,
    Bool.false_eq_true, ↓reduceIte]
  apply bind_ok _ _ s s' s'' _ _ hi
  exact bind_ok _ _ s' s'' s'' _ _ hs rfl

measured_theorem tele_of_syntactic : ∀ (ops : CheckerOps CheckCM) (fe : FEnv)
    (nP : Nat) (ms : MemberShape) (bs : List Expr) (u : Level) (s s' : CState),
    ms.cvT.type.stripPis (nP + ms.nIdx) = some (bs, .sort u) →
    checkConstantValF ops fe ms.cvT s = .ok ((),s') →
    checkBlockTeleF ops fe nP ms s = .ok ((ms.cvT,u),s') := by
  intro ops fe nP ms bs u s s' ht hc
  unfold checkBlockTeleF
  apply bind_ok _ _ s s' s' _ _ hc
  simp only [checkSumTeleF, ht]
  refine bind_ok _ _ s' s' s' _ _ rfl ?_
  simp only [ht, unwrapOr]
  refine bind_ok _ _ s' s' s' _ _ rfl ?_
  simp only [BEq.rfl, Bool.true_eq_false, ↓reduceIte]
  rfl

measured_theorem inds_singleton : ∀ (ops : CheckerOps CheckCM) (fe : FEnv)
    (p : BlockParts) (isRec : Bool) (ms : MemberShape) (u : Level) (s s' : CState),
    p.members = [ms] → checkBlockTeleF ops fe p.nP ms s = .ok ((ms.cvT,u),s') →
    checkBlockIndsF ops fe p isRec s =
      .ok ((consBlockIndsF (p.toBlockShape.withSort u) isRec [ms.cvT] 0 fe,
        [ms.cvT],p.toBlockShape.withSort u),s') := by
  intro ops fe p isRec ms u s s' hp ht
  unfold checkBlockIndsF
  rw [hp]
  apply bind_ok _ _ s s' s' _ _ ht
  rfl

end CachedTransitionComposition
#audit_graph_module
