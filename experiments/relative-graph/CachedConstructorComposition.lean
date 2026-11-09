import CachedTransitionComposition

/-! Experimental cached constructor-stage composition for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedConstructorComposition
open ConLeche ConLeche.Cached CachedTransitionComposition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

measured_theorem domains_step : ∀ (ops : CheckerOps CheckCM) (fe : FEnv) (off j : Nat)
    (fvs doms : Array Expr) (a b : Expr) (s s1 s2 : CState),
    fvs[j]? = some a → doms[j]? = some b →
    ops.isDefEq fe.env (off + j) a.fvarTypeD b s = .ok (true,s1) →
    checkStructDomsAtFA ops fe off fvs doms j s1 = .ok ((),s2) →
    checkStructDomsAtFA ops fe off fvs doms (j + 1) s = .ok ((),s2) := by
  intro ops fe off j fvs doms a b s s1 s2 ha hb he hr
  unfold checkStructDomsAtFA
  simp only [ha, hb, unwrapOr]
  refine bind_ok _ _ s s s2 a _ rfl ?_
  refine bind_ok _ _ s s s2 b _ rfl ?_
  refine bind_ok _ _ s s1 s2 true _ he ?_
  exact hr

measured_theorem prop_fields_step : ∀ (ops : CheckerOps CheckCM) (fe : FEnv)
    (large : Bool) (resSort : Level) (nP j : Nat) (fvs : Array Expr) (idxArgs : List Expr)
    (fv ty : Expr) (u : Level) (us : List Level) (s s1 s2 s3 : CState),
    (Level.isEquiv u .zero == some true || idxArgs.contains fv) = true →
    fvs[j]? = some fv →
    ops.inferType fe.env (nP + j) fv.fvarTypeD s = .ok (ty,s1) →
    ops.ensureSort fe.env (nP + j) ty s1 = .ok (u,s2) →
    checkStructFieldSortsIFA ops fe true large resSort nP fvs idxArgs j s2 = .ok (us,s3) →
    checkStructFieldSortsIFA ops fe true large resSort nP fvs idxArgs (j + 1) s =
      .ok (us ++ [u],s3) := by
  intro ops fe large resSort nP j fvs idxArgs fv ty u us s s1 s2 s3 hg hf hi hw hr
  unfold checkStructFieldSortsIFA
  simp only [hf, unwrapOr]
  refine bind_ok _ _ s s s3 fv _ rfl ?_
  refine bind_ok _ _ s s1 s3 ty _ hi ?_
  refine bind_ok _ _ s1 s2 s3 u _ hw ?_
  cases large <;> simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hg] <;>
    refine bind_ok _ _ s2 s3 s3 us _ hr ?_
  all_goals rfl
measured_theorem constructor_of_runs : ∀ (ops : CheckerOps CheckCM) (fe₀ fe : FEnv)
    (T : Name) (lps : List Name) (nP nIdx nF : Nat) (resSort : Level) (isProp large : Bool)
    (cvC cvTa : ConstantVal) (bs : List Expr) (cbody : Expr)
    (cq tq xq : List Expr × Expr) (sorts : List Level) (s s1 s2 s3 : CState),
    cvC.type.stripPis (nP + nF) = some (bs,cbody) →
    structCtorResidOk T lps nP nF nIdx cbody = true →
    openPisAtFvarsF nP cvC.type 0 = some cq →
    openPisAtFvarsF nP cvTa.type 0 = some tq →
    openPisAtFvarsF nF cq.2 nP = some xq →
    (xq.2.getAppFn == Expr.const T (lps.map .param) &&
      xq.2.getAppArgs.take nP == cq.1 && xq.2.getAppArgs.length == nP + nIdx) = true →
    (xq.1.all fun x => x.fvarTypeD.constsResolveF fe₀) = true →
    ((xq.2.getAppArgs.drop nP).all fun e => e.constsResolveF fe₀) = true →
    checkConstantValF ops fe cvC s = .ok ((),s1) →
    checkStructDomsAtFA ops fe 0 cq.1.toArray (tq.1.map Expr.fvarTypeD).toArray nP s1 = .ok ((),s2) →
    checkStructFieldSortsIFA ops fe isProp large resSort nP xq.1.toArray
      (xq.2.getAppArgs.drop nP) nF s2 = .ok (sorts,s3) →
    checkSumCtorF ops fe₀ fe T lps nP nIdx resSort isProp large cvC nF cvTa s =
      .ok ((cvC,sorts),s3) := by
  intro ops fe₀ fe T lps nP nIdx nF resSort isProp large cvC cvTa bs cbody cq tq xq sorts
    s s1 s2 s3 hs hc hco hto hxo hr hf hi hcv hd hsort
  unfold checkSumCtorF
  refine bind_ok _ _ s s1 s3 () _ hcv ?_
  simp only [hs, unwrapOr]
  refine bind_ok _ _ s1 s1 s3 (bs,cbody) _ rfl ?_
  simp only [hc, ↓reduceIte, hco, hto]
  refine bind_ok _ _ s1 s1 s3 cq _ rfl ?_
  refine bind_ok _ _ s1 s1 s3 tq _ rfl ?_
  refine bind_ok _ _ s1 s2 s3 () _ hd ?_
  simp only [hxo]
  refine bind_ok _ _ s2 s2 s3 xq _ rfl ?_
  simp only [hr, hf, hi, ↓reduceIte]
  refine bind_ok _ _ s2 s3 s3 sorts _ hsort ?_
  rfl

end CachedConstructorComposition
#audit_graph_module
