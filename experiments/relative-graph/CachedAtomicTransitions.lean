import CachedTransitionComposition

/-! Experimental #417 cached variable, constant and reflexivity transitions.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedAtomicTransitions
open ConLeche ConLeche.Cached CachedTransitionComposition
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
set_option pp.deepTerms.threshold 4

def insertInfer (s : CState) (e ty : Expr) : CState :=
  { s with inferC := s.inferC.insert e ty }

measured_theorem fvar_miss : ∀ (env : Env) (f d i : Nat) (ty : Expr) (s : CState),
    i < d → s.inferC[Expr.fvar i ty]? = none →
    (coreKnotI .verified (mkFEnv env) (f + 1)).infer d (.fvar i ty) s =
      .ok (ty,insertInfer s (.fvar i ty) ty) := by
  intro env f d i ty s hd hm
  rw [coreKnotI_infer_succ]
  apply memo_miss (s' := s)
  · exact hm
  · simp only [inferBodyI, hd, ↓reduceIte]
    rfl

measured_theorem infer_hit : ∀ (env : Env) (f d : Nat) (e ty : Expr) (s : CState),
    s.inferC[e]? = some ty →
    (coreKnotI .verified (mkFEnv env) (f + 1)).infer d e s = .ok (ty,s) := by
  intro env f d e ty s hm
  rw [coreKnotI_infer_succ]
  exact memo_hit _ _ _ _ _ _ _ hm

measured_theorem whnf_hit : ∀ (env : Env) (f d : Nat) (e : Expr) (s : CState),
    s.whnfC[e]? = some e →
    (coreKnotI .verified (mkFEnv env) (f + 1)).whnf d e s = .ok (e,s) := by
  intro env f d e s hm
  rw [coreKnotI_whnf_succ]
  exact memo_hit _ _ _ _ _ _ _ hm

def insertDefeq (s : CState) (e : Expr) : CState :=
  { s with defeqC := s.defeqC.insert (e,e) true }

measured_theorem defeq_refl_miss : ∀ (env : Env) (f d : Nat) (e : Expr) (s : CState),
    s.defeqC[(e,e)]? = none →
    (coreKnotI .verified (mkFEnv env) (f + 1)).defeq d e e s =
      .ok (true,insertDefeq s e) := by
  intro env f d e s hm
  rw [coreKnotI_defeq_succ]
  unfold memoBI
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, Except.pure, Except.bind]
  rw [hm]
  dsimp only
  change (defeqBodyI .verified (coreKnotI .verified (mkFEnv env) f) (mkFEnv env) d e e >>= _) s = _
  have hb : defeqBodyI .verified (coreKnotI .verified (mkFEnv env) f) (mkFEnv env) d e e s =
      .ok (true,s) := by simp only [defeqBodyI, BEq.rfl, ↓reduceIte]; rfl
  exact bind_ok _ _ s s (insertDefeq s e) _ _ hb rfl

measured_theorem defeq_hit : ∀ (env : Env) (f d : Nat) (a b : Expr) (s : CState),
    s.defeqC[(a,b)]? = some true →
    (coreKnotI .verified (mkFEnv env) (f + 1)).defeq d a b s = .ok (true,s) := by
  intro env f d a b s hm
  rw [coreKnotI_defeq_succ]
  unfold memoBI
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, Except.pure, Except.bind]
  rw [hm]
  rfl

def insertConstType (s : CState) (n : Name) (us : List Level) (ty : Expr) : CState :=
  { s with constTyAt := s.constTyAt.insert (n,us) ty }

measured_theorem const_type_miss : ∀ (fe : FEnv) (n : Name) (us : List Level)
    (ci : ConstantInfo) (ty : Expr) (s : CState),
    s.constTyAt[(n,us)]? = none → fe.find? n = some ci →
    Expr.instLevelParams ci.toConstantVal.levelParams us ci.toConstantVal.type = ty →
    constTyAtM fe n n us s = .ok (ty,insertConstType s n us ty) := by
  intro fe n us ci ty s hm hf hi
  unfold constTyAtM
  simp only [bind, StateT.bind, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    pure, Except.pure, Except.bind]
  rw [hm]
  dsimp only
  rw [hf]
  simp only [instLevelParamsM, hi]
  rfl

measured_theorem const_body : ∀ (r : CoreFnsI) (fe : FEnv) (d : Nat) (n : Name)
    (us : List Level) (ci : ConstantInfo) (ty : Expr) (s s' : CState),
    fe.find? n = some ci → us.length = ci.toConstantVal.levelParams.length →
    constTyAtM fe n n us s = .ok (ty,s') →
    inferBodyI r fe d (.const n us) s = .ok (ty,s') := by
  intro r fe d n us ci ty s s' hf hl ht
  unfold inferBodyI
  refine bind_ok _ _ s s s' n ty rfl ?_
  rw [hf]
  simp only [hl, ↓reduceIte]
  exact ht

measured_theorem const_miss : ∀ (env : Env) (f d : Nat) (n : Name)
    (us : List Level) (ci : ConstantInfo) (ty : Expr) (s : CState),
    s.inferC[Expr.const n us]? = none → s.constTyAt[(n,us)]? = none →
    (mkFEnv env).find? n = some ci → us.length = ci.toConstantVal.levelParams.length →
    Expr.instLevelParams ci.toConstantVal.levelParams us ci.toConstantVal.type = ty →
    (coreKnotI .verified (mkFEnv env) (f + 1)).infer d (.const n us) s =
      .ok (ty,insertInfer (insertConstType s n us ty) (.const n us) ty) := by
  intro env f d n us ci ty s hm hc hf hl hi
  rw [coreKnotI_infer_succ]
  apply memo_miss (s' := insertConstType s n us ty)
  · exact hm
  · exact const_body _ _ _ _ _ _ _ _ _ hf hl (const_type_miss _ _ _ _ _ _ hc hf hi)

measured_theorem whnf_core_fvar_body : ∀ (mode : CheckMode) (r : CoreFnsI)
    (fe : FEnv) (cheap : Bool) (d : Nat) (i : Nat) (ty : Expr),
    whnfCoreBodyI mode r fe cheap d (.fvar i ty) = pure (.fvar i ty) := by
  intro mode r fe cheap d i ty
  unfold whnfCoreBodyI whnfCoreLoopFuel
  rfl

measured_theorem whnf_fvar_body : ∀ (r : CoreFnsI) (fe : FEnv) (d : Nat)
    (i : Nat) (ty : Expr) (s s' : CState),
    r.whnfCore false d (.fvar i ty) s = .ok (.fvar i ty,s') →
    whnfBodyI r fe d (.fvar i ty) s = .ok (.fvar i ty,s') := by
  intro r fe d i ty s s' h
  unfold whnfBodyI whnfLoopFuel
  change (r.whnfCore false d (.fvar i ty) >>= _) s = _
  simp only [bind, StateT.bind]
  rw [h]
  rfl

def insertCoreFvar (s : CState) (i : Nat) (ty : Expr) : CState :=
  { s with whnfCoreC := s.whnfCoreC.insert (.fvar i ty) (.fvar i ty) }

def insertWhnfFvar (s : CState) (i : Nat) (ty : Expr) : CState :=
  { s with whnfC := s.whnfC.insert (.fvar i ty) (.fvar i ty) }

measured_theorem core_fvar_whnf_miss : ∀ (env : Env) (f d : Nat) (i : Nat) (ty : Expr) (s : CState),
    s.whnfCoreC[Expr.fvar i ty]? = none →
    (coreKnotI .verified (mkFEnv env) (f + 1)).whnfCore false d (.fvar i ty) s =
      .ok (.fvar i ty, insertCoreFvar s i ty) := by
  intro env f d i ty s hm
  rw [coreKnotI_whnfCore_succ]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply memo_miss (s' := s)
  · exact hm
  · rw [whnf_core_fvar_body]
    rfl

measured_theorem whnf_fvar_whnf_miss : ∀ (env : Env) (f d : Nat) (i : Nat) (ty : Expr) (s : CState),
    s.whnfC[Expr.fvar i ty]? = none → s.whnfCoreC[Expr.fvar i ty]? = none →
    (coreKnotI .verified (mkFEnv env) ((f + 1) + 1)).whnf d (.fvar i ty) s =
      .ok (.fvar i ty, insertWhnfFvar (insertCoreFvar s i ty) i ty) := by
  intro env f d i ty s hm hc
  rw [coreKnotI_whnf_succ]
  apply memo_miss (s' := insertCoreFvar s i ty)
  · exact hm
  · apply whnf_fvar_body
    exact core_fvar_whnf_miss env f d i ty s hc


end CachedAtomicTransitions
#audit_graph_module
