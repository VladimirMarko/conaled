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
    pure, StateT.pure, Except.pure, Except.bind]
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

end CachedAtomicTransitions
#audit_graph_module
