import CachedCoreStages
import CachedTransitionComposition

/-! Experimental #417 actual cached And former transitions.
See [artifact scope](../../docs/research/relative-emitted-acceptance.md). -/
namespace CachedAndFormer
open ConLeche ConLeche.Cached CachedTransitionComposition
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
set_option pp.deepTerms.threshold 4

def s1 := CachedCoreStages.sortMemo
def s2 : CState := { s1 with whnfCoreC := s1.whnfCoreC.insert (.sort (.succ .zero)) (.sort (.succ .zero)) }
def s3 : CState := { s2 with whnfC := s2.whnfC.insert (.sort (.succ .zero)) (.sort (.succ .zero)) }

measured_theorem core_sort : ∀ (env : Env) (f d : Nat),
    (coreKnotI .verified (mkFEnv env) (f + 1)).whnfCore false d (.sort (.succ .zero)) s1 =
      .ok (.sort (.succ .zero), s2) := by
  intro env f d
  rw [coreKnotI_whnfCore_succ]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply memo_miss (s' := s1)
  · exact Std.HashMap.getElem?_empty
  · rw [whnf_core_sort_body]
    rfl

measured_theorem whnf_sort : ∀ (env : Env) (f d : Nat),
    (coreKnotI .verified (mkFEnv env) ((f + 1) + 1)).whnf d (.sort (.succ .zero)) s1 =
      .ok (.sort (.succ .zero), s3) := by
  intro env f d
  rw [coreKnotI_whnf_succ]
  apply memo_miss (s' := s2)
  · exact Std.HashMap.getElem?_empty
  · apply whnf_sort_body
    exact core_sort env f d

measured_theorem infer_hit : ∀ (env : Env) (f d : Nat),
    (coreKnotI .verified (mkFEnv env) (f + 1)).infer d (.sort .zero) s3 =
      .ok (.sort (.succ .zero), s3) := by
  intro env f d
  rw [coreKnotI_infer_succ]
  apply memo_hit
  simp [s3, s2, s1, CachedCoreStages.sortMemo]

measured_theorem whnf_hit : ∀ (env : Env) (f d : Nat),
    (coreKnotI .verified (mkFEnv env) (f + 1)).whnf d (.sort (.succ .zero)) s3 =
      .ok (.sort (.succ .zero), s3) := by
  intro env f d
  rw [coreKnotI_whnf_succ]
  apply memo_hit
  simp [s3]

def formerType : Expr := .forallE (.sort .zero) (.forallE (.sort .zero) (.sort .zero))
def formerSort : Level := .imax (.succ .zero) (.imax (.succ .zero) (.succ .zero))

measured_theorem infer_tail_of_runs : ∀ (r : CoreFnsI) (n : Nat) (s : CState),
    (∀ d, r.infer d (.sort .zero) s = .ok (.sort (.succ .zero), s)) →
    (∀ d, r.whnf d (.sort (.succ .zero)) s = .ok (.sort (.succ .zero), s)) →
    inferPisI r 0 (n + 1) (.forallE (.sort .zero) (.sort .zero)) 1
      #[.fvar 0 (.sort .zero)] [.succ .zero] s = .ok (.sort formerSort, s) := by
  intro r n s hi hw
  unfold inferPisI
  simp only [instListRevM, bind, StateT.bind, pure, StateT.pure, Except.pure, Except.bind]
  have inst_sort (vs : Array Expr) : (Expr.sort .zero).instantiateRev vs = .sort .zero := by
    unfold Expr.instantiateRev
    simp [Expr.bvarB, Expr.bvarBRaw_sort, satRange]
  simp only [inst_sort, hi]
  try simp only [Except.bind]
  simp only [hw]
  dsimp only [bind, pure, StateT.bind, StateT.pure, Except.bind, Except.pure]
  rw [infer_pis_sort]
  unfold inferPisLeafI
  simp only [instListRevM, bind, StateT.bind, pure, StateT.pure, Except.pure, Except.bind]
  simp only [inst_sort, hi]
  try simp only [Except.bind]
  simp only [hw]
  rfl

measured_theorem infer_tail : ∀ (env : Env) (f n : Nat),
    inferPisI (coreKnotI .verified (mkFEnv env) ((f + 1) + 1)) 0
      (n + 1) (.forallE (.sort .zero) (.sort .zero)) 1
      #[.fvar 0 (.sort .zero)] [.succ .zero] s3 = .ok (.sort formerSort, s3) := by
  intro env f n
  exact infer_tail_of_runs _ n s3 (infer_hit env (f + 1)) (whnf_hit env (f + 1))

measured_theorem infer_body_of_runs : ∀ (r : CoreFnsI) (fe : FEnv) (s s' s'' : CState),
    r.infer 0 (.sort .zero) s = .ok (.sort (.succ .zero), s') →
    r.whnf 0 (.sort (.succ .zero)) s' = .ok (.sort (.succ .zero), s'') →
    inferPisI r 0 peelFuel (.forallE (.sort .zero) (.sort .zero)) 1
      #[.fvar 0 (.sort .zero)] [.succ .zero] s'' = .ok (.sort formerSort, s'') →
    inferBodyI r fe 0 formerType s = .ok (.sort formerSort, s'') := by
  intro r fe s s' s'' hi hw ht
  unfold formerType inferBodyI
  refine bind_ok _ _ s s' s'' _ _ hi ?_
  refine bind_ok _ _ s' s'' s'' _ _ hw ?_
  refine bind_ok _ _ s'' s'' s'' (.fvar 0 (.sort .zero)) _ rfl ?_
  refine bind_ok _ _ s'' s'' s'' peelFuel _ rfl ?_
  exact ht

measured_theorem infer_body : ∀ (env : Env) (f : Nat),
    inferBodyI (coreKnotI .verified (mkFEnv env) ((f + 1) + 1))
      (mkFEnv env) 0 formerType {} = .ok (.sort formerSort, s3) := by
  intro env f
  apply infer_body_of_runs (s' := s1)
  · exact CachedCoreStages.sort_infer_succ env (f + 1) 0
  · exact whnf_sort env f 0
  · exact Eq.trans
      (congrArg (fun fuel => inferPisI (coreKnotI .verified (mkFEnv env) ((f + 1) + 1)) 0
        fuel (.forallE (.sort .zero) (.sort .zero)) 1
        #[.fvar 0 (.sort .zero)] [.succ .zero] s3)
        (show peelFuel = 16777215 + 1 from rfl))
      (infer_tail env f 16777215)

def s4 : CState := { s3 with inferC := s3.inferC.insert formerType (.sort formerSort) }

measured_theorem former_infer_succ : ∀ (env : Env) (f : Nat),
    (coreKnotI .verified (mkFEnv env) (((f + 1) + 1) + 1)).infer 0 formerType {} =
      .ok (.sort formerSort, s4) := by
  intro env f
  rw [coreKnotI_infer_succ]
  apply memo_miss (s' := s3)
  · exact Std.HashMap.getElem?_empty
  · exact infer_body env f

measured_theorem former_infer_fixed :
    (coreKnotI .verified (mkFEnv AcceptanceStages.equalityEnvironment) checkFuel).infer
      0 formerType {} = .ok (.sort formerSort, s4) := by
  exact Eq.trans
    (congrArg (fun fuel => (coreKnotI .verified (mkFEnv AcceptanceStages.equalityEnvironment) fuel).infer
      0 formerType {})
      (show checkFuel = ((4611686018427387901 + 1) + 1) + 1 by unfold checkFuel; rfl))
    (former_infer_succ AcceptanceStages.equalityEnvironment 4611686018427387901)

measured_theorem actual_former_type : andRaw.toConstantVal.type = formerType := by rfl

def s5 := insertWhnfSort (insertCoreSort s4 formerSort) formerSort

measured_theorem former_whnf_succ : ∀ (env : Env) (f : Nat),
    (coreKnotI .verified (mkFEnv env) ((f + 1) + 1)).whnf 0 (.sort formerSort) s4 =
      .ok (.sort formerSort,s5) := by
  intro env f
  apply whnf_sort_miss
  · simp [s4, s3, s2, s1, CachedCoreStages.sortMemo, formerSort]
  · simp [s4, s3, s2, s1, CachedCoreStages.sortMemo, formerSort]

measured_theorem former_sort_fixed :
    ensureSortI (coreKnotI .verified (mkFEnv AcceptanceStages.equalityEnvironment) checkFuel)
      0 (.sort formerSort) s4 = .ok (formerSort,s5) := by
  apply ensure_sort_of_whnf
  exact Eq.trans
    (congrArg (fun fuel => (coreKnotI .verified (mkFEnv AcceptanceStages.equalityEnvironment) fuel).whnf
      0 (.sort formerSort) s4)
      (show checkFuel = (4611686018427387902 + 1) + 1 by unfold checkFuel; rfl))
    (former_whnf_succ AcceptanceStages.equalityEnvironment 4611686018427387902)

end CachedAndFormer
#audit_graph_module
