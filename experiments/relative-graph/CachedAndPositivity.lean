import CachedAndCrest
import CachedPositivityComposition

/-! Experimental cached And positivity walk for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedAndPositivity
open ConLeche ConLeche.Cached AcceptanceStages.Reference
open CachedAndConstructor CachedAndCrest CachedAtomicTransitions CachedTransitionComposition
open CachedPositivityComposition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 4

def c4 := insertWhnfFvar (insertCoreFvar c3 0 (.sort .zero)) 0 (.sort .zero)
def c5 := insertWhnfFvar (insertCoreFvar c4 1 (.sort .zero)) 1 (.sort .zero)

measured_theorem a_whnf : ∀ f : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) ((f + 1) + 1)).whnf 3 a c3 = .ok (a,c4) := by
  intro f
  apply whnf_fvar_whnf_miss
  all_goals simp [c3, c2, c1, p11, p10, p9, p8, p7, p6, p5, p4, insertInfer, insertDefeq,
    insertConstType, insertWhnfSort, insertCoreSort, CachedAndFormer.s3, CachedAndFormer.s2,
    CachedAndFormer.s1, CachedCoreStages.sortMemo, a]

measured_theorem b_whnf : ∀ f : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) ((f + 1) + 1)).whnf 4 b c4 = .ok (b,c5) := by
  intro f
  apply whnf_fvar_whnf_miss
  all_goals simp [c4, c3, c2, c1, p11, p10, p9, p8, p7, p6, p5, p4, insertInfer, insertDefeq,
    insertConstType, insertWhnfSort, insertCoreSort, insertWhnfFvar, insertCoreFvar,
    CachedAndFormer.s3, CachedAndFormer.s2, CachedAndFormer.s1, CachedCoreStages.sortMemo, b]

measured_theorem a_whnf_fixed :
    (sharedOpsC .verified (mkFEnv indsResult.1)).whnf indsResult.1 3 a c3 = .ok (a,c4) := by
  exact Eq.trans
    (congrArg (fun fuel => (coreKnotI .verified (mkFEnv indsResult.1) fuel).whnf 3 a c3)
      (show checkFuel = (4611686018427387902 + 1) + 1 by unfold checkFuel; rfl))
    (a_whnf 4611686018427387902)

measured_theorem b_whnf_fixed :
    (sharedOpsC .verified (mkFEnv indsResult.1)).whnf indsResult.1 4 b c4 = .ok (b,c5) := by
  exact Eq.trans
    (congrArg (fun fuel => (coreKnotI .verified (mkFEnv indsResult.1) fuel).whnf 4 b c4)
      (show checkFuel = (4611686018427387902 + 1) + 1 by unfold checkFuel; rfl))
    (b_whnf 4611686018427387902)

measured_theorem pos_a : ∀ f : Nat,
    nestPos (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1 ctx (f + 1)
      [] 3 0 a {} c3 = .ok ((.ordinary,a,{}),c4) := by
  intro f
  apply ordinary
  · rfl
  · exact a_whnf_fixed

measured_theorem pos_b : ∀ f : Nat,
    nestPos (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1 ctx (f + 1)
      [] 4 0 b {} c4 = .ok ((.ordinary,b,{}),c5) := by
  intro f
  apply ordinary
  · rfl
  · exact b_whnf_fixed

measured_theorem inst_tail : (Expr.forallE b hole).instantiate1 (.fvar 3 a) = .forallE b hole := by cbv
measured_theorem inst_hole : hole.instantiate1 (.fvar 4 b) = hole := by cbv

measured_theorem fields : ∀ err : CheckError,
    nestFields (nestPos (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1 ctx 1027)
      [] 3 err 2 0 crest {} c3 = .ok (([.ordinary,.ordinary],[a,b],hole,{}),c5) := by
  intro err
  apply fields_step (st1 := {}) (s1 := c4)
  · exact pos_a 1026
  · rw [inst_tail]
    apply fields_step (st1 := {}) (s1 := c5)
    · exact pos_b 1026
    · rw [inst_hole]
      rfl
end CachedAndPositivity
#audit_graph_module
