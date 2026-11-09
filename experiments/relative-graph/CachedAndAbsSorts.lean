import CachedAndRoot
import ConLeche.Verify.CheckerF

/-! Experimental cached abstracted-field sort checks for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedAndAbsSorts
open ConLeche ConLeche.Cached AcceptanceStages.Reference
open CachedAndConstructor CachedAndCrest CachedAndPositivity CachedAtomicTransitions CachedTransitionComposition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 4

measured_theorem a_hit : ∀ f d : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) (f + 1)).infer d a c5 = .ok ((.sort .zero),c5) := by
  intro f d
  apply CachedAtomicTransitions.infer_hit
  simp only [c5, c4, c3, c2, c1, p11, p10, p9, p8, p7, p6, p5, p4, insertInfer, insertDefeq, insertConstType, insertWhnfSort, insertCoreSort, insertWhnfFvar, insertCoreFvar, CachedAndFormer.s3, CachedAndFormer.s2, CachedAndFormer.s1, CachedCoreStages.sortMemo, a, b, appAB, ctorType, crest, resultSort, ctorSort, hole, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
  simp

measured_theorem a_hit_fixed : ∀ d : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).infer d a c5 = .ok ((.sort .zero),c5) := by
  intro d
  exact Eq.trans
    (congrArg (fun fuel => (coreKnotI .verified (mkFEnv indsResult.1) fuel).infer d a c5)
      (show checkFuel = 4611686018427387903 + 1 by unfold checkFuel; rfl))
    (a_hit 4611686018427387903 d)

measured_theorem b_hit : ∀ f d : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) (f + 1)).infer d b c5 = .ok ((.sort .zero),c5) := by
  intro f d
  apply CachedAtomicTransitions.infer_hit
  simp only [c5, c4, c3, c2, c1, p11, p10, p9, p8, p7, p6, p5, p4, insertInfer, insertDefeq, insertConstType, insertWhnfSort, insertCoreSort, insertWhnfFvar, insertCoreFvar, CachedAndFormer.s3, CachedAndFormer.s2, CachedAndFormer.s1, CachedCoreStages.sortMemo, a, b, appAB, ctorType, crest, resultSort, ctorSort, hole, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
  simp

measured_theorem b_hit_fixed : ∀ d : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).infer d b c5 = .ok ((.sort .zero),c5) := by
  intro d
  exact Eq.trans
    (congrArg (fun fuel => (coreKnotI .verified (mkFEnv indsResult.1) fuel).infer d b c5)
      (show checkFuel = 4611686018427387903 + 1 by unfold checkFuel; rfl))
    (b_hit 4611686018427387903 d)

measured_theorem zero_hit : ∀ f d : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) (f + 1)).whnf d (.sort .zero) c5 = .ok ((.sort .zero),c5) := by
  intro f d
  apply CachedAtomicTransitions.whnf_hit
  simp only [c5, c4, c3, c2, c1, p11, p10, p9, p8, p7, p6, p5, p4, insertInfer, insertDefeq, insertConstType, insertWhnfSort, insertCoreSort, insertWhnfFvar, insertCoreFvar, CachedAndFormer.s3, CachedAndFormer.s2, CachedAndFormer.s1, CachedCoreStages.sortMemo, a, b, appAB, ctorType, crest, resultSort, ctorSort, hole, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
  simp

measured_theorem zero_hit_fixed : ∀ d : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).whnf d (.sort .zero) c5 = .ok ((.sort .zero),c5) := by
  intro d
  exact Eq.trans
    (congrArg (fun fuel => (coreKnotI .verified (mkFEnv indsResult.1) fuel).whnf d (.sort .zero) c5)
      (show checkFuel = 4611686018427387903 + 1 by unfold checkFuel; rfl))
    (zero_hit 4611686018427387903 d)

measured_theorem indexed_fields :
    checkStructFieldSortsIFA (sharedOpsC .verified (mkFEnv indsResult.1)) (mkFEnv indsResult.1)
      true false .zero 3 #[.fvar 3 a,.fvar 4 b] [] 2 c5 = .ok ([.zero,.zero],c5) := by
  apply CachedConstructorComposition.prop_fields_step (fv := .fvar 4 b) (ty := .sort .zero)
    (u := .zero) (us := [.zero]) (s1 := c5) (s2 := c5)
  · cbv
  · rfl
  · exact b_hit_fixed 4
  · exact ensure_sort_of_whnf _ _ _ _ _ (zero_hit_fixed 4)
  · apply CachedConstructorComposition.prop_fields_step (fv := .fvar 3 a) (ty := .sort .zero)
      (u := .zero) (us := []) (s1 := c5) (s2 := c5)
    · cbv
    · rfl
    · exact a_hit_fixed 3
    · exact ensure_sort_of_whnf _ _ _ _ _ (zero_hit_fixed 3)
    · rfl

measured_theorem fields :
    checkStructFieldSortsI (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1
      true false .zero 3 [.fvar 3 a,.fvar 4 b] [] 2 c5 = .ok ([.zero,.zero],c5) := by
  have h := indexed_fields
  rw [checkStructFieldSortsIFA_eq, checkStructFieldSortsIF_eq] at h
  exact h

measured_theorem all_sorts :
    checkAbsCtorSortsAll (sharedOpsC .verified (mkFEnv indsResult.1)) indsResult.1 ctx
      ctorResult.1 AndPositivityStages.rootResult.1 c5 = .ok ((),c5) := by
  apply CachedPositivityComposition.abs_one (fvs := [.fvar 3 a,.fvar 4 b])
    (res := hole) (us := [.zero,.zero])
  · exact AndInstallation.defined
  · exact AndInstallation.opened
  · have he : (Level.isEquiv ctx.sort .zero == some true) = true := by cbv
    rw [he]
    exact fields
end CachedAndAbsSorts
#audit_graph_module
