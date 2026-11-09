import CachedAndPassStages

/-! Experimental cached And positivity-crest inference for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedAndCrest
open ConLeche ConLeche.Cached AcceptanceStages.Reference
open CachedAndConstructor CachedAtomicTransitions CachedTransitionComposition CachedBinderComposition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 4

def hole : Expr := .fvar 2 (.sort .zero)
def crest : Expr := .forallE a (.forallE b hole)
def resultSort : Level := .imax .zero (.imax .zero .zero)
def c1 := insertInfer p11 hole (.sort .zero)
def c2 := insertInfer c1 crest (.sort resultSort)
def c3 := insertWhnfSort (insertCoreSort c2 resultSort) resultSort

measured_theorem hole_infer : ∀ f : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) (f + 1)).infer 5 hole p11 = .ok (.sort .zero,c1) := by
  intro f
  apply fvar_miss
  · decide
  · simp only [p11, p10, p9, p8, p7, p6, p5, p4, insertDefeq, insertConstType, insertWhnfSort,
      insertCoreSort, insertInfer, CachedAndFormer.s3, CachedAndFormer.s2, CachedAndFormer.s1,
      CachedCoreStages.sortMemo, a, b, appAB, ctorType, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem?_empty]
    simp

measured_theorem zero_c1 : ∀ f : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) (f + 1)).whnf 5 (.sort .zero) c1 = .ok (.sort .zero,c1) := by
  intro f
  apply CachedAtomicTransitions.whnf_hit
  simp only [c1, p11, p10, p9, p8, p7, p6, p5, p4, insertDefeq, insertConstType, insertWhnfSort,
      insertCoreSort, insertInfer, CachedAndFormer.s3, CachedAndFormer.s2, CachedAndFormer.s1,
      CachedCoreStages.sortMemo, ctorSort, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem?_empty]
  simp

measured_theorem leaf : ∀ f n : Nat,
    inferPisI (coreKnotI .verified (mkFEnv indsResult.1) (f + 1)) 3 n hole 2
      #[.fvar 3 a,.fvar 4 b] [.zero,.zero] p11 = .ok (.sort resultSort,c1) := by
  intro f n
  rw [show inferPisI _ 3 n hole 2 #[.fvar 3 a,.fvar 4 b] [.zero,.zero] =
    inferPisLeafI _ 3 hole 2 #[.fvar 3 a,.fvar 4 b] [.zero,.zero] from pis_fvar _ _ _ _ _ _ _ _]
  apply pis_leaf (ob := hole) (u := .zero) (s1 := p11) (s2 := c1) (s3 := c1)
  · exact inst_fvar _ _ _ _
  · exact hole_infer f
  · exact zero_c1 f
  · rfl

measured_theorem tail : ∀ f n : Nat,
    inferPisI (coreKnotI .verified (mkFEnv indsResult.1) (f + 1)) 3 (n + 1)
      (.forallE b hole) 1 #[.fvar 3 a] [.zero] p11 = .ok (.sort resultSort,c1) := by
  intro f n
  apply pis_step (tyo := b) (u := .zero) (s1 := p11) (s2 := p11) (s3 := p11)
  · exact inst_fvar _ _ _ _
  · exact b_p11 f 4
  · exact zero_p11 f 4
  · exact leaf f n

measured_theorem body : ∀ f : Nat,
    inferBodyI (coreKnotI .verified (mkFEnv indsResult.1) (f + 1)) (mkFEnv indsResult.1)
      3 crest p11 = .ok (.sort resultSort,c1) := by
  intro f
  apply forall_body (u := .zero) (s1 := p11) (s2 := p11)
  · exact a_p11 f 3
  · exact zero_p11 f 3
  · exact Eq.trans
      (congrArg (fun fuel => inferPisI (coreKnotI .verified (mkFEnv indsResult.1) (f + 1))
        3 fuel (.forallE b hole) 1 #[.fvar 3 a] [.zero] p11)
        (show peelFuel = 16777215 + 1 from rfl))
      (tail f 16777215)

measured_theorem infer_succ : ∀ f : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) ((f + 1) + 1)).infer 3 crest p11 =
      .ok (.sort resultSort,c2) := by
  intro f
  rw [coreKnotI_infer_succ]
  apply memo_miss (s' := c1)
  · simp only [p11, p10, p9, p8, p7, p6, p5, p4, insertDefeq, insertConstType, insertWhnfSort,
      insertCoreSort, insertInfer, CachedAndFormer.s3, CachedAndFormer.s2, CachedAndFormer.s1,
      CachedCoreStages.sortMemo, a, b, appAB, ctorType, body1, crest, hole,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
    simp
  · exact body f

measured_theorem infer_fixed :
    (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).infer 3 crest p11 = .ok (.sort resultSort,c2) := by
  exact Eq.trans
    (congrArg (fun fuel => (coreKnotI .verified (mkFEnv indsResult.1) fuel).infer 3 crest p11)
      (show checkFuel = (4611686018427387902 + 1) + 1 by unfold checkFuel; rfl))
    (infer_succ 4611686018427387902)

measured_theorem whnf_succ : ∀ f : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) ((f + 1) + 1)).whnf 3 (.sort resultSort) c2 =
      .ok (.sort resultSort,c3) := by
  intro f
  apply whnf_sort_miss
  · simp [c2, c1, p11, p10, p9, p8, p7, p6, p5, p4, insertInfer, insertDefeq, insertConstType,
      insertWhnfSort, insertCoreSort, CachedAndFormer.s3, CachedAndFormer.s2,
      CachedAndFormer.s1, CachedCoreStages.sortMemo, resultSort, ctorSort]
  · simp [c2, c1, p11, p10, p9, p8, p7, p6, p5, p4, insertInfer, insertDefeq, insertConstType,
      insertWhnfSort, insertCoreSort, CachedAndFormer.s3, CachedAndFormer.s2,
      CachedAndFormer.s1, CachedCoreStages.sortMemo, resultSort, ctorSort]

measured_theorem sort_fixed :
    ensureSortI (coreKnotI .verified (mkFEnv indsResult.1) checkFuel) 3 (.sort resultSort) c2 =
      .ok (resultSort,c3) := by
  apply ensure_sort_of_whnf
  exact Eq.trans
    (congrArg (fun fuel => (coreKnotI .verified (mkFEnv indsResult.1) fuel).whnf 3 (.sort resultSort) c2)
      (show checkFuel = (4611686018427387902 + 1) + 1 by unfold checkFuel; rfl))
    (whnf_succ 4611686018427387902)

end CachedAndCrest
#audit_graph_module
