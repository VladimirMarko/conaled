import CachedAndStages
import CachedAtomicTransitions
import CachedBinderComposition
import CachedConstructorComposition

/-! Experimental #417 cached And constructor inference.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedAndConstructor
open ConLeche ConLeche.Cached AcceptanceStages.Reference CachedAndFormer
open CachedAtomicTransitions CachedTransitionComposition CachedBinderComposition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 4
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj
def a : Expr := .fvar 0 (.sort .zero)
def b : Expr := .fvar 1 (.sort .zero)
def x : Expr := .fvar 2 a
def y : Expr := .fvar 3 b
def appAB : Expr := .app (.app (.const andName []) a) b
def rawResult : Expr := .app (.app (.const andName []) (.bvar 3)) (.bvar 2)
def body3 : Expr := .forallE (.bvar 1) rawResult
def body2 : Expr := .forallE (.bvar 1) body3
def body1 : Expr := .forallE (.sort .zero) body2
def ctorType : Expr := .forallE (.sort .zero) body1
def ctorSort : Level := .imax (.succ .zero) (.imax (.succ .zero) (.imax .zero (.imax .zero .zero)))

def p4 := insertInfer s3 a (.sort .zero)
def p5 := insertWhnfSort (insertCoreSort p4 .zero) .zero
def p6 := insertInfer p5 b (.sort .zero)
def p7 := insertInfer (insertConstType p6 andName [] formerType) (.const andName []) formerType
def p8 := insertDefeq p7 (.sort .zero)
def p9 := insertInfer p8 appAB (.sort .zero)
def p10 := insertInfer p9 ctorType (.sort ctorSort)

measured_theorem actual_type : andIntroRaw.toConstantVal.type = ctorType := by rfl
measured_theorem a_infer : ∀ (env : Env) (f d : Nat), 0 < d →
    (coreKnotI .verified (mkFEnv env) (f + 1)).infer d a s3 = .ok (.sort .zero,p4) := by
  intro env f d hd
  apply fvar_miss
  · exact hd
  · simp [s3, s2, s1, CachedCoreStages.sortMemo]

measured_theorem zero_whnf : ∀ (env : Env) (f d : Nat),
    (coreKnotI .verified (mkFEnv env) ((f + 1) + 1)).whnf d (.sort .zero) p4 =
      .ok (.sort .zero,p5) := by
  intro env f d
  apply whnf_sort_miss
  · simp [p4, s3, s2, s1, CachedCoreStages.sortMemo, insertInfer]
  · simp [p4, s3, s2, s1, CachedCoreStages.sortMemo, insertInfer]

measured_theorem b_infer : ∀ (env : Env) (f d : Nat), 1 < d →
    (coreKnotI .verified (mkFEnv env) (f + 1)).infer d b p5 = .ok (.sort .zero,p6) := by
  intro env f d hd
  apply fvar_miss
  · exact hd
  · simp [p5, p4, insertWhnfSort, insertCoreSort, insertInfer, s3, s2, s1,
      CachedCoreStages.sortMemo, a]

checked_normal_form installedAnd : ConstantInfo := (indsResult.1.find? andName).getD default
measured_theorem installed_lookup : (mkFEnv indsResult.1).find? andName = some installedAnd := by
  rw [mkFEnv_find?]
  cbv

measured_theorem and_infer : ∀ f d : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) (f + 1)).infer d (.const andName []) p6 =
      .ok (formerType,p7) := by
  intro f d
  apply const_miss (ci := installedAnd)
  · simp [p6, p5, p4, insertWhnfSort, insertCoreSort, insertInfer,
      s3, s2, s1, CachedCoreStages.sortMemo, a, b]
  · exact Std.HashMap.getElem?_empty
  · exact installed_lookup
  · cbv
  · cbv

measured_theorem a_hit : ∀ (env : Env) (f d : Nat),
    (coreKnotI .verified (mkFEnv env) (f + 1)).infer d a p7 = .ok (.sort .zero,p7) := by
  intro env f d
  apply CachedAtomicTransitions.infer_hit
  simp only [p7, p6, p5, p4, insertConstType, insertWhnfSort, insertCoreSort, insertInfer, s3, s2, s1, CachedCoreStages.sortMemo, a, b, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
  simp

measured_theorem b_hit : ∀ (env : Env) (f d : Nat),
    (coreKnotI .verified (mkFEnv env) (f + 1)).infer d b p8 = .ok (.sort .zero,p8) := by
  intro env f d
  apply CachedAtomicTransitions.infer_hit
  simp only [p8, p7, p6, p5, p4, insertDefeq, insertConstType, insertWhnfSort, insertCoreSort, insertInfer, s3, s2, s1, CachedCoreStages.sortMemo, a, b, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
  simp

measured_theorem arg_a_eq : ∀ (env : Env) (f d : Nat),
    defeqArgI (coreKnotI .verified (mkFEnv env) (f + 1)) d a (.sort .zero) (.sort .zero) p7 =
      .ok (true,p8) := by
  intro env f d
  have he : Expr.isEagerReduce a = false := by cbv
  simp only [defeqArgI, he, Bool.false_eq_true, ↓reduceIte]
  apply defeq_refl_miss
  exact Std.HashMap.getElem?_empty

measured_theorem arg_b_eq : ∀ (env : Env) (f d : Nat),
    defeqArgI (coreKnotI .verified (mkFEnv env) (f + 1)) d b (.sort .zero) (.sort .zero) p8 =
      .ok (true,p8) := by
  intro env f d
  have he : Expr.isEagerReduce b = false := by cbv
  simp only [defeqArgI, he, Bool.false_eq_true, ↓reduceIte]
  apply defeq_hit
  simp only [p8, p7, p6, p5, p4, insertDefeq, insertConstType, insertWhnfSort, insertCoreSort, insertInfer, s3, s2, s1, CachedCoreStages.sortMemo, a, b, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
  simp

measured_theorem spine : ∀ (env : Env) (f d : Nat),
    inferSpineI (coreKnotI .verified (mkFEnv env) (f + 1)) (mkFEnv env) d
      formerType #[] [a,b] p7 = .ok (.sort .zero,p8) := by
  intro env f d
  unfold formerType
  refine spine_step _ _ _ _ _ _ _ _ _ _ _ p7 p7 p7 p8 p8 (inst_sort _ _ _) (a_hit env f d)
    (arg_a_eq env f d) ?_
  refine spine_step _ _ _ _ _ _ _ _ _ _ _ p8 p8 p8 p8 p8 (inst_sort _ _ _) (b_hit env f d)
    (arg_b_eq env f d) ?_
  exact inst_sort _ _ _

measured_theorem application_body : ∀ (f d : Nat),
    inferBodyI (coreKnotI .verified (mkFEnv indsResult.1) (f + 1)) (mkFEnv indsResult.1)
      d appAB p6 = .ok (.sort .zero,p8) := by
  intro f d
  apply app_body (head := .const andName []) (ty := formerType) (args := [a,b]) (s1 := p7)
  · rfl
  · cbv
  · exact and_infer f d
  · exact spine indsResult.1 f d

measured_theorem application_infer : ∀ (f d : Nat),
    (coreKnotI .verified (mkFEnv indsResult.1) ((f + 1) + 1)).infer d appAB p6 =
      .ok (.sort .zero,p9) := by
  intro f d
  rw [coreKnotI_infer_succ]
  apply memo_miss (s' := p8)
  · simp only [p6, p5, p4, insertWhnfSort, insertCoreSort, insertInfer, s3, s2, s1, CachedCoreStages.sortMemo, a, b, appAB, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
    simp
  · exact application_body f d

measured_theorem zero_hit_p6 : ∀ (env : Env) (f d : Nat),
    (coreKnotI .verified (mkFEnv env) (f + 1)).whnf d (.sort .zero) p6 = .ok (.sort .zero,p6) := by
  intro env f d
  apply CachedAtomicTransitions.whnf_hit
  simp only [p6, p5, p4, insertWhnfSort, insertCoreSort, insertInfer, s3, s2, s1, CachedCoreStages.sortMemo, a, b, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
  simp

measured_theorem zero_hit_p9 : ∀ (env : Env) (f d : Nat),
    (coreKnotI .verified (mkFEnv env) (f + 1)).whnf d (.sort .zero) p9 = .ok (.sort .zero,p9) := by
  intro env f d
  apply CachedAtomicTransitions.whnf_hit
  simp only [p9, p8, p7, p6, p5, p4, insertDefeq, insertConstType, insertWhnfSort, insertCoreSort, insertInfer, s3, s2, s1, CachedCoreStages.sortMemo, a, b, appAB, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
  simp

measured_theorem inst_result : rawResult.instantiateRev #[a,b,x,y] = appAB := by cbv
measured_theorem inst_a : (Expr.bvar 1).instantiateRev #[a,b] = a := by cbv
measured_theorem inst_b : (Expr.bvar 1).instantiateRev #[a,b,x] = b := by cbv

measured_theorem tail4 : ∀ f n : Nat,
    inferPisI (coreKnotI .verified (mkFEnv indsResult.1) ((f + 1) + 1)) 0 n rawResult
      4 #[a,b,x,y] [.zero,.zero,.succ .zero,.succ .zero] p6 = .ok (.sort ctorSort,p9) := by
  intro f n
  rw [show inferPisI _ 0 n rawResult 4 #[a,b,x,y] [.zero,.zero,.succ .zero,.succ .zero] =
    inferPisLeafI _ 0 rawResult 4 #[a,b,x,y] [.zero,.zero,.succ .zero,.succ .zero] from
      pis_app _ _ _ _ _ _ _ _]
  apply pis_leaf (ob := appAB) (u := .zero) (s1 := p6) (s2 := p9) (s3 := p9)
  · unfold instListRevM
    rw [inst_result]
    rfl
  · exact application_infer f 4
  · exact zero_hit_p9 indsResult.1 (f + 1) 4
  · rfl

measured_theorem tail3 : ∀ f n : Nat,
    inferPisI (coreKnotI .verified (mkFEnv indsResult.1) ((f + 1) + 1)) 0 (n + 1) body3
      3 #[a,b,x] [.zero,.succ .zero,.succ .zero] p5 = .ok (.sort ctorSort,p9) := by
  intro f n
  apply pis_step (tyo := b) (u := .zero) (s1 := p5) (s2 := p6) (s3 := p6)
  · unfold instListRevM
    rw [inst_b]
    rfl
  · exact b_infer indsResult.1 (f + 1) 3 (by decide)
  · exact zero_hit_p6 indsResult.1 (f + 1) 3
  · exact tail4 f n

measured_theorem tail2 : ∀ f n : Nat,
    inferPisI (coreKnotI .verified (mkFEnv indsResult.1) ((f + 1) + 1)) 0 ((n + 1) + 1) body2
      2 #[a,b] [.succ .zero,.succ .zero] s3 = .ok (.sort ctorSort,p9) := by
  intro f n
  apply pis_step (tyo := a) (u := .zero) (s1 := s3) (s2 := p4) (s3 := p5)
  · unfold instListRevM
    rw [inst_a]
    rfl
  · exact a_infer indsResult.1 (f + 1) 2 (by decide)
  · exact zero_whnf indsResult.1 f 2
  · exact tail3 f n

measured_theorem tail1 : ∀ f n : Nat,
    inferPisI (coreKnotI .verified (mkFEnv indsResult.1) ((f + 1) + 1)) 0 (((n + 1) + 1) + 1) body1
      1 #[a] [.succ .zero] s3 = .ok (.sort ctorSort,p9) := by
  intro f n
  apply pis_step (tyo := .sort .zero) (u := .succ .zero) (s1 := s3) (s2 := s3) (s3 := s3)
  · exact inst_sort _ _ _
  · exact CachedAndFormer.infer_hit indsResult.1 (f + 1) 1
  · exact CachedAndFormer.whnf_hit indsResult.1 (f + 1) 1
  · exact tail2 f n

measured_theorem constructor_body : ∀ f : Nat,
    inferBodyI (coreKnotI .verified (mkFEnv indsResult.1) ((f + 1) + 1))
      (mkFEnv indsResult.1) 0 ctorType {} = .ok (.sort ctorSort,p9) := by
  intro f
  apply forall_body (s1 := s1) (s2 := s3) (u := .succ .zero)
  · exact CachedCoreStages.sort_infer_succ indsResult.1 (f + 1) 0
  · exact CachedAndFormer.whnf_sort indsResult.1 f 0
  · exact Eq.trans
      (congrArg (fun fuel => inferPisI (coreKnotI .verified (mkFEnv indsResult.1) ((f + 1) + 1))
        0 fuel body1 1 #[a] [.succ .zero] s3)
        (show peelFuel = ((16777213 + 1) + 1) + 1 from rfl))
      (tail1 f 16777213)

measured_theorem constructor_infer_succ : ∀ f : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) (((f + 1) + 1) + 1)).infer 0 ctorType {} =
      .ok (.sort ctorSort,p10) := by
  intro f
  rw [coreKnotI_infer_succ]
  apply memo_miss (s' := p9)
  · exact Std.HashMap.getElem?_empty
  · exact constructor_body f

measured_theorem constructor_infer_fixed :
    (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).infer 0 ctorType {} =
      .ok (.sort ctorSort,p10) := by
  exact Eq.trans
    (congrArg (fun fuel => (coreKnotI .verified (mkFEnv indsResult.1) fuel).infer 0 ctorType {})
      (show checkFuel = ((4611686018427387901 + 1) + 1) + 1 by unfold checkFuel; rfl))
    (constructor_infer_succ 4611686018427387901)

def p11 := insertWhnfSort (insertCoreSort p10 ctorSort) ctorSort

measured_theorem constructor_whnf : ∀ f : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) ((f + 1) + 1)).whnf 0 (.sort ctorSort) p10 =
      .ok (.sort ctorSort,p11) := by
  intro f
  apply whnf_sort_miss
  · simp [p10, p9, p8, p7, p6, p5, p4, insertInfer, insertDefeq, insertConstType,
      insertWhnfSort, insertCoreSort, s3, s2, s1, CachedCoreStages.sortMemo, ctorSort]
  · simp [p10, p9, p8, p7, p6, p5, p4, insertInfer, insertDefeq, insertConstType,
      insertWhnfSort, insertCoreSort, s3, s2, s1, CachedCoreStages.sortMemo, ctorSort]

measured_theorem constructor_sort_fixed :
    ensureSortI (coreKnotI .verified (mkFEnv indsResult.1) checkFuel)
      0 (.sort ctorSort) p10 = .ok (ctorSort,p11) := by
  apply ensure_sort_of_whnf
  exact Eq.trans
    (congrArg (fun fuel => (coreKnotI .verified (mkFEnv indsResult.1) fuel).whnf
      0 (.sort ctorSort) p10)
      (show checkFuel = (4611686018427387902 + 1) + 1 by unfold checkFuel; rfl))
    (constructor_whnf 4611686018427387902)

measured_theorem infer_actual :
    (sharedOpsC .verified (mkFEnv indsResult.1)).inferType indsResult.1 0
      andIntroRaw.toConstantVal.type {} = .ok (.sort ctorSort,p10) := by
  change (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).infer
    0 andIntroRaw.toConstantVal.type {} = _
  exact Eq.trans
    (congrArg (fun e => (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).infer 0 e {}) actual_type)
    constructor_infer_fixed

measured_theorem constant :
    checkConstantValF (sharedOpsC .verified (mkFEnv indsResult.1))
      (mkFEnv indsResult.1) andIntroRaw.toConstantVal {} = .ok ((),p11) := by
  apply constant_of_facts (stype := .sort ctorSort) (u := ctorSort) (s' := p10)
  · rw [mkFEnv_find?]; cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · rw [constsResolveF_eq]; cbv
  · exact infer_actual
  · exact constructor_sort_fixed

measured_theorem a_p11 : ∀ f d : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) (f + 1)).infer d a p11 = .ok ((.sort .zero),p11) := by
  intro f d
  apply CachedAtomicTransitions.infer_hit
  simp only [p11, p10, p9, p8, p7, p6, p5, p4, insertDefeq, insertConstType, insertWhnfSort, insertCoreSort, insertInfer, s3, s2, s1, CachedCoreStages.sortMemo, a, b, appAB, ctorType, ctorSort, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
  simp

measured_theorem b_p11 : ∀ f d : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) (f + 1)).infer d b p11 = .ok ((.sort .zero),p11) := by
  intro f d
  apply CachedAtomicTransitions.infer_hit
  simp only [p11, p10, p9, p8, p7, p6, p5, p4, insertDefeq, insertConstType, insertWhnfSort, insertCoreSort, insertInfer, s3, s2, s1, CachedCoreStages.sortMemo, a, b, appAB, ctorType, ctorSort, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
  simp

measured_theorem zero_p11 : ∀ f d : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) (f + 1)).whnf d (.sort .zero) p11 = .ok ((.sort .zero),p11) := by
  intro f d
  apply CachedAtomicTransitions.whnf_hit
  simp only [p11, p10, p9, p8, p7, p6, p5, p4, insertDefeq, insertConstType, insertWhnfSort, insertCoreSort, insertInfer, s3, s2, s1, CachedCoreStages.sortMemo, a, b, appAB, ctorType, ctorSort, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
  simp

measured_theorem eq_p11 : ∀ f d : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) (f + 1)).defeq d (.sort .zero) (.sort .zero) p11 = .ok (true,p11) := by
  intro f d
  apply defeq_hit
  simp only [p11, p10, p9, p8, p7, p6, p5, p4, insertDefeq, insertConstType, insertWhnfSort, insertCoreSort, insertInfer, s3, s2, s1, CachedCoreStages.sortMemo, a, b, appAB, ctorType, ctorSort, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
  simp

measured_theorem a_p11_fixed : ∀ d : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).infer d a p11 = .ok ((.sort .zero),p11) := by
  intro d
  exact Eq.trans
    (congrArg (fun fuel => (coreKnotI .verified (mkFEnv indsResult.1) fuel).infer d a p11)
      (show checkFuel = 4611686018427387903 + 1 by unfold checkFuel; rfl))
    (a_p11 4611686018427387903 d)

measured_theorem b_p11_fixed : ∀ d : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).infer d b p11 = .ok ((.sort .zero),p11) := by
  intro d
  exact Eq.trans
    (congrArg (fun fuel => (coreKnotI .verified (mkFEnv indsResult.1) fuel).infer d b p11)
      (show checkFuel = 4611686018427387903 + 1 by unfold checkFuel; rfl))
    (b_p11 4611686018427387903 d)

measured_theorem zero_p11_fixed : ∀ d : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).whnf d (.sort .zero) p11 = .ok ((.sort .zero),p11) := by
  intro d
  exact Eq.trans
    (congrArg (fun fuel => (coreKnotI .verified (mkFEnv indsResult.1) fuel).whnf d (.sort .zero) p11)
      (show checkFuel = 4611686018427387903 + 1 by unfold checkFuel; rfl))
    (zero_p11 4611686018427387903 d)

measured_theorem eq_p11_fixed : ∀ d : Nat,
    (coreKnotI .verified (mkFEnv indsResult.1) checkFuel).defeq d (.sort .zero) (.sort .zero) p11 = .ok (true,p11) := by
  intro d
  exact Eq.trans
    (congrArg (fun fuel => (coreKnotI .verified (mkFEnv indsResult.1) fuel).defeq d (.sort .zero) (.sort .zero) p11)
      (show checkFuel = 4611686018427387903 + 1 by unfold checkFuel; rfl))
    (eq_p11 4611686018427387903 d)

measured_theorem domains :
    checkStructDomsAtFA (sharedOpsC .verified (mkFEnv indsResult.1)) (mkFEnv indsResult.1)
      0 #[a,b] #[.sort .zero,.sort .zero] 2 p11 = .ok ((),p11) := by
  apply CachedConstructorComposition.domains_step (a := b) (b := .sort .zero) (s1 := p11)
  · rfl
  · rfl
  · exact eq_p11_fixed 1
  · apply CachedConstructorComposition.domains_step (a := a) (b := .sort .zero) (s1 := p11)
    · rfl
    · rfl
    · exact eq_p11_fixed 0
    · rfl

measured_theorem fields : ∀ large : Bool,
    checkStructFieldSortsIFA (sharedOpsC .verified (mkFEnv indsResult.1)) (mkFEnv indsResult.1)
      true large .zero 2 #[x,y] [] 2 p11 = .ok ([.zero,.zero],p11) := by
  intro large
  apply CachedConstructorComposition.prop_fields_step (fv := y) (ty := .sort .zero)
    (u := .zero) (us := [.zero]) (s1 := p11) (s2 := p11)
  · cbv
  · rfl
  · exact b_p11_fixed 3
  · exact ensure_sort_of_whnf _ _ _ _ _ (zero_p11_fixed 3)
  · apply CachedConstructorComposition.prop_fields_step (fv := x) (ty := .sort .zero)
      (u := .zero) (us := []) (s1 := p11) (s2 := p11)
    · cbv
    · rfl
    · exact a_p11_fixed 2
    · exact ensure_sort_of_whnf _ _ _ _ _ (zero_p11_fixed 2)
    · rfl

measured_theorem constructor : ∀ large : Bool,
    checkSumCtorF (sharedOpsC .verified (mkFEnv indsResult.1))
      (mkFEnv indsResult.1) (mkFEnv indsResult.1) andName [] 2 0 .zero true large
      andIntroRaw.toConstantVal 2 andRaw.toConstantVal {} =
        .ok ((andIntroRaw.toConstantVal,[.zero,.zero]),p11) := by
  intro large
  apply CachedConstructorComposition.constructor_of_runs
    (bs := [.sort .zero,.sort .zero,.bvar 1,.bvar 1]) (cbody := rawResult)
    (cq := ([a,b],.forallE a (.forallE b appAB))) (tq := ([a,b],.sort .zero))
    (xq := ([x,y],appAB)) (s1 := p11) (s2 := p11)
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · exact constant
  · exact domains
  · exact fields large

end CachedAndConstructor
#audit_graph_module
