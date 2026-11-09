import AndAcceptanceRoot
namespace AndInstallation
open ConLeche AcceptanceStages.Reference AndPositivityStages
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 8
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_fvar Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj CheckerReduction.depth_eq

measured_theorem opened : openPisAtFvars 2 crest 3 =
    some ([Expr.fvar 3 (.fvar 0 (.sort .zero)),Expr.fvar 4 (.fvar 1 (.sort .zero))],
      Expr.fvar 2 (.sort .zero)) := by rw [crest_eq]; cbv
measured_theorem defined : crest.allLevelParamsDefined ctx.lps = true := by
  rw [crest_eq]; change (Expr.forallE _ _).allLevelParamsDefined [] = true; cbv

theorem infer0 (env : Env) : (fueledOps .verified 32).inferType env 3
    (.fvar 0 (.sort .zero)) = .ok (.sort .zero) := rfl
theorem infer1 (env : Env) : (fueledOps .verified 32).inferType env 4
    (.fvar 1 (.sort .zero)) = .ok (.sort .zero) := rfl
theorem sort0 (env : Env) (hi : Nat) : (fueledOps .verified 32).ensureSort env hi
    (.sort .zero) = .ok .zero := by
  change ensureSort (pureFns .verified env 32) env hi (.sort .zero) = _
  unfold ensureSort
  change (whnf .verified env 32 hi (.sort .zero) >>= _) = _
  rw [whnf_sort env 30 hi .zero]
  rfl

def fvs : List Expr := [.fvar 3 (.fvar 0 (.sort .zero)),.fvar 4 (.fvar 1 (.sort .zero))]
measured_theorem fieldSorts : checkStructFieldSortsI (fueledOps .verified 32) indsResult.1
    true false .zero 3 fvs [] 2 = .ok [.zero,.zero] := by
  simp only [checkStructFieldSortsI, fvs, List.getElem?_cons_zero,
    List.getElem?_cons_succ, unwrapOr, bind, Except.bind, pure, Except.pure]
  simp only [Expr.fvarTypeD, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Nat.reduceAdd, infer1, infer0, sort0]
  rfl
measured_theorem absSorts : checkAbsCtorSortsAll (fueledOps .verified 32) indsResult.1 ctx
    ctorResult.1 rootResult.1 = .ok () := by
  change checkAbsCtorSortsAll (fueledOps .verified 32) indsResult.1 ctx
    [[(andIntroRaw.toConstantVal,2)]] [[([.ordinary,.ordinary],crest)]] = .ok ()
  simp only [checkAbsCtorSortsAll, checkAbsCtorSorts, defined, ↓reduceIte]
  rw [AndAcceptanceRoot.hi_eq,opened]
  simp only [unwrapOr, bind, Except.bind, pure, Except.pure]
  have hsort : ctx.sort = .zero := rfl
  rw [hsort]
  have heq : (Level.isEquiv .zero .zero == some true) = true := by cbv
  rw [heq]
  have hf := fieldSorts
  dsimp only [fvs] at hf
  rw [hf]
def posResult : List (List (List NestFieldKind)) × List (List Expr) × NestState :=
  (rootResult.1.map (·.map (·.1)),rootResult.1.map (·.map (·.2)),rootResult.2)

measured_theorem positivity : checkBlockPositivity (fueledOps .verified 32) indsResult.1
    indsResult.1.find? completed indsResult.2.1 ctorResult.1 = .ok posResult := by
  exact AcceptanceComposition.block_positivity (fueledOps .verified 32) indsResult.1
    indsResult.1.find? completed indsResult.2.1 ctorResult.1 ctx holes rootResult.1 rootResult.2
    context_accepted andUniformAccepted AndAcceptanceRoot.root absSorts
-- Exact outputs are named by the operational expression until a structural
-- equation supplies their success; getD is not used as an acceptance premise.
checked_normal_form classes : ClassRead × List TargetMajor := (checkBlockClasses (fueledOps .verified 32) (mkFEnv indsResult.1)
    completed.toBlockShape ctx.params ctorResult.1).toOption.getD default
measured_theorem classes_ok : checkBlockClasses (fueledOps .verified 32) (mkFEnv indsResult.1)
    completed.toBlockShape ctx.params ctorResult.1 = .ok classes := by cbv

measured_theorem seeds_ok : nestSeeds (fueledOps .verified 32) indsResult.1 ctx
    (classSeeds ctx holes classes.2) posResult.2.2 = .ok posResult.2.2 := by cbv

def passResult : BlockPass Env :=
  ⟨indsResult.1,indsResult.2.1,completed,ctorResult.1,ctorResult.2,posResult.1,posResult.2.1,
    ctx.params,classes.1,classes.2,posResult.2.2.ctorNfs⟩
measured_theorem pass_ok : checkBlockPass (fueledOps .verified 32) eqEnv parts false = .ok passResult := by
  exact AcceptanceComposition.block_pass (fueledOps .verified 32) eqEnv indsResult.1 parts false
    indsResult.2.1 indsResult.2.2 ctorResult.1 ctorResult.2 ctx holes classes.1 classes.2
    posResult.1 posResult.2.1 posResult.2.2 posResult.2.2
    inds_accepted andConstructorsAccepted context_accepted (classes_ok.trans (AcceptanceComposition.pair_ok classes)) positivity seeds_ok

def andEnv : Env := ⟨(andPin.map GraphEnvironment.storedProposition).reverse ++
  AcceptanceStages.equalityEnvironment.consts,[GraphEnvironment.andTable]⟩
end AndInstallation
#audit_graph_module

