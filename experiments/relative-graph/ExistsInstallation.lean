import ExistsRoot
/-! Experimental #135 checkpoint. Exact initial stages for installing the preserved Exists block after And.
See [measurement and scope report](../../docs/research/relative-and-root-checkpoint.md). -/
namespace ExistsInstallation
open ConLeche GraphEnvironment ExistsPassStages ExistsPositivity ExistsRoot AcceptanceComposition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 8
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_fvar Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj CheckerReduction.depth_eq

checked_normal_form absResult : Except CheckError Unit := checkAbsCtorSortsAll (fueledOps .verified 32) indsResult.1 ctx ctorResult.1 rootResult.1
measured_theorem absSorts : checkAbsCtorSortsAll (fueledOps .verified 32) indsResult.1 ctx ctorResult.1 rootResult.1 = .ok () := absResult_eq
def posResult : List (List (List NestFieldKind)) × List (List Expr) × NestState := (rootResult.1.map (·.map (·.1)),rootResult.1.map (·.map (·.2)),rootResult.2)
measured_theorem positivity : checkBlockPositivity (fueledOps .verified 32) indsResult.1 indsResult.1.find? completed indsResult.2.1 ctorResult.1 = .ok posResult := by
  exact block_positivity (fueledOps .verified 32) indsResult.1 indsResult.1.find? completed indsResult.2.1 ctorResult.1 ctx holes rootResult.1 rootResult.2 context_ok uniform_ok root absSorts
checked_normal_form classesResult : Except CheckError (ClassRead × List TargetMajor) := checkBlockClasses (fueledOps .verified 32) (mkFEnv indsResult.1) completed.toBlockShape ctx.params ctorResult.1
def classes := classesResult.toOption.getD default
measured_theorem classes_ok : checkBlockClasses (fueledOps .verified 32) (mkFEnv indsResult.1) completed.toBlockShape ctx.params ctorResult.1 = .ok classes := classesResult_eq
measured_theorem seeds_ok : nestSeeds (fueledOps .verified 32) indsResult.1 ctx (classSeeds ctx holes classes.2) posResult.2.2 = .ok posResult.2.2 := by cbv
def passResult : BlockPass Env := ⟨indsResult.1,indsResult.2.1,completed,ctorResult.1,ctorResult.2,posResult.1,posResult.2.1,ctx.params,classes.1,classes.2,posResult.2.2.ctorNfs⟩
measured_theorem pass_ok : checkBlockPass (fueledOps .verified 32) AndInstallation.andEnv parts false = .ok passResult := by
  exact block_pass (fueledOps .verified 32) AndInstallation.andEnv indsResult.1 parts false indsResult.2.1 indsResult.2.2 ctorResult.1 ctorResult.2 ctx holes classes.1 classes.2 posResult.1 posResult.2.1 posResult.2.2 posResult.2.2
    inds_ok ctors_ok context_ok (classes_ok.trans (pair_ok classes)) positivity seeds_ok
end ExistsInstallation
#audit_graph_module
