import AndInstallerAcceptance
/-! Experimental #135 checkpoint. Exact initial stages for installing the preserved Exists block after And.
See [measurement and scope report](../../docs/research/relative-and-root-checkpoint.md). -/
namespace ExistsPassStages
open ConLeche GraphEnvironment AndInstallation
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 8
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_fvar Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj CheckerReduction.depth_eq

checked_normal_form parts : BlockParts := (blockParts? 2 existsBlock).getD default
checked_normal_form inds : Except CheckError (Env × List ConstantVal × BlockShape) := checkBlockInds (fueledOps .verified 32) andEnv parts false
def indsResult : Env × List ConstantVal × BlockShape := inds.toOption.getD default
measured_theorem inds_ok : checkBlockInds (fueledOps .verified 32) andEnv parts false = .ok indsResult := inds_eq
checked_normal_form completed : BlockParts := parts.complete indsResult.2.2
checked_normal_form ctorOut : Except CheckError (List (List (ConstantVal × Nat)) × List (List (List Level))) := checkBlockCtors (fueledOps .verified 32) indsResult.1 indsResult.1 completed.toBlockShape (completed.members.zip indsResult.2.1)
def ctorResult := ctorOut.toOption.getD default
measured_theorem ctors_ok : checkBlockCtors (fueledOps .verified 32) indsResult.1 indsResult.1 completed.toBlockShape (completed.members.zip indsResult.2.1) = .ok ctorResult := ctorOut_eq
checked_normal_form context : Except CheckError (NestCtx × List Expr) := blockNestCtx (m := Except CheckError) completed.toBlockShape indsResult.2.1 indsResult.1.find?
def ctx := (context.toOption.map Prod.fst).getD (completed.toBlockShape.nestCtx [] indsResult.1.find?)
def holes := (context.toOption.map Prod.snd).getD []
measured_theorem context_ok : blockNestCtx (m := Except CheckError) completed.toBlockShape indsResult.2.1 indsResult.1.find? = .ok (ctx,holes) := context_eq
measured_theorem uniform_ok : nestUniform (m := Except CheckError) ctx ctorResult.1 = .ok () := by cbv
end ExistsPassStages
#audit_graph_module
