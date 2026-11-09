import AndGeneratedType
import RecursorComposition
import ConLeche.Verify.CheckerSplit
/-! Experimental #135 checkpoint. Checked generated rules at the exact rule-less recursor environment.
See [measurement and scope report](../../docs/research/relative-and-root-checkpoint.md). -/
namespace AndGeneratedRules
open AndGeneratedType AndRecursorStages ConLeche AcceptanceStages.Reference AndPositivityStages AndInstallation AndInstallationTail
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 8
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_fvar Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj CheckerReduction.depth_eq


checked_normal_form ruleEnv : FEnv := classFeR q.p.toBlockShape Ms [generated] q.rd.recCls (mkFEnv ctorEnv)
checked_normal_form rulesResult : Except CheckError (List (ConstantVal × TargetMajor × List Expr)) := classRecsRulesOk (fueledOps .verified 32) StructWalkers.plain (mkFEnv ctorEnv) ruleEnv g (classRecOf q.rd.recCls [generated]) [generated] q.rd.recCls
def out : List (ConstantVal × TargetMajor × List Expr) := rulesResult.toOption.getD []
measured_theorem rules_ok : classRecsRulesOk (fueledOps .verified 32) StructWalkers.plain (mkFEnv ctorEnv) ruleEnv g (classRecOf q.rd.recCls [generated]) [generated] q.rd.recCls = .ok out := rulesResult_eq
end AndGeneratedRules
#audit_graph_module
