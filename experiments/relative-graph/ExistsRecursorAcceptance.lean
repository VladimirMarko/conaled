import ExistsGeneratedRules
import RecursorComposition
import ConLeche.Verify.CheckerSplit
/-! Experimental #135 checkpoint. Symbolic composition of every GenRec stage into actual checkBlockRec success.
See [measurement and scope report](../../docs/research/relative-and-root-checkpoint.md). -/
namespace ExistsRecursorAcceptance
open GraphEnvironment ExistsGeneratedRules ExistsGeneratedType ExistsRecursorStages ConLeche ExistsPassStages ExistsPositivity ExistsInstallation ExistsInstallationTail
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 8
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_fvar Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj CheckerReduction.depth_eq


measured_theorem rec_ok : checkBlockRec (fueledOps .verified 32) ctorEnv q.p (blockNestedBit q.p.toBlockShape q.kinds) q.params q.tbl.toList q.rd q.cls existsBlock q.cvTas = .ok out := by
  have hk : 0 < q.p.k := by decide +kernel
  have hlarge : (q.p.large && !blockLargeElimAllowed q.p.toBlockShape (blockNestedBit q.p.toBlockShape q.kinds || q.cls.any (·.member.isNone))) = false := by cbv
  have hminor : ((q.rd.slots.filter ClassSlot.isMinor).length == (ctors.map List.length).sum) = true := by cbv
  have hr := rules_ok
  rw [← ruleEnv_eq] at hr
  exact RecursorComposition.genRec_of_facts (fueledOps .verified 32) ctorEnv q.p.toBlockShape
    (blockNestedBit q.p.toBlockShape q.kinds) q.params q.tbl.toList q.rd q.cls Ms q.cvTas
    existsBlock [ExistsRecursorType.recCv] ctors formerTys pre [generated] out
    pins ExistsRecursorType.stream_ok hk hlarge nfs_ok ctors_ok hminor formers_ok prefix_ok types_ok hr
end ExistsRecursorAcceptance
#audit_graph_module
