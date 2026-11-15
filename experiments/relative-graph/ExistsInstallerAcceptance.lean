import ExistsRecursorAcceptance
import RecursorComposition
import ConLeche.Verify.CheckerSplit
/-! Experimental #135 checkpoint. Exact pure checkDecl acceptance of Exists, including generated records and projection table.
See [measurement and scope report](../../docs/research/relative-and-root-checkpoint.md). -/
namespace ExistsInstallerAcceptance
open GraphEnvironment ExistsRecursorAcceptance ExistsGeneratedRules ExistsGeneratedType ExistsRecursorStages ConLeche ExistsPassStages ExistsPositivity ExistsInstallation ExistsInstallationTail
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 8
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_fvar Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj CheckerReduction.depth_eq


checked_normal_form recEnv : Env := consBlockRecsT ctorEnv.find? q.p.toBlockShape 0 out ctorEnv
measured_theorem tables_ok : checkBlockTables (m := Except CheckError) q.p.toBlockShape (q.p.members.zip (q.ctorsAs.zip q.sortsss)) recEnv = .ok GraphEnvironment.environment := by cbv
measured_theorem tail_ok : checkBlockTail (fueledOps .verified 32) existsBlock q = .ok GraphEnvironment.environment := by
  exact RecursorComposition.tail_of_facts (fueledOps .verified 32) existsBlock q ctorEnv recEnv GraphEnvironment.environment out [[]]
    idx_ok ctorEnv_eq rec_ok recEnv_eq tables_ok
measured_theorem block_ok : checkBlock (fueledOps .verified 32) AndInstallation.andEnv existsBlock parts = .ok GraphEnvironment.environment := by
  have hp := pass_ok
  rw [q_eq] at hp
  have hraw : blockRawRec parts = false := by cbv
  apply RecursorComposition.block_of_facts (fueledOps .verified 32) AndInstallation.andEnv GraphEnvironment.environment existsBlock parts q
  · decide +kernel
  · rw [hraw]; exact hp
  · exact tail_ok
measured_theorem accepted : checkDecl .verified (fueledOps .verified 32) [] AndInstallation.andEnv (.indDecl existsBlock 2) = .ok GraphEnvironment.environment := by
  have hb : basisPinHit existsBlock = none := by cbv
  have hn : indParamsOk 2 existsBlock = true := by cbv
  have hp : blockParts? 2 existsBlock = some parts := by cbv
  simp only [checkDecl, hb, hn, hp, ↓reduceIte]
  exact block_ok
end ExistsInstallerAcceptance
#audit_graph_module
