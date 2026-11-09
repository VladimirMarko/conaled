import AndRecursorAcceptance
import RecursorComposition
import ConLeche.Verify.CheckerSplit
/-! Experimental #135 checkpoint. Exact pure checkDecl acceptance of And, including generated records and projection table.
See [measurement and scope report](../../docs/research/relative-and-root-checkpoint.md). -/
namespace AndInstallerAcceptance
open AndRecursorAcceptance AndGeneratedRules AndGeneratedType AndRecursorStages ConLeche AcceptanceStages.Reference AndPositivityStages AndInstallation AndInstallationTail
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 8
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_fvar Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj CheckerReduction.depth_eq


checked_normal_form recEnv : Env := consBlockRecsT ctorEnv.find? q.p.toBlockShape 0 out ctorEnv
measured_theorem tables_ok : checkBlockTables (m := Except CheckError) q.p.toBlockShape (q.p.members.zip (q.ctorsAs.zip q.sortsss)) recEnv = .ok andEnv := by cbv
measured_theorem tail_ok : checkBlockTail (fueledOps .verified 32) andPin q = .ok andEnv := by
  exact RecursorComposition.tail_of_facts (fueledOps .verified 32) andPin q ctorEnv recEnv andEnv out [[]]
    idx_ok ctorEnv_eq rec_ok recEnv_eq tables_ok
measured_theorem block_ok : checkBlock (fueledOps .verified 32) eqEnv andPin parts = .ok andEnv := by
  have hp := pass_ok
  rw [q_eq] at hp
  have hraw : blockRawRec parts = false := by cbv
  apply RecursorComposition.block_of_facts (fueledOps .verified 32) eqEnv andEnv andPin parts q
  · decide +kernel
  · rw [hraw]; exact hp
  · exact tail_ok
measured_theorem accepted : checkDecl .verified (fueledOps .verified 32) [] eqEnv (.indDecl andPin 2) = .ok andEnv := by
  have hb : basisPinHit andPin = none := by cbv
  have hn : indParamsOk 2 andPin = true := by cbv
  have hp : blockParts? 2 andPin = some parts := by cbv
  simp only [checkDecl, hb, hn, hp, ↓reduceIte]
  exact block_ok
end AndInstallerAcceptance
#audit_graph_module
