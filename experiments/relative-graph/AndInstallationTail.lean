import AndInstallation
/-! Experimental #135 checkpoint. Normalized pass and constructor environment, with exact index-sort and recursor-pin checks.
See [measurement and scope report](../../docs/research/relative-and-root-checkpoint.md). -/
namespace AndInstallationTail
open ConLeche AcceptanceStages.Reference AndPositivityStages AndInstallation
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 8
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_fvar Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj CheckerReduction.depth_eq

checked_normal_form q : BlockPass Env := passResult
checked_normal_form ctorEnv : Env := consBlockCtors q.p.nP q.ctorsAs q.env₁
measured_theorem idx_ok : checkBlockIdxSorts (fueledOps .verified 32) q.env₁ q.p.toBlockShape
    (q.p.members.zip q.cvTas) = .ok [[]] := by cbv

measured_theorem pins : targetRecPins (m := Except CheckError) q.p.toBlockShape andPin = .ok () := by cbv

end AndInstallationTail
#audit_graph_module
