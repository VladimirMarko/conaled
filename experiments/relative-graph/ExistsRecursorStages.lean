import ExistsRecursorType
import ConLeche.Verify.CheckerSplit
/-! Experimental #135 checkpoint. Exact class normalization, constructor, former-type and prefix stages of the Exists recursor generator.
See [measurement and scope report](../../docs/research/relative-and-root-checkpoint.md). -/
namespace ExistsRecursorStages
open GraphEnvironment ConLeche ExistsPassStages ExistsPositivity ExistsInstallation ExistsInstallationTail
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 8
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_fvar Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj CheckerReduction.depth_eq


checked_normal_form nfResult : Except CheckError (List TargetMajor) := classesNfs (fueledOps .verified 32) ctorEnv q.p.toBlockShape (q.cvTas.map (·.type)) q.tbl.toList q.cls
def Ms : List TargetMajor := nfResult.toOption.getD []
measured_theorem nfs_ok : classesNfs (fueledOps .verified 32) ctorEnv q.p.toBlockShape (q.cvTas.map (·.type)) q.tbl.toList q.cls = .ok Ms := nfResult_eq
checked_normal_form ctorResult : Except CheckError (List (List ClassCtor)) := classesCtors (fueledOps .verified 32) ctorEnv q.p.toBlockShape (q.cvTas.map (·.type)) q.rd Ms 0 Ms
def ctors : List (List ClassCtor) := ctorResult.toOption.getD []
measured_theorem ctors_ok : classesCtors (fueledOps .verified 32) ctorEnv q.p.toBlockShape (q.cvTas.map (·.type)) q.rd Ms 0 Ms = .ok ctors := ctorResult_eq
checked_normal_form formerTys : List Expr := (Ms.mapM (classFormerTy (m := Except CheckError) (mkFEnv ctorEnv) q.cvTas)).toOption.getD []
measured_theorem formers_ok : Ms.mapM (classFormerTy (m := Except CheckError) (mkFEnv ctorEnv) q.cvTas) = .ok formerTys := by cbv
def g0 : ClassGen := ⟨q.p.nP, q.params, Ms, formerTys, q.rd.slots, ctors, structElimLevel q.p.elim q.p.large, []⟩
checked_normal_form pre : List Expr := g0.prefixBinders.getD []
measured_theorem prefix_ok : g0.prefixBinders = some pre := by cbv
def g : ClassGen := {g0 with pre := pre}
end ExistsRecursorStages
#audit_graph_module
