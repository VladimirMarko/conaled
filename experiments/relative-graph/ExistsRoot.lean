import ExistsPositivity
/-! Experimental #135 checkpoint. Exact initial stages for installing the preserved Exists block after And.
See [measurement and scope report](../../docs/research/relative-and-root-checkpoint.md). -/
namespace ExistsRoot
open ConLeche GraphEnvironment ExistsPassStages ExistsPositivity AcceptanceComposition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 8
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_fvar Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj CheckerReduction.depth_eq

checked_normal_form inferred : Except CheckError Expr := (fueledOps .verified 32).inferType indsResult.1 3 crest
checked_normal_form u : Level := match inferred with | .ok (.sort u) => u | _ => .zero
measured_theorem infer_ok : (fueledOps .verified 32).inferType indsResult.1 3 crest = .ok (.sort u) := inferred_eq
measured_theorem sort_ok : (fueledOps .verified 32).ensureSort indsResult.1 3 (.sort u) = .ok u := by
  change ensureSortCore .verified indsResult.1 32 3 (.sort u) = .ok u
  rw [ensureSortCore_eq, whnf_sort indsResult.1 30 3 u]
  rfl
measured_theorem crest_ok : nestCrest ctx.names (ctx.lps.map Level.param) ctx.params holes
  (existsIntroRaw.toConstantVal.type.instantiateLevelParams existsIntroRaw.toConstantVal.levelParams (ctx.lps.map Level.param)) = some crest := by cbv
measured_theorem close_ok : closeTelescope [A,second] 3 res = crest := by cbv
def post : NestState := { ctorNfs := #[].push (nestCtorNf ctx [] 3 (ctx.lps.map Level.param) ctx.params existsIntroRaw.toConstantVal [A,second] res) }
def rootResult : List (List (List NestFieldKind × Expr)) × NestState := ([[([.ordinary,.ordinary],crest)]],post)
measured_theorem constructors : nestCtors ctx (fueledOps .verified 32) indsResult.1
    (fun crest => nestPos (fueledOps .verified 32) indsResult.1 ctx (whnfWalkFuel crest)) []
    (ctx.hiAt 0) (ctx.lps.map Level.param) ctx.params ctx.names holes [(existsIntroRaw.toConstantVal,2)] {} = .ok ([([.ordinary,.ordinary],crest)],post) := by
  have hi : ctx.hiAt 0 = 3 := by cbv
  rw [hi]
  have h := ctors_one ctx (fueledOps .verified 32) indsResult.1
    (fun crest => nestPos (fueledOps .verified 32) indsResult.1 ctx (whnfWalkFuel crest)) []
    3 (ctx.lps.map Level.param) ctx.params ctx.names holes existsIntroRaw.toConstantVal 2 {} {} crest (.sort u) u
    [.ordinary,.ordinary] [A,second] res (by cbv) crest_ok infer_ok sort_ok fields (by cbv) (by cbv)
  rw [close_ok] at h
  exact h
measured_theorem root : nestRoot (fueledOps .verified 32) indsResult.1 ctx holes ctorResult.1 {} = .ok rootResult := by
  have hc : ctorResult.1 = [[(existsIntroRaw.toConstantVal,2)]] := by cbv
  rw [hc]
  exact root_one (fueledOps .verified 32) indsResult.1 ctx holes [(existsIntroRaw.toConstantVal,2)] {} post [([.ordinary,.ordinary],crest)] constructors
end ExistsRoot
#audit_graph_module
