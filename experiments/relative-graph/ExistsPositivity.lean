import ExistsPassStages
/-! Experimental #135 checkpoint. Exact initial stages for installing the preserved Exists block after And.
See [measurement and scope report](../../docs/research/relative-and-root-checkpoint.md). -/
namespace ExistsPositivity
open ConLeche GraphEnvironment ExistsPassStages
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 8
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_fvar Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj CheckerReduction.depth_eq

checked_normal_form crest : Expr := (nestCrest ctx.names (ctx.lps.map Level.param) ctx.params holes
  (existsIntroRaw.toConstantVal.type.instantiateLevelParams existsIntroRaw.toConstantVal.levelParams (ctx.lps.map Level.param))).getD (.sort .zero)
checked_normal_form opened : Option (List Expr × Expr) := openPisAtFvars 2 crest 3
def A : Expr := .fvar 0 (.sort (Level.param BasisDSL.uN))
def P : Expr := .fvar 1 (.forallE A (.sort .zero))
def second : Expr := .app P (.fvar 3 A)
def res : Expr := .fvar 2 (.sort .zero)
attribute [local cbv_opaque] nestPos
@[local cbv_eval] theorem posA (fuel dep kb : Nat) (st : NestState) :
    nestPos (fueledOps .verified 32) indsResult.1 ctx (fuel + 1) [] dep kb A st = .ok (.ordinary,A,st) := by
  rw [nestPos]
  cbv
@[local cbv_eval] theorem posP (fuel dep kb : Nat) (st : NestState) :
    nestPos (fueledOps .verified 32) indsResult.1 ctx (fuel + 1) [] dep kb second st = .ok (.ordinary,second,st) := by
  rw [nestPos]
  cbv
checked_normal_form walkFuel : Nat := whnfWalkFuel crest
theorem fields (err : CheckError) :
    nestFields (nestPos (fueledOps .verified 32) indsResult.1 ctx (whnfWalkFuel crest)) [] 3 err 2 0 crest {} =
    .ok ([.ordinary,.ordinary],[A,second],res,{}) := by
  rw [walkFuel_eq]
  change nestFields (nestPos (fueledOps .verified 32) indsResult.1 ctx 1028) [] 3 err 2 0
    (.forallE A (.forallE (.app P (.bvar 0)) res)) {} = _
  rw [nestFields]
  rw [posA 1027 3 0 {}]
  simp only [bind, Except.bind, pure]
  change nestFields (nestPos (fueledOps .verified 32) indsResult.1 ctx 1028) [] 3 err 1 1
    (.forallE second res) {} >>= _ = _
  rw [nestFields, posP 1027 4 0 {}]
  rfl
end ExistsPositivity
#audit_graph_module
