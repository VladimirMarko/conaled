import AcceptanceStages
import CheckerReduction
namespace AndPositivityStages
open ConLeche AcceptanceStages.Reference
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option cbv.maxSteps 10000000
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj

attribute [local cbv_eval] CheckerReduction.depth_eq
def crest := (nestCrest ctx.names (ctx.lps.map Level.param) ctx.params holes
  (andIntroRaw.toConstantVal.type.instantiateLevelParams [] [])).getD (.bvar 0)
example : (match (fueledOps .verified 32).inferType indsResult.1 (ctx.hiAt 0) crest with | .ok _ => true | .error _ => false) = true := by cbv


attribute [local cbv_opaque] nestPos
@[local cbv_eval] theorem pos0 (fuel dep kb : Nat) (st : NestState) :
    nestPos (fueledOps .verified 32) indsResult.1 ctx (fuel + 1) [] dep kb (.fvar 0 (.sort .zero)) st =
      .ok (.ordinary, .fvar 0 (.sort .zero), st) := by
  rw [nestPos]
  cbv
@[local cbv_eval] theorem pos1 (fuel dep kb : Nat) (st : NestState) :
    nestPos (fueledOps .verified 32) indsResult.1 ctx (fuel + 1) [] dep kb (.fvar 1 (.sort .zero)) st =
      .ok (.ordinary, .fvar 1 (.sort .zero), st) := by
  rw [nestPos]
  cbv

theorem fields (err : CheckError) :
    nestFields (nestPos (fueledOps .verified 32) indsResult.1 ctx 1027) [] 3 err 2 0
      (.forallE (.fvar 0 (.sort .zero)) (.forallE (.fvar 1 (.sort .zero)) (.fvar 2 (.sort .zero)))) {} =
    .ok ([.ordinary, .ordinary], [.fvar 0 (.sort .zero), .fvar 1 (.sort .zero)], .fvar 2 (.sort .zero), {}) := by
  rw [nestFields]
  rw [pos0 1026 3 0 {}]
  simp only [bind, Except.bind, pure]
  change nestFields (nestPos (fueledOps .verified 32) indsResult.1 ctx 1027) [] 3 err 1 1
    (.forallE (.fvar 1 (.sort .zero)) (.fvar 2 (.sort .zero))) {} >>= _ = _
  rw [nestFields, pos1 1026 4 0 {}]
  rfl

theorem inferCrest : (fueledOps .verified 32).inferType indsResult.1 3 crest = .ok (.sort (.imax .zero (.imax .zero .zero))) := by cbv
theorem crest_ok : nestCrest ctx.names [] ctx.params holes andIntroRaw.toConstantVal.type = some crest := by cbv

def rootResult : List (List (List NestFieldKind × Expr)) × NestState :=
  ([[([.ordinary, .ordinary], crest)]],
    { ctorNfs := #[].push (nestCtorNf ctx [] 3 [] ctx.params andIntroRaw.toConstantVal
      [.fvar 0 (.sort .zero), .fvar 1 (.sort .zero)] (.fvar 2 (.sort .zero))) })
theorem crest_eq : crest = Expr.forallE (.fvar 0 (.sort .zero)) (.forallE (.fvar 1 (.sort .zero)) (.fvar 2 (.sort .zero))) := by cbv

theorem fieldsCrest (err : CheckError) :
    nestFields (nestPos (fueledOps .verified 32) indsResult.1 ctx 1027) [] 3 err 2 0 crest {} =
    .ok ([.ordinary, .ordinary], [.fvar 0 (.sort .zero), .fvar 1 (.sort .zero)], .fvar 2 (.sort .zero), {}) := by
  rw [crest_eq]
  exact fields err

theorem hguard : ((List.range 2).any fun i =>
      ([NestFieldKind.ordinary, .ordinary].getD i .ordinary != .ordinary) &&
        structUsedLater (closeTelescope [.fvar 0 (.sort .zero), .fvar 1 (.sort .zero)] 3
          (.fvar 2 (.sort .zero))) 0 i) = false := rfl
theorem hres : (nestResHead (.fvar 2 (.sort .zero)) &&
      (Expr.fvar 2 (.sort .zero)).getAppArgs.all (fun x => !x.nestOcc ctx.names ctx.nP 3)) = true := rfl
theorem hclose : closeTelescope [.fvar 0 (.sort .zero), .fvar 1 (.sort .zero)] 3 (.fvar 2 (.sort .zero)) = crest := by cbv

end AndPositivityStages
#audit_graph_module
