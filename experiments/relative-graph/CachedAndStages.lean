import CachedAndFormer
import ConLeche.Verify.Cached.BlockRunC

/-! Experimental #417 cached And former installation.
See [artifact scope](../../docs/research/relative-emitted-acceptance.md). -/
namespace CachedAndStages
open ConLeche ConLeche.Cached AcceptanceStages.Reference CachedAndFormer CachedTransitionComposition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 4
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj

measured_theorem infer_actual :
    (sharedOpsC .verified (mkFEnv AcceptanceStages.equalityEnvironment)).inferType
      AcceptanceStages.equalityEnvironment 0 andRaw.toConstantVal.type {} =
      .ok (.sort formerSort,s4) := by
  change (coreKnotI .verified (mkFEnv AcceptanceStages.equalityEnvironment) checkFuel).infer
    0 andRaw.toConstantVal.type {} = _
  exact Eq.trans
    (congrArg (fun e => (coreKnotI .verified (mkFEnv AcceptanceStages.equalityEnvironment) checkFuel).infer
      0 e {}) actual_former_type)
    former_infer_fixed

measured_theorem constant :
    checkConstantValF (sharedOpsC .verified (mkFEnv AcceptanceStages.equalityEnvironment))
      (mkFEnv AcceptanceStages.equalityEnvironment) andRaw.toConstantVal {} = .ok ((),s5) := by
  apply constant_of_facts (stype := .sort formerSort) (u := formerSort) (s' := s4)
  · rw [mkFEnv_find?]; cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · rw [constsResolveF_eq]; cbv
  · exact infer_actual
  · exact former_sort_fixed

checked_normal_form member : MemberShape := parts.members.headD default
measured_theorem member_cv : member.cvT = andRaw.toConstantVal := by cbv
measured_theorem members : parts.members = [member] := by cbv

measured_theorem tele :
    checkBlockTeleF (sharedOpsC .verified (mkFEnv AcceptanceStages.equalityEnvironment))
      (mkFEnv AcceptanceStages.equalityEnvironment) parts.nP member {} =
      .ok ((member.cvT,.zero),s5) := by
  apply tele_of_syntactic (bs := [.sort .zero,.sort .zero])
  · cbv
  · exact Eq.trans
      (congrArg (fun cv => checkConstantValF
        (sharedOpsC .verified (mkFEnv AcceptanceStages.equalityEnvironment))
        (mkFEnv AcceptanceStages.equalityEnvironment) cv {}) member_cv)
      constant

measured_theorem former :
    checkBlockIndsF (sharedOpsC .verified (mkFEnv AcceptanceStages.equalityEnvironment))
      (mkFEnv AcceptanceStages.equalityEnvironment) parts false {} =
      .ok ((mkFEnv indsResult.1, indsResult.2),s5) := by
  have h := inds_singleton _ _ parts false member .zero ({} : CState) s5 members tele
  rw [member_cv, consBlockIndsF_mkFEnv] at h
  exact h

end CachedAndStages
#audit_graph_module
