import NativeHelper2
import EmittedEnvironment
import ConLeche.Verify.CheckerSplit
/-! Experimental #135 checkpoint. Fixed-fuel acceptance of native helper 3 in its actual predecessor environment.
See [measurement and scope report](../../docs/research/relative-emitted-acceptance.md). -/
namespace NativeHelper3
open ConLeche
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 8
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_fvar Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj CheckerReduction.depth_eq


def before := NativeHelper2.after
checked_normal_form decl : Declaration := EmittedEnvironment.helpers.getD 3 (.basisDecl .eqK)
checked_normal_form cv : ConstantVal := match decl with | .thmDecl c _ => c | .defnDecl c _ _ => c | _ => default
checked_normal_form value : Expr := match decl with | .thmDecl _ v => v | .defnDecl _ v _ => v | _ => .sort .zero
checked_normal_form inferred : Except CheckError Expr := inferTypeCore .verified before 32 0 cv.type
checked_normal_form u : Level := match inferred with | .ok (.sort u) => u | _ => .zero
measured_theorem infer_ok : inferTypeCore .verified before 32 0 cv.type = .ok (.sort u) := inferred_eq
measured_theorem sort_ok : ensureSortCore .verified before 32 0 (.sort u) = .ok u := by
  rw [ensureSortCore_eq, whnf_sort before 30 0 u]
  rfl
checked_normal_form valInferred : Except CheckError Expr := inferTypeCore .verified before 32 0 value
def vtype := valInferred.toOption.getD (.sort .zero)
measured_theorem valInfer_ok : inferTypeCore .verified before 32 0 value = .ok vtype := valInferred_eq
checked_normal_form equalResult : Except CheckError Bool := isDefEqCore .verified before 32 0 vtype cv.type
measured_theorem equal_ok : isDefEqCore .verified before 32 0 vtype cv.type = .ok true := equalResult_eq
measured_theorem constant_ok : checkConstantVal (fueledOps .verified 32) before cv = .ok () := by
  exact checkConstantVal_of_facts (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) infer_ok sort_ok
def after : Env := ⟨.thmInfo cv :: before.consts,before.tables⟩
measured_theorem value_ok : checkThmVal (fueledOps .verified 32) before cv value = .ok after := by
  exact checkThmVal_of_facts infer_ok sort_ok (by cbv) (by cbv) (by cbv) (by cbv) (by cbv) valInfer_ok equal_ok
measured_theorem accepted : checkDecl .verified (fueledOps .verified 32) [] before decl = .ok after := by
  have hd : decl = .thmDecl cv value := by cbv
  rw [hd]
  simp only [checkDecl, constant_ok, value_ok, bind, Except.bind]
end NativeHelper3
#audit_graph_module
