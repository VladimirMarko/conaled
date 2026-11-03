import ArtifactAudit
import GraphEnvironment
import ConLeche.Model.Fold

/-! Kernel-checked installation stages. Indexed installation is rewritten with
its proved list implementation before reducing the bounded records. -/
namespace AcceptanceStages
open ConLeche ConLeche.Cached

def equalityEnvironment : Env := ⟨[eqRecA, eqReflA, eqA], []⟩

theorem equalityPin : basisPinHit eqBasis = some .eqK := by
  simp [basisPinHit, BasisKind.decls, canonEqList]

theorem equalityGuard : andPinOk (.indDecl eqBasis 2) = true := by
  decide +kernel

theorem equalityInstall :
    installDeclStep .verified [] (0, mkFEnv Env.empty, #[]) (.indDecl eqBasis 2) =
      .ok (1, mkFEnv equalityEnvironment, #[]) := by
  simp only [installDeclStep, equalityGuard, ↓reduceIte, installStepC,
    checkDeclStepC, checkDeclC, equalityPin, checkBasisDeclC, reduceCtorEq,
    installBasisFoldF_pushC]
  rfl

theorem equalityAccepted :
    checkDecls .verified [] #[.indDecl eqBasis 2] = .ok equalityEnvironment := by
  simp only [checkDecls, ← Array.foldlM_toList, List.foldlM_cons, List.foldlM_nil,
    equalityInstall]
  rfl

namespace Reference
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option cbv.maxSteps 10000000
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj

abbrev eqEnv := equalityEnvironment
def parts := (blockParts? 2 andPin).getD default
theorem inds_success : (match checkBlockInds (fueledOps .verified 32) eqEnv parts false with | .ok _ => true | .error _ => false) = true := by cbv

def shape := parts.toBlockShape.withSort .zero
def indsResult : Env × List ConstantVal × BlockShape :=
  (consBlockInds shape false [andRaw.toConstantVal] 0 eqEnv, [andRaw.toConstantVal], shape)
@[local cbv_eval] theorem inds_accepted : checkBlockInds (fueledOps .verified 32) eqEnv parts false = .ok indsResult := by cbv

def completed := parts.complete indsResult.2.2
def ctorResult : List (List (ConstantVal × Nat)) × List (List (List Level)) :=
  ([[ (andIntroRaw.toConstantVal, 2) ]], [[[.zero, .zero]]])
theorem andConstructorsAccepted : checkBlockCtors (fueledOps .verified 32) indsResult.1 indsResult.1 completed.toBlockShape (completed.members.zip indsResult.2.1) = .ok ctorResult := by cbv

def ctx : NestCtx := completed.toBlockShape.nestCtx [Expr.fvar 0 (.sort .zero), Expr.fvar 1 (.sort .zero)] indsResult.1.find?
def holes := (nestHoles ctx).getD []
@[local cbv_eval] theorem context_accepted : blockNestCtx (m := Except CheckError) completed.toBlockShape indsResult.2.1 indsResult.1.find? = .ok (ctx, holes) := by cbv
theorem andUniformAccepted : nestUniform (m := Except CheckError) ctx ctorResult.1 = .ok () := by cbv

end Reference

end AcceptanceStages
#audit_graph_module
