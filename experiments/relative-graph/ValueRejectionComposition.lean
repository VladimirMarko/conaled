import AcceptanceComposition
import ConLeche.Verify.CheckerSplit
/-! Experimental #135 negative control: explicit successful guards followed by type mismatch.
See [scope report](../../docs/research/relative-emitted-acceptance.md). -/
namespace ValueRejectionComposition
open ConLeche
variable {μ : CheckMode} {F : Nat} {env : Env}
theorem thm_mismatch {cv : ConstantVal} {value vtype stype : Expr} {u : Level}
    (hst : inferTypeCore μ env F 0 cv.type = .ok stype)
    (hsort : ensureSortCore μ env F 0 stype = .ok u)
    (heqv : Level.isEquiv u .zero = some true)
    (hlb : value.looseBVarsBounded 0 = true)
    (hif : value.hasFvar = false)
    (hvp : value.allLevelParamsDefined cv.levelParams = true)
    (hvr : value.constsResolve env = true)
    (hvt : inferTypeCore μ env F 0 value = .ok vtype)
    (hde : isDefEqCore μ env F 0 vtype cv.type = .ok false) :
    checkThmVal (fueledOps μ F) env cv value = .error (.invalid s!"type mismatch in theorem {cv.name}") := by
  simp only [checkThmVal, fueledOps_inferType, fueledOps_isDefEq,
    fueledOps_ensureSort, liftFueled, Bind.bind, Except.bind, Pure.pure, Except.pure, hst,
    hsort, heqv, hlb, hif, hvp, hvr, hvt, hde, Bool.false_eq_true, ↓reduceIte]

  rfl

end ValueRejectionComposition
#audit_graph_module
