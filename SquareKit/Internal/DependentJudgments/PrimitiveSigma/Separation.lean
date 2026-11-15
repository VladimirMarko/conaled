import SquareKit.Internal.DependentJudgments.PrimitiveSigma.Reindexing
import SquareKit.Internal.DependentJudgments.PrimitiveSigma.ConstantStable

/-! The source split-eta rule fails in a model of primitive elimination.
This is a counterinterpretation, rather than an unsuccessful proof search. -/
namespace SquareKit.Internal.DependentJudgments.PrimitiveSigma
open GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false

abbrev splitEtaRule : Rule signature where
  parameterCount := 5
  hypotheses := 4
  premise := ![family (.var 0) (.var 1), family (extend (.var 0) (.var 1)) (.var 2),
    family (extend (.var 0) (sigma (.var 1) (.var 2))) (.var 3),
    term (extend (.var 0) (sigma (.var 1) (.var 2))) (.var 3) (.var 4)]
  conclusion := .eq (split (.var 1) (.var 2) (.var 3)
    (subTm (.var 4) (pack (.var 1) (.var 2)))) (.var 4)

namespace Separation
abbrev M := ConstantFamilies.model PUnit
abbrev S := (ConstantFamilies.stable PUnit).toCapability
abbrev sumContext := M.extend PUnit (S.sigma (Γ := PUnit) PUnit PUnit)
def observeFlag : M.Section sumContext Bool := ⟨fun p => p.2.2⟩
def valuation : Fin 5 → Value M.toStructuralModel :=
  ![.context PUnit, .family PUnit PUnit, .family (M.extend PUnit PUnit) PUnit,
    .family sumContext Bool, .term sumContext Bool observeFlag]

theorem premises : ∀ i, (splitEtaRule.premise i).eval (algebra M S) valuation := by
  intro i
  fin_cases i
  · exact ⟨PUnit, PUnit, rfl, rfl⟩
  · refine ⟨M.extend PUnit PUnit, PUnit, ?_, rfl⟩
    simp [Term.eval, algebra, Contextual.algebra, DependentJudgments.operation, valuation]
  · refine ⟨sumContext, Bool, ?_, rfl⟩
    simp [Term.eval, algebra, operation, Contextual.algebra, DependentJudgments.operation, valuation]
  · refine ⟨sumContext, Bool, observeFlag, ?_, rfl, rfl⟩
    simp [Term.eval, algebra, operation, Contextual.algebra, DependentJudgments.operation, valuation]

theorem conclusion_false : ¬ splitEtaRule.conclusion.eval (algebra M S) valuation := by
  intro h
  change (split (.var 1) (.var 2) (.var 3)
    (subTm (.var 4) (pack (.var 1) (.var 2)))).eval (algebra M S) valuation = valuation 4 at h
  simp only [Term.eval, FinitaryTerm.fold, algebra, operation, Contextual.algebra,
    DependentJudgments.operation, valuation, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, inputs_values, Value.familyAt_family,
    Value.termIn_term, Value.termAt_term] at h
  have e := eq_of_heq (Value.term.inj h).2.2
  have bad := congrArg (fun f => f.down (PUnit.unit, ((PUnit.unit, PUnit.unit), true))) e
  change false = true at bad
  cases bad

/-- No derivation of this rule from its well-typed premises exists in the
selected weak source theory. The model also supplies stable elimination and J. -/
theorem splitEta_not_derivable :
    Derivation theory (List.ofFn splitEtaRule.premise) splitEtaRule.conclusion → False := by
  intro d
  apply conclusion_false
  apply d.sound (model M S) valuation
  intro p hp
  rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
  exact premises i

/-- The same obstruction remains after admitting all selected context
substitution rules. -/
theorem stable_splitEta_not_derivable :
    Derivation Reindexing.theory (List.ofFn splitEtaRule.premise)
      splitEtaRule.conclusion → False := by
  intro d
  apply conclusion_false
  apply d.sound (Reindexing.model M (ConstantFamilies.stable PUnit)) valuation
  intro p hp
  rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
  exact premises i

end Separation
end SquareKit.Internal.DependentJudgments.PrimitiveSigma
