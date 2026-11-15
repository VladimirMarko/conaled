import SquareKit.DependentDeclarationSequentialRules
import SquareKit.DependentEliminationSequentialRules

/-! A checked syntactic dependency order for the closed pair-rule templates.
This is an occurrence check, distinct from typing boundary derivations. -/
namespace SquareKit.DependentSequentialRules
open DependentTheoryMaps DependentPairJudgments

/-- All referenced metavariables precede the supplied cutoff. Bound variables
are tracked by the expression scope and do not count as metavariables. -/
def referencesBefore {S : Signature} {M : Metavariables} (n : Nat) :
    {V : Type} → Expr (extend S M) V → Bool
  | _, .var _ => true
  | _, .app sym es =>
    (match sym with | .inl _ => true | .inr m => decide (m.val < n)) &&
      (List.finRange ((extend S M).arity sym)).all (fun i => referencesBefore n (es i))

def Telescope.referencesBefore {S : Signature} {M : Metavariables} (n : Nat) :
    {k : Nat} → Telescope (DependentTheoryMaps.extend S M) k → Bool
  | _, .empty => true
  | _, .extend Γ A => Γ.referencesBefore n && DependentSequentialRules.referencesBefore n A

def formReferencesBefore {S : Signature} {M : Metavariables} (n : Nat) :
    Form (extend S M) V → Bool
  | .ctx => true
  | .type A => referencesBefore n A
  | .term a A => referencesBefore n a && referencesBefore n A
  | .typeEq A B => referencesBefore n A && referencesBefore n B
  | .termEq a b A => referencesBefore n a && referencesBefore n b && referencesBefore n A

/-- Premise i may mention its own declared metavariable and earlier ones;
its bound-variable telescope may mention only earlier metavariables. -/
def RelativeJudgment.orderedAt {S : Signature} {M : Metavariables}
    (j : RelativeJudgment (extend S M)) (i : Nat) : Bool :=
  j.telescope.referencesBefore i && formReferencesBefore (i + 1) j.form

/-- One premise per declared argument, with no forward metavariable references.
This predicate does not assert full BHL acceptability or boundary derivability. -/
def Rule.Ordered {S : Signature} {M : Metavariables} (r : Rule S M) : Prop :=
  r.premises.length = M.count ∧
  (∀ i : Fin r.premises.length, (r.premises.get i).orderedAt i.val = true) ∧
  formReferencesBefore M.count r.conclusion = true

instance {S : Signature} {M : Metavariables} (r : Rule S M) : Decidable r.Ordered := by
  unfold Rule.Ordered
  infer_instance

namespace Projection
open DependentProjectionSequentialRules

theorem formation_ordered : formation.Ordered := by decide
theorem component_ordered (r : ComponentRule) : (componentRule r).Ordered := by
  cases r <;> decide
theorem argument_ordered (r : ArgumentRule) : (argumentRule r).Ordered := by
  cases r <;> decide

/-- Declaring B(x) before A is not admitted by the checked dependency order. -/
theorem reversed_family_rejected :
    ¬ ({ formation with premises := formation.premises.reverse }).Ordered := by decide

end Projection

namespace Elimination
open DependentEliminationSequentialRules

theorem formation_ordered : formationRule.Ordered := by decide
theorem pack_ordered : packRule.Ordered := by decide
theorem split_ordered : splitRule.Ordered := by decide
theorem beta_ordered : betaRule.Ordered := by decide
theorem eta_ordered : etaRule.Ordered := by decide

end Elimination

namespace Declarations
open DependentDeclarationSequentialRules

theorem nullary_ordered (k : Bool) : (nullary k).Ordered := by cases k <;> decide
theorem unary_ordered (k : Bool) (r : Unary) : (unary k r).Ordered := by
  cases k <;> cases r <;> decide
theorem binary_ordered (k : Bool) : (binary k).Ordered := by cases k <;> decide

end Declarations
end SquareKit.DependentSequentialRules
