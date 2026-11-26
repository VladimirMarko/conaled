import Examples.Lawvere
import SquareKit.Lawvere.Action

/-! Evaluation clients use ordinary numerals and carrier instances after restriction. -/
noncomputable section
namespace Examples.LawvereEncoding
open SquareKit SquareKit.Lawvere SquareKit.Lawvere.Operations Examples.Lawvere

abbrev interpretation := pointedInvolution.interpretation smoothSymbol smooth_equation
abbrev smoothAction : Action smoothOperations ℝ := (smoothAlgebra ℝ).action
abbrev realAction : Action pointedInvolution.operations ℝ :=
  smoothAction.restrict interpretation

def negOp : pointedInvolution.operations.Op 1 :=
  Quotient.mk _ (.node .neg (fun _ => .leaf 0))
def zeroOp : pointedInvolution.operations.Op 0 :=
  Quotient.mk _ (.node .zero Fin.elim0)

example : realAction.act negOp (fun _ => 3) = -3 := rfl
example : realAction.act zeroOp Fin.elim0 = 0 := rfl
example : realAction.act negOp (fun _ => realAction.act negOp (fun _ => 3)) = 3 := by
  change -(-(3 : ℝ)) = 3
  exact neg_neg _
example : realAction.algebra.model = realModel := Action.restrict_model _ _

/-- Composed restriction needs no new arity or scalar annotations. -/
example : (smoothAction.restrict
    ((Map.id pointedInvolution.operations).comp interpretation)).act negOp (fun _ => 3) = -3 := rfl

/-- The same interface works for the unary Boolean model. -/
abbrev boolAction := ((unaryPresentation unaryInvolution).algebra boolUnary).action
example : boolAction.act
    (Quotient.mk ((unaryPresentation unaryInvolution).setoid 1)
      (UnaryInteraction.term [()])) (fun _ => true) = false := rfl

/-- Crossing the boundary and back retains the whole algebra, not just evaluations. -/
example (O : Operations) (A : O.Algebra) : A.action.algebra = A := A.action_algebra
example (O : Operations) (X : Type*) (A : Action O X) : A.algebra.action = A := A.algebra_action

/-- The original composition client still computes eight. -/
example : smoothAction.act
    (smoothOperations.subst (double 0) increment) (fun _ => 3) = 8 := by
  change (2 : ℝ) * (3 + 1) = 8
  norm_num
end Examples.LawvereEncoding
