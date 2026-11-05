import SquareKit.Internal.DependentJudgments.PrimitiveSigma.Recovery
import SquareKit.Internal.DependentJudgments.PrimitiveSigma.Maps
import SquareKit.Internal.DependentJudgments.Sigma.DerivedEliminationLaws

/-! The strong provider specializes the primitive contract with its exact
chosen eliminator. The source presentations agree at their typed boundary. -/
namespace SquareKit.Internal.DependentJudgments.PrimitiveSigma
open GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
universe u
variable (M : PathTransport.Typed.Model.{u}) (S : Sigma.Capability M.toStructuralModel)
variable (Γ : M.Context) (A : M.Family Γ) (B : M.Family (M.extend Γ A))
variable (C : M.Family (M.extend Γ (S.sigma A B)))
variable (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B)))

/-- Source primitive split and strong derived split denote the same selected
section when the motive and branch have the required dependent types. -/
theorem split_source_agreement :
    (split (.var 0) (.var 1) (.var 2) (.var 3) : Expression (Fin 4)).eval
      (algebra M (ofStrong S))
      ![.family Γ A, .family (M.extend Γ A) B,
        .family (M.extend Γ (S.sigma A B)) C,
        .term (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B)) d] =
    (Sigma.split (.var 0) (.var 1) (.var 3) : Sigma.Expression (Fin 4)).eval
      (Sigma.algebra M S)
      ![.family Γ A, .family (M.extend Γ A) B,
        .family (M.extend Γ (S.sigma A B)) C,
        .term (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B)) d] := by
  simp only [Term.eval, FinitaryTerm.fold, algebra, operation, ofStrong,
    Sigma.algebra, Sigma.operation, Contextual.algebra, DependentJudgments.operation,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, inputs_values, Sigma.inputs_values,
    Value.familyAt_family, Value.termAt_term, Value.termIn_term]
  exact Value.term_eq (S.split_type A B C).symm (S.split_heq A B C d)

/-- Typed derivations in the weaker source theory are valid in every existing
strong provider, with no additional model-builder obligations. -/
theorem interpret_strong {V : Type} {Ω : List (Judgment V)} {a : Judgment V}
    (proof : Derivation theory Ω a) (ρ : V → Value M.toStructuralModel)
    (h : ∀ p ∈ Ω, p.eval (algebra M (ofStrong S)) ρ) :
    a.eval (algebra M (ofStrong S)) ρ := interpret proof M (ofStrong S) ρ h

end SquareKit.Internal.DependentJudgments.PrimitiveSigma
