import SquareKit.DependentPairEliminationCongruence

/-! Syntax-fixing inclusion of the two complete, separately specified projection tables. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations

@[simp] theorem Judgment.map_identity (j : Judgment S) :
    j.map (.identity S) = j := by
  rcases j with ⟨V, Γ, φ⟩
  cases φ <;> simp only [Judgment.map, Context.map_identity, Judgment.mapForm] <;> rfl

@[simp] theorem Schema.map_identity (r : Schema S) : r.map (.identity S) = r := by
  rcases r with ⟨ps, j⟩
  have h : Judgment.map (.identity S) = id := funext Judgment.map_identity
  simp [Schema.map, h]

/-- Congruence and declaration rules are replayed; the pair rule table has its
own independently checked inclusion. -/
def projectionInclusionLabel : (projectionPresentation false).Label →
    (projectionPresentation true).Label
  | .inl r => .inl r
  | .inr (.inl r) => .inr (.inl (ProjectionRule.inclusion r))
  | .inr (.inr r) => .inr (.inr r)

def projectionInclusion : TheoryMap (projectionPresentation false) (projectionPresentation true) id where
  certificate r := by
    cases r with
    | inl r => exact Derivation.rule (R := projectionPresentation true) (.inl r) (fun i => .hyp ⟨i, rfl⟩)
    | inr r =>
      cases r with
      | inr r => exact Derivation.rule (R := projectionPresentation true) (.inr (.inr r)) (fun i => .hyp ⟨i, rfl⟩)
      | inl r =>
        cases r with
        | formation Γ A B =>
          exact Derivation.rule (R := projectionPresentation true) (.inr (.inl (.formation Γ A B))) (fun i => .hyp ⟨i, rfl⟩)
        | pair Γ A B a b =>
          exact Derivation.rule (R := projectionPresentation true) (.inr (.inl (.pair Γ A B a b))) (fun i => .hyp ⟨i, rfl⟩)
        | first Γ A B p =>
          exact Derivation.rule (R := projectionPresentation true) (.inr (.inl (.first Γ A B p))) (fun i => .hyp ⟨i, rfl⟩)
        | second Γ A B p =>
          exact Derivation.rule (R := projectionPresentation true) (.inr (.inl (.second Γ A B p))) (fun i => .hyp ⟨i, rfl⟩)
        | firstBeta Γ A B a b =>
          exact Derivation.rule (R := projectionPresentation true) (.inr (.inl (.firstBeta Γ A B a b))) (fun i => .hyp ⟨i, rfl⟩)
        | secondBeta Γ A B a b =>
          exact Derivation.rule (R := projectionPresentation true) (.inr (.inl (.secondBeta Γ A B a b))) (fun i => .hyp ⟨i, rfl⟩)
        | eta h => contradiction

end SquareKit.DependentPairJudgments
