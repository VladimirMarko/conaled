import Std

/-! Positional tie observations, independent of a selector. -/
namespace Optimization
universe u v
variable {α : Type u} {K : Type v}

/-- The first minimum occurrence has strictly larger costs before it. -/
def FirstMinimum [LT K] [LE K] (cost : α → K) (xs : List α) (a : α) : Prop :=
  ∃ before after, xs = before ++ a :: after ∧
    (∀ b ∈ before, cost a < cost b) ∧ (∀ b ∈ after, cost a ≤ cost b)

/-- The last minimum occurrence has strictly larger costs after it. -/
def LastMinimum [LT K] [LE K] (cost : α → K) (xs : List α) (a : α) : Prop :=
  ∃ before after, xs = before ++ a :: after ∧
    (∀ b ∈ before, cost a ≤ cost b) ∧ (∀ b ∈ after, cost a < cost b)

end Optimization
