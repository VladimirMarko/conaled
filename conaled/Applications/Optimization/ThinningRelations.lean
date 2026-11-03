import Applications.Optimization.Thinning
import Applications.Optimization.Relations

/-! # Optional relational presentations of candidate pruning

Ordinary callers use `Represents` and its theorems directly. These adapters let
a pruning derivation compose with a change of representation using existing
relational squares; they require no syntax encoding.
-/
namespace Optimization.Thinning

universe u

/-- Implemented candidates retain origin and dominate specified candidates. -/
def candidateRep {α : Type u} (R : α → α → Prop) : Relational.RelRep where
  R := List α
  S := List α
  Rel retained original := Represents R original retained

/-- A relation-preserving map also preserves candidate refinement. -/
def mapSquare {α β : Type u} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hm : ∀ x y, R x y → S (f x) (f y)) :
    Relational.RelSquare (candidateRep R) (candidateRep S) where
  impl := List.map f
  spec := List.map f
  preserves := represents_map f hm

/-- Fold pruning connects the independently supplied generator to its frontier. -/
def foldSquare {α δ : Type u} (R : α → α → Prop)
    (hr : ∀ x, R x x) (ht : ∀ x y z, R x y → R y z → R x z)
    (step : δ → List α → List α) (prune : List α → List α)
    (step_preserves : ∀ d xs ys, Represents R xs ys → Represents R (step d xs) (step d ys))
    (prune_correct : ∀ xs, Represents R xs (prune xs)) (seed : List α) :
    Relational.RelSquare (inputRep (List δ)) (candidateRep R) where
  impl := pruneFold step prune seed
  spec := List.foldr step seed
  preserves := by
    rintro ds _ rfl
    exact pruneFold_refinement R hr ht step prune step_preserves prune_correct seed ds

end Optimization.Thinning
