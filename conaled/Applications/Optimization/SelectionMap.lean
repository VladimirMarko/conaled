import Applications.Optimization.SelectionTies

/-! Exact transport of the accepted first-tie selector through candidate maps. -/
namespace Optimization.Thinning
universe u v w
variable {α : Type u} {β : Type v} {K : Type w} [LinearOrder K]

theorem argmin_map (f : α → β) (cost : β → K) (xs : List α) :
    argmin cost (xs.map f) = (argmin (cost ∘ f) xs).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,argmin,ih]
    cases h : argmin (cost ∘ f) xs with
    | none => rfl
    | some y => simp only [Option.map_some,Function.comp_apply]; split <;> rfl

end Optimization.Thinning
