import Applications.Resources.QuickSort

/-!
# Mapping the actual measured first-pivot execution

Mapping payloads and pulling the Boolean comparator back preserves both recorded
cost coordinates. This compares the existing executions; it does not charge for
computing the map or for a later occurrence lookup. No injectivity of the map is
needed, so duplicate payloads and equal keys retain their occurrences.
-/

namespace Resources.QuickSort

universe u v
variable {α : Type u} {β : Type v}

/-- Both filters, recursive results and measured append observations commute
with a payload map when the comparator is pulled back along that same map. -/
theorem run_map (f : α → β) (lt : β → β → Bool) (xs : List α) :
    run lt (xs.map f) =
      ((run (fun a b => lt (f a) (f b)) xs).1.map f,
        (run (fun a b => lt (f a) (f b)) xs).2) := by
  match xs with
  | [] => simp
  | pivot :: ys =>
      simp only [List.map_cons, run_cons, List.filter_map, Function.comp_def,
        run_map f lt (ys.filter (fun a => lt (f a) (f pivot))),
        run_map f lt (ys.filter (fun a => !(lt (f a) (f pivot)))),
        List.length_map, List.map_append, List.map_nil]
termination_by xs.length
decreasing_by
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- The existing pair of exercise and append observations is unchanged. -/
theorem counts_map (f : α → β) (lt : β → β → Bool) (xs : List α) :
    (run lt (xs.map f)).2 = (run (fun a b => lt (f a) (f b)) xs).2 := by
  rw [run_map]

theorem exerciseCost_map (f : α → β) (lt : β → β → Bool) (xs : List α) :
    exerciseCost lt (xs.map f) = exerciseCost (fun a b => lt (f a) (f b)) xs := by
  unfold exerciseCost
  rw [run_map]

theorem appendCost_map (f : α → β) (lt : β → β → Bool) (xs : List α) :
    appendCost lt (xs.map f) = appendCost (fun a b => lt (f a) (f b)) xs := by
  unfold appendCost
  rw [run_map]

theorem literalCost_map (f : α → β) (lt : β → β → Bool) (xs : List α) :
    literalCost lt (xs.map f) = literalCost (fun a b => lt (f a) (f b)) xs := by
  simp only [literalCost, exerciseCost_map, appendCost_map]

end Resources.QuickSort
