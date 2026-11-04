import Applications.Resources.QuickSortTransport
import Mathlib.Tactic.NormNum

/-! Connected occurrence, duplicate-payload and comparator-boundary examples
for the actual measured first-pivot execution. -/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.QuickSortTransport

open Resources.QuickSort

universe u
variable {α : Type u}

/-- No equality or inhabitance instance on the payload is needed. The label
list may itself be incomplete or contain repetitions. -/
theorem arbitrary_occurrence_lookup (lt : α → α → Bool) (xs : List α)
    (labels : List (Fin xs.length)) :
    run lt (labels.map (fun i => xs[i])) =
      ((run (fun i j : Fin xs.length => lt xs[i] xs[j]) labels).1.map
          (fun i => xs[i]),
        (run (fun i j : Fin xs.length => lt xs[i] xs[j]) labels).2) :=
  run_map (fun i : Fin xs.length => xs[i]) lt labels

theorem arbitrary_occurrence_costs (lt : α → α → Bool) (xs : List α)
    (labels : List (Fin xs.length)) :
    exerciseCost lt (labels.map (fun i => xs[i])) =
        exerciseCost (fun i j : Fin xs.length => lt xs[i] xs[j]) labels ∧
      appendCost lt (labels.map (fun i => xs[i])) =
        appendCost (fun i j : Fin xs.length => lt xs[i] xs[j]) labels ∧
      literalCost lt (labels.map (fun i => xs[i])) =
        literalCost (fun i j : Fin xs.length => lt xs[i] xs[j]) labels :=
  ⟨exerciseCost_map (fun i : Fin xs.length => xs[i]) lt labels,
    appendCost_map (fun i : Fin xs.length => xs[i]) lt labels,
    literalCost_map (fun i : Fin xs.length => xs[i]) lt labels⟩

/-- A visibly non-injective map still preserves the entire measured result
with its pulled-back comparator. It never collapses list occurrences. -/
theorem noninjective_constant_run (xs : List Bool) :
    ¬ Function.Injective (fun _ : Bool => (0 : Nat)) ∧
      run (fun a b : Nat => decide (a < b)) (xs.map (fun _ => 0)) =
        ((run (fun _ _ : Bool => false) xs).1.map (fun _ => 0),
          (run (fun _ _ : Bool => false) xs).2) := by
  constructor
  · intro h
    have heq : false = true := h rfl
    cases heq
  · exact run_map (fun _ : Bool => (0 : Nat)) (fun a b : Nat => decide (a < b)) xs

theorem duplicate_fixture :
    run (fun a b : Nat => decide (a < b))
        (([true, false, true] : List Bool).map (fun _ => 0)) =
      ([0, 0, 0], (25, 9)) := by
  rw [run_map]
  norm_num [run_cons]

theorem empty_uninhabited (f : Empty → α) (lt : α → α → Bool) :
    (run lt (([] : List Empty).map f)).2 = (1, 0) := by
  simp only [counts_map, run_nil]

/-- The comparator correspondence is substantive: reversing the branch
choice on a two-element input changes the actual append-inclusive cost. -/
theorem comparator_cost_boundary :
    literalCost (fun _ _ : Bool => false) [false, true] = 19 ∧
      literalCost (fun _ _ : Bool => true) [false, true] = 20 ∧
      literalCost (fun _ _ : Bool => false) [false, true] ≠
        literalCost (fun _ _ : Bool => true) [false, true] := by
  norm_num [literalCost, exerciseCost, appendCost, run_cons]

end Examples.QuickSortTransport
