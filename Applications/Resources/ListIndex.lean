import Applications.Resources.CallCount
import Mathlib.Data.List.Enum

/-!
# Measured occurrence indexing

This recursive realization returns the ordinary `List.zipIdx` value. It charges
one function entry, including the empty case, and the declared pair/successor
tariffs for each visited element. These are source-model charges, not a claim
about the standard library's compiled implementation, allocation or bit costs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.ListIndex
universe u
variable {α : Type u}

def run (pairCost succCost : Nat) : List α → Nat → Measured (List (α × Nat)) Nat
  | [], _ => ([], 1)
  | x :: xs, start =>
      CallCount.tick (bind ((x, start), pairCost) fun pair =>
        bind (start + 1, succCost) fun next =>
          bind (run pairCost succCost xs next) fun tail => pure (pair :: tail))

@[simp] theorem run_nil (pairCost succCost start : Nat) :
    run pairCost succCost ([] : List α) start = ([], 1) := rfl

theorem run_cons (pairCost succCost start : Nat) (x : α) (xs : List α) :
    run pairCost succCost (x :: xs) start =
      ((x, start) :: (run pairCost succCost xs (start + 1)).1,
        pairCost + succCost + (run pairCost succCost xs (start + 1)).2 + 1) := by
  simp [run, bind, pure, CallCount.tick, Nat.add_assoc]

theorem run_value (pairCost succCost : Nat) (xs : List α) (start : Nat) :
    (run pairCost succCost xs start).1 = xs.zipIdx start := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih => simp [run_cons, ih]

theorem run_cost (pairCost succCost : Nat) (xs : List α) (start : Nat) :
    (run pairCost succCost xs start).2 = (pairCost + succCost + 1) * xs.length + 1 := by
  induction xs generalizing start with
  | nil => simp [run_nil]
  | cons x xs ih =>
      simp only [run_cons, ih, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem run_exact (pairCost succCost : Nat) (xs : List α) (start : Nat) :
    run pairCost succCost xs start =
      (xs.zipIdx start, (pairCost + succCost + 1) * xs.length + 1) :=
  Prod.ext (run_value pairCost succCost xs start) (run_cost pairCost succCost xs start)

theorem run_length (pairCost succCost : Nat) (xs : List α) (start : Nat) :
    (run pairCost succCost xs start).1.length = xs.length := by
  simp [run_value]

theorem run_ids (pairCost succCost : Nat) (xs : List α) (start : Nat) :
    ((run pairCost succCost xs start).1.map Prod.snd) = List.range' start xs.length := by
  rw [run_value, List.zipIdx_map_snd]

end Resources.ListIndex
