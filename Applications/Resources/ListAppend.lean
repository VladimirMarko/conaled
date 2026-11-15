import Applications.Resources.Measured

/-!
# Executed list append with explicit source prices

The recursive primitive counts copied left cells. `weighted` assigns a price to
each observed constructor and each copied cell, including the final nil case.
The affine translation is applied to each append call separately.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.ListAppend

universe u
variable {α : Type u}

/-- Ordinary append, counting one copied cell per left cons. -/
def copies : List α → List α → Measured (List α) Nat
  | [], ys => (ys, 0)
  | x :: xs, ys =>
      let rest := copies xs ys
      (x :: rest.1, rest.2 + 1)

theorem copies_exact (xs ys : List α) : copies xs ys = (xs ++ ys, xs.length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [copies, ih]

/-- Full left-spine observation and copying, with independent nonnegative prices. -/
def weighted (dispatch cell : Nat) (xs ys : List α) : Measured (List α) Nat :=
  reweight (fun n => (dispatch + cell) * n + dispatch) (copies xs ys)

theorem weighted_exact (dispatch cell : Nat) (xs ys : List α) :
    weighted dispatch cell xs ys =
      (xs ++ ys, (dispatch + cell) * xs.length + dispatch) := by
  simp [weighted, reweight, copies_exact]

theorem weighted_value (dispatch cell : Nat) (xs ys : List α) :
    (weighted dispatch cell xs ys).1 = xs ++ ys := by rw [weighted_exact]

theorem weighted_work (dispatch cell : Nat) (xs ys : List α) :
    (weighted dispatch cell xs ys).2 = (dispatch + cell) * xs.length + dispatch := by
  rw [weighted_exact]

end Resources.ListAppend
