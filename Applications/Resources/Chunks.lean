import Applications.Resources.ListCalls
import Applications.Sequences.Chunks

/-! The FDSA chopping execution calls take and drop separately at each
nonempty positive-size step. Their measured traversals both contribute to the
source call count. The existing split-length adapter specifies only the value;
it supplies neither the execution nor its cost. Zero-size and empty calls each
return the source's empty result with one entry charge.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.Chunks
open Applications.Sequences.Chunks
universe u
variable {α : Type u}

/-- Source recursion with separate measured take and drop calls. -/
def chopRun : (d : Nat) → List α → Measured (List (List α)) Nat
  | 0, _ => ([], 1)
  | _ + 1, [] => ([], 1)
  | d + 1, x :: xs =>
      let taken := ListCalls.takeRun (d + 1) (x :: xs)
      let dropped := ListCalls.dropRun (d + 1) (x :: xs)
      let tail := chopRun (d + 1) dropped.1
      (taken.1 :: tail.1, taken.2 + dropped.2 + tail.2 + 1)
termination_by _ xs => xs.length
decreasing_by
  simp only [ListCalls.dropRun_exact, List.length_drop, List.length_cons]
  omega

theorem chopRun_zero (xs : List α) : chopRun 0 xs = ([], 1) := by
  rw [chopRun]

theorem chopRun_nil (d : Nat) : chopRun d ([] : List α) = ([], 1) := by
  cases d <;> rw [chopRun]

/-- The positive step exposes both traversals and one recursive entry. -/
theorem chopRun_eq_cons (d : Nat) (xs : List α) (hd : 0 < d) (hx : xs ≠ []) :
    chopRun d xs =
      (xs.take d :: (chopRun d (xs.drop d)).1,
        (ListCalls.takeRun d xs).2 + (ListCalls.dropRun d xs).2 +
          (chopRun d (xs.drop d)).2 + 1) := by
  cases d with
  | zero => omega
  | succ d =>
      cases xs with
      | nil => exact False.elim (hx rfl)
      | cons x xs =>
          rw [chopRun]
          simp only [ListCalls.takeRun_exact, ListCalls.dropRun_exact]

theorem chopRun_value (d : Nat) (xs : List α) : (chopRun d xs).1 = chop d xs := by
  by_cases hd : d = 0
  · subst d
    rw [chopRun_zero, chop_zero]
  by_cases hx : xs = []
  · subst xs
    rw [chopRun_nil, chop_nil]
  rw [chopRun_eq_cons d xs (Nat.pos_of_ne_zero hd) hx,
    chop_eq_cons d xs (Nat.pos_of_ne_zero hd) hx]
  simp only [chopRun_value d (xs.drop d)]
termination_by xs.length
decreasing_by exact drop_length_lt d xs (Nat.pos_of_ne_zero hd) hx

/-- The exact count includes the terminal empty call, both list traversals,
and one chopping entry for each nonempty chunk. -/
theorem chopRun_cost (d : Nat) (xs : List α) (hd : 0 < d) :
    (chopRun d xs).2 = 2 * xs.length + 3 * (xs.length ⌈/⌉ d) + 1 := by
  by_cases hx : xs = []
  · subst xs
    rw [chopRun_nil]
    simp
  have hcount : xs.length ⌈/⌉ d = (xs.drop d).length ⌈/⌉ d + 1 := by
    have h := congrArg List.length (chop_eq_cons d xs hd hx)
    simpa only [length_chop, List.length_cons] using h
  rw [chopRun_eq_cons d xs hd hx]
  simp only [ListCalls.takeRun_exact, ListCalls.dropRun_exact]
  rw [chopRun_cost d (xs.drop d) hd]
  have hsplit : min d xs.length + (xs.drop d).length = xs.length := by
    simp only [List.length_drop]
    omega
  omega
termination_by xs.length
decreasing_by exact drop_length_lt d xs hd hx

theorem chopRun_exact (d : Nat) (xs : List α) (hd : 0 < d) :
    chopRun d xs = (chop d xs, 2 * xs.length + 3 * (xs.length ⌈/⌉ d) + 1) :=
  Prod.ext (chopRun_value d xs) (chopRun_cost d xs hd)

/-- This source bound is uniform in the grouping size, including size zero. -/
theorem chopRun_cost_bound (d : Nat) (xs : List α) :
    (chopRun d xs).2 ≤ 5 * xs.length + 1 := by
  by_cases hd : d = 0
  · subst d
    rw [chopRun_zero]
    omega
  have hc := length_chop_le d xs
  rw [length_chop] at hc
  rw [chopRun_cost d xs (Nat.pos_of_ne_zero hd)]
  omega

theorem chopRun_one_cost (xs : List α) : (chopRun 1 xs).2 = 5 * xs.length + 1 := by
  rw [chopRun_cost 1 xs (by decide), Nat.ceilDiv_eq_add_pred_div]
  omega

theorem chopRun_length (d : Nat) (xs : List α) :
    (chopRun d xs).1.length = xs.length ⌈/⌉ d := by
  rw [chopRun_value, length_chop]

theorem chopRun_mem_ne_nil (d : Nat) (xs ys : List α)
    (hy : ys ∈ (chopRun d xs).1) : ys ≠ [] := by
  rw [chopRun_value] at hy
  exact chop_mem_ne_nil d xs ys hy

theorem chopRun_mem_length (d : Nat) (xs ys : List α)
    (hy : ys ∈ (chopRun d xs).1) : ys.length ≤ d := by
  rw [chopRun_value] at hy
  exact length_mem_chop d xs ys hy

theorem chopRun_flatten (d : Nat) (xs : List α) (hd : 0 < d) :
    (chopRun d xs).1.flatten = xs := by
  rw [chopRun_value, flatten_chop d xs hd]

end Resources.Chunks
