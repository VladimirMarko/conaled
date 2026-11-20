import Applications.Sorting.SourceSelection
import Applications.Resources.Measured
import Applications.Resources.Growth

/-!
# Comparisons performed by source selection sorting

Each nonempty select step executes one relation test and charges one comparison.
The sort executes that measured select, recurses on its actual returned remainder,
and retains the selected value. Zero fuel and empty input perform no selection.
The independent size recurrence is proved to agree with this execution before
its triangular formula or asymptotic bounds are used. Counts are independent of
the cost of implementing a relation test, function calls, allocation and runtime.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.SelectionSort

universe u
variable {α : Type u}

open Applications.Sorting

/-- Execute and charge the head test, then select through the chosen tail call. -/
def selectRun (r : α → α → Prop) [DecidableRel r] (x : α) :
    List α → Measured (α × List α) Nat
  | [] => pure (x, [])
  | h :: t =>
      bind ((decide (r x h), 1) : Measured Bool Nat) (fun keep =>
        if keep then
          bind (selectRun r x t) (fun p => pure (p.1, h :: p.2))
        else
          bind (selectRun r h t) (fun p => pure (p.1, x :: p.2)))

theorem selectRun_value (r : α → α → Prop) [DecidableRel r]
    (x : α) (xs : List α) : (selectRun r x xs).1 = SourceSelection.select r x xs := by
  induction xs generalizing x with
  | nil => rfl
  | cons h t ih =>
      by_cases hx : r x h <;>
        simp [selectRun, bind, pure, hx, ih, SourceSelection.select]

/-- Both branches traverse the whole tail; neither stops at an early minimum. -/
theorem selectRun_comparisons (r : α → α → Prop) [DecidableRel r]
    (x : α) (xs : List α) : (selectRun r x xs).2 = xs.length := by
  induction xs generalizing x with
  | nil => rfl
  | cons h t ih =>
      by_cases hx : r x h <;>
        simp [selectRun, bind, pure, hx, ih, Nat.add_comm]

theorem selectRun_exact (r : α → α → Prop) [DecidableRel r]
    (x : α) (xs : List α) :
    selectRun r x xs = (SourceSelection.select r x xs, xs.length) :=
  Prod.ext (selectRun_value r x xs) (selectRun_comparisons r x xs)

/-- This size-only specification is independent of values and of any relation. -/
def sizeCost : Nat → Nat → Nat
  | _, 0 => 0
  | 0, _ + 1 => 0
  | m + 1, n + 1 => m + sizeCost m n

theorem sizeCost_zero (m : Nat) : sizeCost m 0 = 0 := by cases m <;> rfl

theorem sizeCost_nil (n : Nat) : sizeCost 0 n = 0 := by cases n <;> rfl

theorem sizeCost_step (m n : Nat) :
    sizeCost (m + 1) (n + 1) = m + sizeCost m n := rfl

/-- Execute select and recurse on its measured remainder, not a specification
or a separately computed sorted list. Output reconstruction carries zero charge. -/
def sortFuelRun (r : α → α → Prop) [DecidableRel r] :
    List α → Nat → Measured (List α) Nat
  | _, 0 => pure []
  | [], _ + 1 => pure []
  | x :: xs, n + 1 =>
      bind (selectRun r x xs) (fun p =>
        bind (sortFuelRun r p.2 n) (fun ys => pure (p.1 :: ys)))

theorem sortFuelRun_value (r : α → α → Prop) [DecidableRel r]
    (xs : List α) (n : Nat) :
    (sortFuelRun r xs n).1 = SourceSelection.sortFuel r xs n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
      cases xs with
      | nil => rfl
      | cons x xs =>
          simp [sortFuelRun, bind, pure, ih, selectRun_value, SourceSelection.sortFuel]

/-- The actual remainder's proved length connects execution to the size model. -/
theorem sortFuelRun_comparisons (r : α → α → Prop) [DecidableRel r]
    (xs : List α) (n : Nat) : (sortFuelRun r xs n).2 = sizeCost xs.length n := by
  induction n generalizing xs with
  | zero => exact (sizeCost_zero xs.length).symm
  | succ n ih =>
      cases xs with
      | nil => rfl
      | cons x xs =>
          simp [sortFuelRun, bind, pure, ih, selectRun_value,
            selectRun_comparisons, SourceSelection.select_length, sizeCost]

theorem sortFuelRun_exact (r : α → α → Prop) [DecidableRel r]
    (xs : List α) (n : Nat) :
    sortFuelRun r xs n = (SourceSelection.sortFuel r xs n, sizeCost xs.length n) :=
  Prod.ext (sortFuelRun_value r xs n) (sortFuelRun_comparisons r xs n)

def sortRun (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    Measured (List α) Nat := sortFuelRun r xs xs.length

theorem sortRun_value (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    (sortRun r xs).1 = SourceSelection.sort r xs := sortFuelRun_value r xs xs.length

theorem sortRun_comparisons (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    (sortRun r xs).2 = sizeCost xs.length xs.length :=
  sortFuelRun_comparisons r xs xs.length

/-- Additional fuel cannot perform comparisons after the list becomes empty. -/
theorem sizeCost_of_le (m n : Nat) (h : m ≤ n) : sizeCost m n = sizeCost m m := by
  induction m generalizing n with
  | zero => simp [sizeCost_nil]
  | succ m ih =>
      cases n with
      | zero => omega
      | succ n =>
          rw [sizeCost_step, sizeCost_step, ih n (Nat.le_of_succ_le_succ h)]

theorem sortFuelRun_comparisons_of_le (r : α → α → Prop) [DecidableRel r]
    (xs : List α) (n : Nat) (h : xs.length ≤ n) :
    (sortFuelRun r xs n).2 = (sortRun r xs).2 := by
  rw [sortFuelRun_comparisons, sortRun_comparisons, sizeCost_of_le _ _ h]

/-- Sufficient fuel preserves the whole measured result, not only its value. -/
theorem sortFuelRun_saturated (r : α → α → Prop) [DecidableRel r]
    (xs : List α) (n : Nat) (h : xs.length ≤ n) :
    sortFuelRun r xs n = sortRun r xs := by
  apply Prod.ext
  · rw [sortFuelRun_value, sortRun_value, SourceSelection.sortFuel_saturated r xs n h]
  · exact sortFuelRun_comparisons_of_le r xs n h

/-- A division-free exact count including empty and singleton inputs. -/
theorem sizeCost_double (n : Nat) : 2 * sizeCost n n = n * (n - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [sizeCost_step]
      cases n with
      | zero => rfl
      | succ n =>
          simp only [Nat.add_sub_cancel] at ih ⊢
          nlinarith

theorem sizeCost_exact (n : Nat) : sizeCost n n = n * (n - 1) / 2 := by
  have h := sizeCost_double n
  omega

theorem sortRun_double (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    2 * (sortRun r xs).2 = xs.length * (xs.length - 1) := by
  rw [sortRun_comparisons, sizeCost_double]

theorem sortRun_exact_comparisons (r : α → α → Prop) [DecidableRel r]
    (xs : List α) : (sortRun r xs).2 = xs.length * (xs.length - 1) / 2 := by
  rw [sortRun_comparisons, sizeCost_exact]

/-- Even different relations with equal input lengths have equal comparison
counts. This does not assert equality of their output values. -/
theorem sortFuelRun_same_length (r s : α → α → Prop) [DecidableRel r] [DecidableRel s]
    (xs ys : List α) (n : Nat) (h : xs.length = ys.length) :
    (sortFuelRun r xs n).2 = (sortFuelRun s ys n).2 := by
  rw [sortFuelRun_comparisons, sortFuelRun_comparisons, h]

theorem sizeCost_le_square (n : Nat) : sizeCost n n ≤ n ^ 2 := by
  have h := sizeCost_double n
  have hm := Nat.mul_le_mul_left n (Nat.sub_le n 1)
  nlinarith

theorem square_le_four_sizeCost (n : Nat) (hn : 2 ≤ n) : n ^ 2 ≤ 4 * sizeCost n n := by
  have h := sizeCost_double n
  have hs : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  nlinarith

/-- The exact recurrence gives quadratic comparison growth in both directions
after real casting, with a finite lower-bound threshold of two. -/
theorem sizeCost_isBigO_square :
    Asymptotics.IsBigO Filter.atTop (fun n : Nat => (sizeCost n n : ℝ))
      (fun n : Nat => ((n ^ 2 : Nat) : ℝ)) :=
  Resources.isBigO_of_nat_bound (fun n => sizeCost n n) (fun n => n ^ 2) 1 0
    (fun n _ => by simpa using sizeCost_le_square n)

theorem square_isBigO_sizeCost :
    Asymptotics.IsBigO Filter.atTop (fun n : Nat => ((n ^ 2 : Nat) : ℝ))
      (fun n : Nat => (sizeCost n n : ℝ)) :=
  Resources.isBigO_of_nat_bound (fun n => n ^ 2) (fun n => sizeCost n n) 4 2
    square_le_four_sizeCost

end Resources.SelectionSort
