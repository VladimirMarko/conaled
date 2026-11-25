import Applications.Resources.CallCount
import Applications.Resources.SymmetricCosts
import Applications.Resources.TreeFlattening.Core
import Mathlib.Tactic.Linarith

/-! Two realizations of list reversal, with the FDSA recursive-call convention.
The naive realization recursively reverses the tail and then appends. The
accumulator realization reuses `SymmetricCosts.reverseRun`. Both erase to
`List.reverse`; their observations are proved separately. No cost claim is made
about the standard library's implementation of `List.reverse`.
Provenance and statement review: `docs/research/fdsa-reconstruction-map.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.ListReversal
universe u
variable {α : Type u}

/-- Convert the existing copied-cell count to the book's call count, including
the final empty-list invocation. This does not change the append algorithm.
-/
def appendRun (xs ys : List α) : Measured (List α) Nat :=
  CallCount.tick (TreeFlattening.appendWithCost xs ys)

theorem appendRun_exact (xs ys : List α) :
    appendRun xs ys = (xs ++ ys, xs.length + 1) := by
  simp [appendRun, TreeFlattening.appendWithCost_exact, CallCount.tick]

theorem appendRun_nil (ys : List α) : appendRun [] ys = (ys, 1) := rfl

theorem appendRun_cons (x : α) (xs ys : List α) :
    appendRun (x :: xs) ys =
      let r := appendRun xs ys
      (x :: r.1, r.2 + 1) := by
  simp [appendRun_exact]

/-- The source's naive reverse: recursive tail reversal followed by append. -/
def naiveRun : List α → Measured (List α) Nat
  | [] => ([], 1)
  | x :: xs =>
      CallCount.tick (bind (naiveRun xs) (fun ys => appendRun ys [x]))

theorem naiveRun_value (xs : List α) : (naiveRun xs).1 = xs.reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [naiveRun, bind, appendRun_exact, ih]

theorem naiveRun_nil : naiveRun ([] : List α) = ([], 1) := rfl

/-- The book's time recurrence retains the append cost as a separate term. -/
theorem naiveRun_cons_cost (x : α) (xs : List α) :
    (naiveRun (x :: xs)).2 =
      (naiveRun xs).2 + (appendRun xs.reverse [x]).2 + 1 := by
  simp [naiveRun, bind, appendRun_exact, naiveRun_value]

/-- A division-free exact form of the chapter's unnumbered exercise. -/
theorem naiveRun_double_cost (xs : List α) :
    2 * (naiveRun xs).2 = (xs.length + 1) * (xs.length + 2) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [naiveRun_cons_cost, appendRun_exact]
      simp only [List.length_reverse, List.length_cons]
      nlinarith

/-- Exact triangular count, with ordinary natural-number division. -/
theorem naiveRun_cost (xs : List α) :
    (naiveRun xs).2 = (xs.length + 1) * (xs.length + 2) / 2 := by
  rw [← naiveRun_double_cost]
  omega

theorem naiveRun_cost_le (xs : List α) :
    (naiveRun xs).2 ≤ (xs.length + 1) ^ 2 := by
  have h := naiveRun_double_cost xs
  nlinarith [Nat.zero_le (xs.length * xs.length)]

/-- The source's accumulator reversal is already present in conaled. -/
theorem accumulator_exact (xs acc : List α) :
    SymmetricCosts.reverseRun xs acc = (xs.reverse ++ acc, xs.length + 1) := by
  apply Prod.ext
  · exact SymmetricCosts.reverseRun_value xs acc
  · exact SymmetricCosts.reverseRun_work xs acc

/-- Same ordered output, including duplicate elements, independently of costs. -/
theorem realizations_agree (xs : List α) :
    (naiveRun xs).1 = (SymmetricCosts.reverseRun xs []).1 := by
  simp [naiveRun_value, SymmetricCosts.reverseRun_value]

/-- The accumulator realization never uses more calls in this particular model. -/
theorem accumulator_cost_le (xs acc : List α) :
    (SymmetricCosts.reverseRun xs acc).2 ≤ (naiveRun xs).2 := by
  rw [SymmetricCosts.reverseRun_work]
  have h := naiveRun_double_cost xs
  nlinarith [Nat.zero_le (xs.length * xs.length)]

/-- The improvement is strict for every nonempty source list. -/
theorem accumulator_cost_lt (xs acc : List α) (hne : xs ≠ []) :
    (SymmetricCosts.reverseRun xs acc).2 < (naiveRun xs).2 := by
  rw [SymmetricCosts.reverseRun_work]
  have hp : 0 < xs.length := List.length_pos_iff.mpr hne
  have h := naiveRun_double_cost xs
  nlinarith [Nat.zero_le (xs.length * xs.length)]

/-- Nonempty reverse/append constructor visits in the same structural reversal.
The removed calls are one terminal reverse call plus one terminal append call
per input element. This observation recovers the archived VFA queue tariff. -/
def constructorVisits (xs : List α) : Nat :=
  (naiveRun xs).2 - (xs.length + 1)

/-- The subtraction in `constructorVisits` loses no count: all terminal calls
are present in the measured recursion. -/
theorem naiveRun_cost_eq_constructorVisits (xs : List α) :
    (naiveRun xs).2 = constructorVisits xs + xs.length + 1 := by
  have lower := accumulator_cost_le xs []
  rw [SymmetricCosts.reverseRun_work] at lower
  unfold constructorVisits
  omega

@[simp] theorem constructorVisits_nil : constructorVisits ([] : List α) = 0 := rfl

/-- The historical tariff charges one nonempty reverse visit and the reversed
tail's nonempty append visits; both terminal invocations cost zero. -/
theorem constructorVisits_cons (x : α) (xs : List α) :
    constructorVisits (x :: xs) = constructorVisits xs + xs.length + 1 := by
  have current := naiveRun_cons_cost x xs
  rw [appendRun_exact] at current
  simp only [List.length_reverse] at current
  have full := naiveRun_cost_eq_constructorVisits (x :: xs)
  have tail := naiveRun_cost_eq_constructorVisits xs
  simp only [List.length_cons] at full
  omega

/-- Exact historical constructor count, without division or truncated subtraction. -/
theorem constructorVisits_double (xs : List α) :
    2 * constructorVisits xs = xs.length * (xs.length + 1) := by
  have calls := naiveRun_double_cost xs
  rw [naiveRun_cost_eq_constructorVisits] at calls
  nlinarith

/-- The measured implementation is usable through the existing semantic square. -/
def naiveSquare : Squares.Square ⟨List α, List α, id⟩
    ⟨Measured (List α) Nat, List α, Prod.fst⟩ :=
  erasureSquare naiveRun List.reverse naiveRun_value

/-- The optimized realization supplies the same specification to square clients. -/
def accumulatorSquare : Squares.Square ⟨List α, List α, id⟩
    ⟨Measured (List α) Nat, List α, Prod.fst⟩ :=
  erasureSquare (fun xs => SymmetricCosts.reverseRun xs []) List.reverse
    (by intro xs; simp [SymmetricCosts.reverseRun_value])

end Resources.ListReversal
