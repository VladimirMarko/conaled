import Mathlib.Data.Nat.Basic
import Applications.Resources.Measured

/-!
# A measured unary less-than-or-equal comparator

This staged model charges one unit per call of the constructor-pattern
comparison, including the terminal call. It describes the recursion below,
not Lean's native Nat representation, compiler output, or elapsed time.

It addresses the difference-based comparison-cost wording in VFA 2.1,
`Extract.v:65–66` and `SearchTree.v:1290–1292`. No identification with Coq's
`Nat.ltb` (which may add a successor before a less-or-equal comparison) is made.

Instrumentation uses conaled's `Resources.Measured` alias directly. Its
`erasureSquare` packages the actual recursive comparator, and its `bind`/`pure`
compose a two-comparison client without changing the counted primitive.
-/

set_option autoImplicit false
set_option warningAsError true

namespace VFA.Staging.UnaryCosts

/-- Ordinary lockstep unary comparison, with zero compared before successors. -/
def unaryLE : Nat → Nat → Bool
  | 0, _ => true
  | _ + 1, 0 => false
  | n + 1, m + 1 => unaryLE n m

/-- The same recursion, charging one constructor-pattern comparison per call. -/
def unaryLERun : Nat → Nat → Resources.Measured Bool Nat
  | 0, _ => (true, 1)
  | _ + 1, 0 => (false, 1)
  | n + 1, m + 1 =>
      let next := unaryLERun n m
      (next.1, next.2 + 1)

/-- Independent arithmetic meaning of the Boolean comparator. -/
theorem unaryLE_eq_decide (n m : Nat) :
    unaryLE n m = decide (n ≤ m) := by
  induction n generalizing m with
  | zero => simp [unaryLE]
  | succ n ih =>
      cases m with
      | zero => simp [unaryLE]
      | succ m => simpa [unaryLE] using ih m

/-- Instrumentation preserves the actual unmeasured recursive algorithm. -/
theorem unaryLERun_erases (n m : Nat) :
    (unaryLERun n m).1 = unaryLE n m := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
      cases m with
      | zero => rfl
      | succ m => simpa [unaryLERun, unaryLE] using ih m

/-- The measured result is true exactly when the first number is at most the second. -/
theorem unaryLERun_true_iff (n m : Nat) :
    (unaryLERun n m).1 = true ↔ n ≤ m := by
  rw [unaryLERun_erases, unaryLE_eq_decide]
  simp

/-- Exact charged calls, including the final zero-pattern comparison. -/
theorem unaryLERun_steps (n m : Nat) :
    (unaryLERun n m).2 = min n m + 1 := by
  induction n generalizing m with
  | zero => simp [unaryLERun]
  | succ n ih =>
      cases m with
      | zero => simp [unaryLERun]
      | succ m => simp [unaryLERun, ih, Nat.succ_min_succ]

/-- Semantic erasure and exact work are separate components of the same run. -/
theorem unaryLERun_spec (n m : Nat) :
    unaryLERun n m = (decide (n ≤ m), min n m + 1) := by
  apply Prod.ext
  · exact (unaryLERun_erases n m).trans (unaryLE_eq_decide n m)
  · exact unaryLERun_steps n m

/-- Equal inputs have zero difference but arbitrarily many charged calls. -/
theorem equal_inputs_steps (n : Nat) : (unaryLERun n n).2 = n + 1 := by
  simpa using unaryLERun_steps n n

/-- No finite bound depending only on absolute operand difference bounds all calls. -/
theorem no_difference_only_bound (bound : Nat → Nat) :
    ¬ ∀ n m : Nat, (unaryLERun n m).2 ≤ bound ((n - m) + (m - n)) := by
  intro h
  have impossible := h (bound 0) (bound 0)
  have contradiction : bound 0 + 1 ≤ bound 0 := by
    simpa [equal_inputs_steps] using impossible
  exact Nat.not_succ_le_self (bound 0) contradiction

/-- The obstruction remains after excluding every finite initial segment. -/
theorem equal_inputs_beyond_threshold (threshold budget : Nat) :
    ∃ n : Nat, threshold ≤ n ∧ budget < (unaryLERun n n).2 := by
  refine ⟨threshold + budget, ?_, ?_⟩
  · exact Nat.le_add_right threshold budget
  · rw [equal_inputs_steps]
    exact Nat.lt_succ_of_le (Nat.le_add_left budget threshold)

/-- Package the measured recursion through the existing value-erasure interface. -/
def unaryLESquare :
    Squares.Square ⟨Nat × Nat, Nat × Nat, id⟩
      ⟨Resources.Measured Bool Nat, Bool, Prod.fst⟩ :=
  Resources.erasureSquare
    (fun p : Nat × Nat => unaryLERun p.1 p.2)
    (fun p : Nat × Nat => unaryLE p.1 p.2)
    (fun p => unaryLERun_erases p.1 p.2)

/-- A consumer of the shared square obtains the independent arithmetic meaning. -/
theorem unaryLESquare_value (n m : Nat) :
    (unaryLESquare.impl (n, m)).1 = decide (n ≤ m) :=
  (unaryLESquare.commutes (n, m)).trans (unaryLE_eq_decide n m)

/-- Execute both orientations in order, preserving both answers and adding calls.
Both comparisons run regardless of the first answer; pair construction is uncharged. -/
def compareBothWays (n m : Nat) : Resources.Measured (Bool × Bool) Nat :=
  Resources.bind (unaryLERun n m) fun forward =>
    Resources.bind (unaryLERun m n) fun backward =>
      Resources.pure (forward, backward)

/-- Shared bind erasure preserves the order of the two returned answers. -/
theorem compareBothWays_value (n m : Nat) :
    (compareBothWays n m).1 = (unaryLE n m, unaryLE m n) := by
  simp only [compareBothWays, Resources.bind_value, Resources.pure, unaryLERun_erases]

/-- Composed work is the sum of the exact counts of both executed comparisons. -/
theorem compareBothWays_spec (n m : Nat) :
    compareBothWays n m =
      ((decide (n ≤ m), decide (m ≤ n)), (min n m + 1) + (min m n + 1)) := by
  simp only [compareBothWays, unaryLERun_spec, Resources.bind, Resources.pure, Nat.add_zero]

/-! Checked specializations use the public specification, not an independent
reimplementation of the comparator. Four calls compare `(3,3)`, `(2,2)`,
`(1,1)`, and `(0,0)`; a zero in the first call terminates immediately. -/

theorem example_zero_left : unaryLERun 0 7 = (true, 1) := by
  rw [unaryLERun_spec]
  rfl

theorem example_zero_right : unaryLERun 7 0 = (false, 1) := by
  rw [unaryLERun_spec]
  rfl

theorem example_equal_three : unaryLERun 3 3 = (true, 4) := by
  rw [unaryLERun_spec]
  rfl

theorem example_strictly_less : unaryLERun 3 8 = (true, 4) := by
  rw [unaryLERun_spec]
  rfl

theorem example_strictly_greater : unaryLERun 8 3 = (false, 4) := by
  rw [unaryLERun_spec]
  rfl

theorem example_large_equal : (unaryLERun 1000 1000).2 = 1001 :=
  equal_inputs_steps 1000

theorem example_difference_zero :
    (1000 - 1000) + (1000 - 1000) = (0 : Nat) ∧
      (unaryLERun 1000 1000).2 > 1000 := by
  constructor
  · rfl
  · rw [equal_inputs_steps]
    exact Nat.lt_succ_self 1000

/-- This case consumes the square interface, including its commutativity proof. -/
theorem example_square_strictly_greater :
    (unaryLESquare.impl (8, 3)).1 = false := by
  rw [unaryLESquare_value]
  rfl

/-- Four calls in each direction give true/false in that order and eight total calls. -/
theorem example_composed_directions : compareBothWays 3 8 = ((true, false), 8) := by
  rw [compareBothWays_spec]
  rfl

end VFA.Staging.UnaryCosts

#print axioms VFA.Staging.UnaryCosts.unaryLERun_spec
#print axioms VFA.Staging.UnaryCosts.unaryLERun_true_iff
#print axioms VFA.Staging.UnaryCosts.no_difference_only_bound
#print axioms VFA.Staging.UnaryCosts.equal_inputs_beyond_threshold
#print axioms VFA.Staging.UnaryCosts.unaryLESquare_value
#print axioms VFA.Staging.UnaryCosts.compareBothWays_value
#print axioms VFA.Staging.UnaryCosts.compareBothWays_spec
#print axioms VFA.Staging.UnaryCosts.example_composed_directions
