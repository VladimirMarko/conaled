import Applications.Resources.ListReversal

/-! Worked clients of the FDSA call-count laws and two reversal realizations.
Expected results were calculated from the source recurrences independently:
length three gives naive calls 1+2+3+4 = 10 and accumulator calls 4.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ListReversal
open Resources Resources.ListReversal
universe u

theorem empty_counts : naiveRun ([] : List Nat) = ([], 1) ∧
    SymmetricCosts.reverseRun [] [9] = ([9], 1) := by
  constructor
  · exact naiveRun_nil
  · simpa using accumulator_exact ([] : List Nat) [9]

theorem ordered_duplicates :
    naiveRun [2, 1, 2] = ([2, 1, 2], 10) ∧
    SymmetricCosts.reverseRun [2, 1, 2] [] = ([2, 1, 2], 4) := by
  constructor
  · apply Prod.ext
    · simpa using naiveRun_value [2, 1, 2]
    · simpa using naiveRun_cost [2, 1, 2]
  · simpa using accumulator_exact [2, 1, 2] []

/-- Distinct labels distinguish reversal from an identity or a set observation. -/
theorem order_and_accumulator :
    SymmetricCosts.reverseRun [1, 2, 3] [8, 9] = ([3, 2, 1, 8, 9], 4) := by
  simpa using accumulator_exact [1, 2, 3] [8, 9]

theorem singleton_improvement :
    (SymmetricCosts.reverseRun [7] [8]).2 < (naiveRun [7]).2 :=
  accumulator_cost_lt [7] [8] (by decide)

theorem uniform_quadratic_bound {α : Type u} (xs : List α) :
    (naiveRun xs).2 ≤ (xs.length + 1) ^ 2 := naiveRun_cost_le xs

/-- A continuation square retains the first observation when sequencing runs. -/
def accumulatorAfter {α : Type u} : Squares.Square
    ⟨Measured (List α) Nat, List α, Prod.fst⟩
    ⟨Measured (List α) Nat, List α, Prod.fst⟩ where
  impl r := bind r (fun ys => SymmetricCosts.reverseRun ys [])
  spec := List.reverse
  commutes r := by simp [Resources.bind, SymmetricCosts.reverseRun_value]

/-- Pasting the squares proves that two reversals recover the input. -/
theorem composed_square {α : Type u} (xs : List α) :
    ((Squares.compose (accumulatorAfter (α := α)) naiveSquare).impl xs).1 = xs := by
  have h := (Squares.compose (accumulatorAfter (α := α)) naiveSquare).commutes xs
  simpa [Squares.compose, accumulatorAfter, naiveSquare, erasureSquare] using h

theorem composed_run {α : Type u} (xs : List α) :
    (bind (naiveRun xs) (fun ys => SymmetricCosts.reverseRun ys [])).1 = xs := by
  rw [bind_value, SymmetricCosts.reverseRun_value, naiveRun_value]
  simp

/-- Sequencing retains both counts: ten calls followed by four calls. -/
theorem composed_costs :
    (bind (naiveRun [1, 2, 3]) (fun ys => SymmetricCosts.reverseRun ys [])).2 = 14 := by
  simp [Resources.bind, SymmetricCosts.reverseRun_work, naiveRun_value, naiveRun_cost]

theorem append_call_count : appendRun [1, 2] [3, 4] = ([1, 2, 3, 4], 3) := by
  simpa using appendRun_exact [1, 2] [3, 4]

theorem primitive_has_no_extra_charge :
    bind ((3, 4) : Measured Nat Nat) (fun x => pure (x + 2)) = (5, 4) := by
  rw [CallCount.primitive_rule]

theorem call_entry_charged_once :
    CallCount.tick (bind ((3, 4) : Measured Nat Nat) (fun x => pure (x + 2))) = (5, 5) := by
  rw [CallCount.primitive_rule]
  rfl

theorem let_uses_bound_value :
    bind ((3, 2) : Measured Nat Nat) (fun x => (x + 1, x)) = (4, 5) := by
  rw [CallCount.let_rule]
  rfl

theorem arguments_add_costs :
    bind ((3, 2) : Measured Nat Nat)
      (fun a => bind ((4, 5) : Measured Nat Nat) (fun b => (a + b, 7))) = (7, 14) := by
  rw [CallCount.arguments_rule]
  rfl

theorem inactive_branch_uncharged :
    bind ((true, 2) : Measured Bool Nat)
      (fun b => if b then (11, 3) else (99, 1000)) = (11, 5) := by
  rw [CallCount.if_rule _ (fun _ => (11, 3)) (fun _ => (99, 1000))]
  rfl

theorem selected_case_only :
    bind ((Sum.inr 4, 2) : Measured (Nat ⊕ Nat) Nat)
      (Sum.elim (fun x => (x, 1000)) (fun y => (y + 1, 3))) = (5, 5) := by
  rw [CallCount.case_rule]
  rfl

end Examples.ListReversal
