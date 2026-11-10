import SquareKit.Iteration
import Applications.Dijkstra.Target
import Mathlib.Data.Set.Function

/-!
# Checked clients of first-hit and rank-terminating iteration

Countdown and a pair accumulator use the same terminating loop. Projection
transports the pair execution to countdown, while an independent invariant
determines its accumulated result. Existing Dijkstra executions consume the
shared relation's uniqueness law without changing their fuelled implementation.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.RankedIteration

open Iteration

/-- Five additions of two from three visit five, seven, nine, eleven, thirteen. -/
theorem iterate_source_fixture : (fun n : Nat => n + 2)^[5] 3 = 13 := rfl

theorem repeat_source_fixture : Nat.repeat (fun n : Nat => n + 2) 5 3 = 13 :=
  (repeat_eq_iterate _ _ _).trans iterate_source_fixture

/-- The alternate successor orientation comes from the standard iterator. -/
example {α : Type*} (f : α → α) (n : Nat) (x : α) :
    Nat.repeat f (n + 1) x = Nat.repeat f n (f x) := by
  simp only [repeat_eq_iterate, Function.iterate_succ_apply]

example {α : Type*} (f : α → α) (m n : Nat) (x : α) :
    Nat.repeat f (m + n) x = Nat.repeat f m (Nat.repeat f n x) := by
  simp only [repeat_eq_iterate, Function.iterate_add_apply]

/-- Arbitrary predicate preservation is a specialization of `Set.MapsTo.iterate`. -/
example {α : Type*} (f : α → α) (P : α → Prop)
    (step : ∀ y, P y → P (f y)) (n : Nat) (x : α) (initial : P x) :
    P (Nat.repeat f n x) := by
  rw [repeat_eq_iterate]
  have preserve : Set.MapsTo f { y | P y } { y | P y } := fun _ hy => step _ hy
  exact preserve.iterate n initial

def zero (n : Nat) : Bool := n == 0

theorem pred_decreases (n : Nat) (h : zero n = false) : n.pred < n := by
  cases n with
  | zero => simp [zero] at h
  | succ n => exact Nat.lt_succ_self n

def countdown (n : Nat) : Nat := runUntil zero Nat.pred id pred_decreases n

theorem countdown_eq_zero (n : Nat) : countdown n = 0 := by
  have stop := runUntil_stops zero Nat.pred id pred_decreases n
  simpa only [countdown, zero, beq_iff_eq] using stop

/-- A larger rank proves the same result without changing first-hit semantics. -/
theorem countdown_other_rank (n : Nat) :
    countdown n =
      runUntil zero Nat.pred (fun k => 2 * k + 7)
        (fun k hk => by have := pred_decreases k hk; omega) n :=
  runUntil_rank_independent zero Nat.pred id (fun k => 2 * k + 7)
    pred_decreases (fun k hk => by have := pred_decreases k hk; omega) n

def threshold (n : Nat) : Bool := decide (n ≤ 3)

theorem threshold_decreases (n : Nat) (h : threshold n = false) : n.pred < n := by
  have hn : ¬ n ≤ 3 := by simpa [threshold] using h
  cases n with
  | zero => omega
  | succ n => exact Nat.lt_succ_self n

/-- Six, five and four fail; three succeeds even though zero would also succeed. -/
theorem threshold_trace : UntilSpec threshold Nat.pred 6 3 :=
  .step rfl (.step rfl (.step rfl (.stop rfl)))

theorem threshold_first_result : runUntil threshold Nat.pred id threshold_decreases 6 = 3 :=
  (runUntil_spec threshold Nat.pred id threshold_decreases 6).unique threshold_trace

theorem threshold_first_hit :
    ∃ n, (3 : Nat) = Nat.pred^[n] 6 ∧ threshold 3 = true ∧
      ∀ k < n, threshold (Nat.pred^[k] 6) = false := by
  simpa only [threshold_first_result] using
    runUntil_first_hit threshold Nat.pred id threshold_decreases 6

/-- Starting at a successful guard performs no step. -/
theorem threshold_initial_stop : runUntil threshold Nat.pred id threshold_decreases 2 = 2 :=
  (runUntil_spec threshold Nat.pred id threshold_decreases 2).unique (.stop rfl)

def transferStep (s : Nat × Nat) : Nat × Nat := (s.1.pred, s.2 + 1)

theorem transfer_decreases (s : Nat × Nat) (h : zero s.1 = false) :
    (transferStep s).1 < s.1 := pred_decreases s.1 h

def transfer (n total : Nat) : Nat × Nat :=
  runUntil (fun s => zero s.1) transferStep Prod.fst transfer_decreases (n, total)

/-- Projection is a state interpretation; the accumulator does not affect control. -/
theorem transfer_remaining (n total : Nat) : (transfer n total).1 = 0 := by
  have projection := runUntil_map (fun s : Nat × Nat => zero s.1) zero
    transferStep Nat.pred Prod.fst (fun _ => rfl) (fun _ _ => rfl)
    Prod.fst id transfer_decreases pred_decreases (n, total)
  exact projection.trans (countdown_eq_zero n)

theorem transfer_preserves (budget : Nat) (s : Nat × Nat)
    (h : s.1 + s.2 = budget) (go : zero s.1 = false) :
    (transferStep s).1 + (transferStep s).2 = budget := by
  have positive : s.1 ≠ 0 := by simpa [zero] using go
  simp only [transferStep, Nat.pred_eq_sub_one]
  omega

theorem transfer_conserved (n total : Nat) :
    (transfer n total).1 + (transfer n total).2 = n + total :=
  runUntil_invariant (fun s => zero s.1) transferStep Prod.fst transfer_decreases
    (fun s => s.1 + s.2 = n + total) (transfer_preserves (n + total)) (n, total) rfl

theorem transfer_result (n total : Nat) : transfer n total = (0, n + total) := by
  apply Prod.ext
  · exact transfer_remaining n total
  · have h := transfer_conserved n total
    simpa only [transfer_remaining, Nat.zero_add] using h

def transferWhile (n total : Nat) : Nat × Nat :=
  runWhile (fun s => !zero s.1) transferStep Prod.fst
    (fun s hs => transfer_decreases s (by simpa using hs)) (n, total)

/-- The complement convention of while agrees with the until implementation. -/
theorem transfer_while_eq (n total : Nat) : transferWhile n total = transfer n total := by
  have run := runWhile_spec (fun s : Nat × Nat => !zero s.1) transferStep Prod.fst
    (fun s hs => transfer_decreases s (by simpa using hs)) (n, total)
  have run' : UntilSpec (fun s => zero s.1) transferStep (n, total)
      (transferWhile n total) := by
    simpa only [transferWhile, Bool.not_not] using run
  exact run'.unique (runUntil_spec _ _ _ _ _)

theorem transfer_while_conserved (n total : Nat) :
    (transferWhile n total).1 + (transferWhile n total).2 = n + total := by
  apply runWhile_invariant (fun s : Nat × Nat => !zero s.1) transferStep Prod.fst
    (fun s hs => transfer_decreases s (by simpa using hs))
    (fun s => s.1 + s.2 = n + total) _ (n, total) rfl
  intro s hs hp
  exact transfer_preserves (n + total) s hs (by simpa using hp)

theorem transfer_example : transfer 4 7 = (0, 11) := transfer_result 4 7

theorem transfer_empty : transferWhile 0 7 = (0, 7) := by
  rw [transfer_while_eq, transfer_result]

theorem divergent_identity_has_no_rank :
    ¬ ∃ rank : Nat → Nat, ∀ n, (false : Bool) = false → rank (id n) < rank n :=
  identity_loop_has_no_rank (0 : Nat)

theorem divergent_identity_has_no_result :
    ¬ UntilSpec (fun _ : Nat => false) id 3 3 :=
  identity_loop_has_no_result 3 3

/-- Both results come from the existing Dijkstra executor, possibly with
different fuel. Its established first-hit contract suffices for equality. -/
theorem dijkstra_successful_results_unique {n : Nat} (wa : Dijkstra.Core.Weights n)
    (target : Fin n) (m k : Nat) (s out₁ out₂ : Dijkstra.Core.State n)
    (first : Dijkstra.Target.untilTarget wa target m s = some out₁)
    (second : Dijkstra.Target.untilTarget wa target k s = some out₂) : out₁ = out₂ :=
  (Dijkstra.Target.untilTarget_spec wa target m s out₁ first).unique
    (Dijkstra.Target.untilTarget_spec wa target k s out₂ second)

end Examples.RankedIteration
