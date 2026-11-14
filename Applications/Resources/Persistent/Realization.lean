import Applications.Resources.Workload
import Mathlib.Data.Finset.Card

/-!
# Interpreting shared debit observations

The existing measured executor retains the support already realized. Each step
charges its unshared work and the newly encountered debit identities. These are
the costs of this explicit debit interpreter; a concrete evaluator needs a
separate work-accounting correspondence.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.Persistent

universe u v w
variable {V : Type u} {D : Type v} [DecidableEq D]

/-- Observe shared identities in an operation list, retaining their union. -/
def realizationSupport (realized : V → Finset D) : List V → Finset D
  | [] => ∅
  | operation :: rest => realized operation ∪ realizationSupport realized rest

/-- One abstract debit step. `seen` records realized work, not prepaid debt. -/
def realizeStep (unshared : V → Nat) (realized : V → Finset D)
    (operation : V) (seen : Finset D) : Measured (Finset D) Nat :=
  (seen ∪ realized operation, unshared operation + (realized operation \ seen).card)

/-- Newly encountered identities account exactly for growth of realized support. -/
theorem realizeStep_balance (unshared : V → Nat) (realized : V → Finset D)
    (operation : V) (seen : Finset D) :
    (realizeStep unshared realized operation seen).2 + seen.card =
      unshared operation + (realizeStep unshared realized operation seen).1.card := by
  change (unshared operation + (realized operation \ seen).card) + seen.card =
    unshared operation + (seen ∪ realized operation).card
  rw [Nat.add_assoc, Finset.card_sdiff_add_card, Finset.union_comm]

/-- State observation of the same measured run, with the initial support retained. -/
theorem realize_run_state (unshared : V → Nat) (realized : V → Finset D)
    (operations : List V) (seen : Finset D) :
    (run (realizeStep unshared realized) operations seen).1 =
      seen ∪ realizationSupport realized operations := by
  induction operations generalizing seen with
  | nil => simp [run, pure, realizationSupport]
  | cons operation rest ih =>
      simp [run_cons, realizeStep, realizationSupport, ih, Finset.union_assoc]

/-- Exact accounting along the actual state trajectory of the debit interpreter.
The list sum counts occurrences; it has not been replaced by a sum over nodes. -/
theorem realize_run_balance (unshared : V → Nat) (realized : V → Finset D)
    (operations : List V) (seen : Finset D) :
    (run (realizeStep unshared realized) operations seen).2 + seen.card =
      (operations.map unshared).sum +
        (run (realizeStep unshared realized) operations seen).1.card := by
  induction operations generalizing seen with
  | nil => simp [run, pure]
  | cons operation rest ih =>
      have first := realizeStep_balance unshared realized operation seen
      have later := ih (realizeStep unshared realized operation seen).1
      simp only [run_cons, List.map_cons, List.sum_cons]
      omega

/-- The initial-support term remains explicit without truncated subtraction. -/
theorem realize_run_identity (unshared : V → Nat) (realized : V → Finset D)
    (operations : List V) (seen : Finset D) :
    (run (realizeStep unshared realized) operations seen).2 + seen.card =
      (operations.map unshared).sum +
        (seen ∪ realizationSupport realized operations).card := by
  rw [← realize_run_state unshared realized operations seen]
  exact realize_run_balance unshared realized operations seen

/-- Empty initial support gives the source's abstract unshared-plus-union count. -/
theorem realize_run_cost (unshared : V → Nat) (realized : V → Finset D)
    (operations : List V) :
    (run (realizeStep unshared realized) operations ∅).2 =
      (operations.map unshared).sum + (realizationSupport realized operations).card := by
  simpa using realize_run_identity unshared realized operations ∅

/-- Previously realized work cannot increase this interpreter's new-work charge. -/
theorem realize_run_cost_le_fresh (unshared : V → Nat) (realized : V → Finset D)
    (operations : List V) (seen : Finset D) :
    (run (realizeStep unshared realized) operations seen).2 ≤
      (run (realizeStep unshared realized) operations ∅).2 := by
  have balance := realize_run_identity unshared realized operations seen
  have unionBound := Finset.card_union_le seen (realizationSupport realized operations)
  rw [realize_run_cost]
  omega

variable {E : Type w} [DecidableEq E]

/-- Injective renaming preserves a step's support and its numerical charge. -/
theorem realizeStep_map (rename : D ↪ E) (unshared : V → Nat)
    (realized : V → Finset D) (operation : V) (seen : Finset D) :
    realizeStep unshared (fun v => (realized v).map rename) operation (seen.map rename) =
      ((realizeStep unshared realized operation seen).1.map rename,
        (realizeStep unshared realized operation seen).2) := by
  simp only [realizeStep, Finset.map_union]
  rw [← Finset.map_sdiff, Finset.card_map]

/-- The same measured run transports through an injective debit renaming. -/
theorem realize_run_map (rename : D ↪ E) (unshared : V → Nat)
    (realized : V → Finset D) (operations : List V) (seen : Finset D) :
    run (realizeStep unshared (fun v => (realized v).map rename)) operations
        (seen.map rename) =
      ((run (realizeStep unshared realized) operations seen).1.map rename,
        (run (realizeStep unshared realized) operations seen).2) := by
  induction operations generalizing seen with
  | nil => simp [run, pure]
  | cons operation rest ih =>
      simp only [run_cons, realizeStep_map]
      rw [ih]

end Resources.Persistent
