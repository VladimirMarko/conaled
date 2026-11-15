import Std

/-!
# Finite folds with a stopping test

The test is checked before each remaining input. Exhaustion returns the current
state even when the test is false. A simulation transports both the decision to
stop and the state update, only at valid inputs and related reachable states.
This is a finite-value contract; it makes no demand or execution-cost claim.
-/
set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.GuardedFold

universe u v w z
variable {A : Type u} {B : Type v} {S : Type w} {T : Type z}

def run (stop : S → Bool) (step : S → A → S) : S → List A → S
  | state, [] => state
  | state, a :: rest =>
      if stop state then state else run stop step (step state a) rest

/-- A simulation preserves the stopping point as well as the final observation.
The input predicate permits caches whose equations hold only on valid entries.
The transition law is needed only when the source continues. -/
theorem refine (stopS : S → Bool) (stopT : T → Bool)
    (stepS : S → A → S) (stepT : T → B → T) (input : A → B)
    (R : S → T → Prop) (P : A → Prop)
    (stops : ∀ s t, R s t → stopS s = stopT t)
    (steps : ∀ s t a, R s t → P a → stopS s = false →
      R (stepS s a) (stepT t (input a)))
    (xs : List A) (valid : ∀ a ∈ xs, P a)
    (s : S) (t : T) (initial : R s t) :
    R (run stopS stepS s xs) (run stopT stepT t (xs.map input)) := by
  induction xs generalizing s t with
  | nil => exact initial
  | cons a xs ih =>
      have same := stops s t initial
      cases hstop : stopS s with
      | false =>
          have ht : stopT t = false := same.symm.trans hstop
          simp only [run, List.map_cons, hstop, ht, Bool.false_eq_true, ↓reduceIte]
          exact ih (fun x hx => valid x (List.mem_cons_of_mem a hx)) _ _
            (steps s t a initial (valid a List.mem_cons_self) hstop)
      | true =>
          have ht : stopT t = true := same.symm.trans hstop
          simpa only [run, List.map_cons, hstop, ht, ↓reduceIte] using initial

/-- Preservation of an invariant along the actually visited transitions. -/
theorem invariant (stop : S → Bool) (step : S → A → S)
    (P : S → Prop) (Q : A → Prop)
    (closed : ∀ s a, P s → Q a → stop s = false → P (step s a))
    (xs : List A) (valid : ∀ a ∈ xs, Q a) (s : S) (initial : P s) :
    P (run stop step s xs) := by
  induction xs generalizing s with
  | nil => exact initial
  | cons a xs ih =>
      cases hs : stop s with
      | false =>
          simp only [run, hs, Bool.false_eq_true, ↓reduceIte]
          exact ih (fun x hx => valid x (List.mem_cons_of_mem a hx)) _
            (closed s a initial (valid a List.mem_cons_self) hs)
      | true => simpa only [run, hs, ↓reduceIte] using initial

end SquareKit.GuardedFold
