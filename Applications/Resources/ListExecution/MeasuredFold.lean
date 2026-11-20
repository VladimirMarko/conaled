import Applications.Resources.ListExecution
import Applications.Resources.WorkloadBounds
import Mathlib.Algebra.Group.Nat.Defs

/-!
# A right fold with actual measured callbacks

The recursive tail runs before its callback. List entries, callback invocations
and the ordered callback observation are distinct coordinates. Comparing with
the existing left-to-right runner on the reversed list is a theorem, not an
extra reversal performed by this executor.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.ListExecution.MeasuredFold

universe u v w z
variable {α : Type u} {σ : Type v} {C : Type w} {D : Type z}

abbrev Counts := Nat × Nat
abbrev Cost (C : Type w) := Counts × C

def run [Zero C] [Add C] (callback : α → σ → Measured σ C) :
    List α → σ → Measured σ (Cost C)
  | [], seed => (seed, ((1, 0), 0))
  | x :: xs, seed => bind (run callback xs seed) (fun state =>
      reweight (fun cost => ((1, 1), cost)) (callback x state))

@[simp] theorem run_nil [Zero C] [Add C] (callback : α → σ → Measured σ C)
    (seed : σ) : run callback [] seed = (seed, ((1, 0), 0)) := rfl

theorem run_cons [Zero C] [Add C] (callback : α → σ → Measured σ C)
    (x : α) (xs : List α) (seed : σ) :
    run callback (x :: xs) seed =
      let tail := run callback xs seed
      let next := callback x tail.1
      (next.1, ((tail.2.1.1 + 1, tail.2.1.2 + 1), tail.2.2 + next.2)) := rfl

theorem run_value [Zero C] [Add C] (callback : α → σ → Measured σ C)
    (xs : List α) (seed : σ) :
    (run callback xs seed).1 = xs.foldr (fun x state => (callback x state).1) seed := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [run_cons, List.foldr_cons, ih]

theorem run_value_of [Zero C] [Add C] (callback : α → σ → Measured σ C)
    (step : α → σ → σ) (erases : ∀ x state, (callback x state).1 = step x state)
    (xs : List α) (seed : σ) : (run callback xs seed).1 = xs.foldr step seed := by
  rw [run_value]
  simp only [erases]

theorem run_counts [Zero C] [Add C] (callback : α → σ → Measured σ C)
    (xs : List α) (seed : σ) : (run callback xs seed).2.1 = (xs.length + 1, xs.length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [run_cons, List.length_cons]
      have he := congrArg Prod.fst ih
      have hc := congrArg Prod.snd ih
      exact Prod.ext (congrArg (· + 1) he) (congrArg (· + 1) hc)

theorem run_callback [AddMonoid C] (callback : α → σ → Measured σ C)
    (xs : List α) (seed : σ) :
    ((run callback xs seed).1, (run callback xs seed).2.2) =
      Resources.run callback xs.reverse seed := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.reverse_cons, Resources.run_append, ← ih]
      simp only [run_cons, bind, Resources.run_cons, Resources.run_nil, add_zero]

theorem run_invariant_on [AddMonoid C] (callback : α → σ → Measured σ C)
    (allowed : α → Prop) (I : σ → Prop)
    (closed : ∀ x state, allowed x → I state → I (callback x state).1)
    (xs : List α) (inputs : ∀ x ∈ xs, allowed x) (seed : σ) (initial : I seed) :
    I (run callback xs seed).1 := by
  have h := Resources.run_invariant_on callback allowed I closed xs.reverse
    (fun x member => inputs x (List.mem_reverse.mp member)) seed initial
  rw [← run_callback] at h
  exact h

theorem run_callback_work_le_sum (callback : α → σ → Measured σ Nat)
    (allowed : α → Prop) (I : σ → Prop) (weight : α → Nat)
    (closed : ∀ x state, allowed x → I state → I (callback x state).1)
    (bounded : ∀ x state, allowed x → I state → (callback x state).2 ≤ weight x)
    (xs : List α) (inputs : ∀ x ∈ xs, allowed x) (seed : σ) (initial : I seed) :
    (run callback xs seed).2.2 ≤ (xs.map weight).sum := by
  have h := Resources.run_work_le_sum_on callback allowed I weight closed bounded xs.reverse
    (fun x member => inputs x (List.mem_reverse.mp member)) seed initial
  have costs := congrArg Prod.snd (run_callback callback xs seed)
  rw [← costs, List.map_reverse, List.sum_reverse] at h
  exact h

theorem run_callback_work_le (callback : α → σ → Measured σ Nat)
    (allowed : α → Prop) (I : σ → Prop) (bound : Nat)
    (closed : ∀ x state, allowed x → I state → I (callback x state).1)
    (bounded : ∀ x state, allowed x → I state → (callback x state).2 ≤ bound)
    (xs : List α) (inputs : ∀ x ∈ xs, allowed x) (seed : σ) (initial : I seed) :
    (run callback xs seed).2.2 ≤ xs.length * bound := by
  have h := Resources.run_work_le_on callback allowed I bound closed bounded xs.reverse
    (fun x member => inputs x (List.mem_reverse.mp member)) seed initial
  have costs := congrArg Prod.snd (run_callback callback xs seed)
  rw [← costs, List.length_reverse] at h
  exact h

theorem run_reweight [AddMonoid C] [AddMonoid D] (h : C →+ D)
    (callback : α → σ → Measured σ C) (xs : List α) (seed : σ) :
    run (fun x state => reweight h (callback x state)) xs seed =
      reweight (fun cost => (cost.1, h cost.2)) (run callback xs seed) := by
  induction xs with
  | nil => simp [run, reweight]
  | cons x xs ih =>
      simp only [run_cons]
      rw [ih]
      simp only [reweight, map_add]

/-- Recover the earlier pure fold's tariff, which does not price invocations. -/
theorem pure_fold (price : Nat) (step : α → σ → σ) (xs : List α) (seed : σ) :
    reweight (fun cost => cost.1.1 + cost.2)
        (run (fun x state => (step x state, price)) xs seed) =
      ListExecution.foldr price step seed xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      apply Prod.ext
      · simp only [reweight_value, run_cons, ListExecution.foldr, bind_value]
        exact congrArg (step x) (congrArg Prod.fst ih)
      · have h := congrArg Prod.snd ih
        simp only [reweight, run_cons, ListExecution.foldr, bind] at h ⊢
        omega

end Resources.ListExecution.MeasuredFold
