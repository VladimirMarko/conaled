import Mathlib.Logic.Function.Iterate

/-!
# Finite iteration, first-hit execution and terminating loops

`repeat_eq_iterate` connects core fixed-count repetition to the standard
iterator without introducing another executor. It states value equality only.
Its source correspondence is in `docs/research/adwh-finite-correspondence.md`.

`UntilSpec` records a finite execution which stops at the first successful test.
The executor uses an explicit decreasing natural rank; it does not approximate
the loop with fuel. Laws for invariants and state interpretations apply directly
to the relation, including executions constructed by other implementations.

The rank establishes totality, not a runtime or reduction-cost bound. See
`docs/research/adwh-ranked-iteration.md` for provenance and checked uses.
-/
set_option autoImplicit false
set_option warningAsError true
namespace Iteration
universe u
variable {α : Type u}

/-- Core repetition and the standard iterator return the same finite iterate. -/
theorem repeat_eq_iterate (f : α → α) (n : Nat) (x : α) :
    Nat.repeat f n x = f^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact congrArg f ih

inductive UntilSpec (p : α → Bool) (f : α → α) : α → α → Prop
  | stop {x : α} : p x = true → UntilSpec p f x x
  | step {x y : α} : p x = false → UntilSpec p f (f x) y → UntilSpec p f x y

theorem UntilSpec.stopping {p : α → Bool} {f : α → α} {x y : α}
    (h : UntilSpec p f x y) : p y = true := by
  induction h with
  | stop hp => exact hp
  | step _ _ ih => exact ih

/-- An invariant needs preservation only on steps actually taken by the loop. -/
theorem UntilSpec.invariant {p : α → Bool} {f : α → α} (P : α → Prop)
    (preserve : ∀ x, P x → p x = false → P (f x)) {x y : α}
    (h : UntilSpec p f x y) (initial : P x) : P y := by
  induction h with
  | stop _ => exact initial
  | @step x y hp _ ih => exact ih (preserve x initial hp)

/-- Every preceding iterate fails the test; the output is its first successful hit. -/
theorem UntilSpec.first_hit {p : α → Bool} {f : α → α} {x y : α}
    (h : UntilSpec p f x y) :
    ∃ n, y = f^[n] x ∧ p y = true ∧ ∀ k < n, p (f^[k] x) = false := by
  induction h with
  | stop hp =>
    refine ⟨0, rfl, hp, ?_⟩
    intro k hk
    exact False.elim (Nat.not_lt_zero k hk)
  | @step x y hp _ ih =>
    rcases ih with ⟨n, hresult, hstop, hearly⟩
    refine ⟨n + 1, hresult, hstop, ?_⟩
    intro k hk
    cases k with
    | zero => exact hp
    | succ k => exact hearly k (Nat.lt_of_succ_lt_succ hk)

/-- A fixed deterministic step and stopping test have at most one finite result. -/
theorem UntilSpec.unique {p : α → Bool} {f : α → α} {x y z : α}
    (hy : UntilSpec p f x y) (hz : UntilSpec p f x z) : y = z := by
  induction hy generalizing z with
  | stop hp =>
    cases hz with
    | stop _ => rfl
    | step hq _ => simp_all
  | step hp _ ih =>
    cases hz with
    | stop hq => simp_all
    | step _ hz => exact ih hz

/-- Transport a finite execution through a guard-preserving state interpretation.
The step equation is required only when the source actually continues. -/
theorem UntilSpec.map {β : Type*} {p : α → Bool} {q : β → Bool}
    {f : α → α} {g : β → β} (h : α → β)
    (guard : ∀ x, q (h x) = p x)
    (step : ∀ x, p x = false → h (f x) = g (h x)) {x y : α}
    (run : UntilSpec p f x y) : UntilSpec q g (h x) (h y) := by
  induction run with
  | stop hp => exact .stop (by rw [guard]; exact hp)
  | @step x y hp _ ih =>
      apply UntilSpec.step (by rw [guard]; exact hp)
      rw [← step x hp]
      exact ih

/-- Execute until the stopping test succeeds, with a proof of strict progress. -/
def runUntil (p : α → Bool) (f : α → α) (rank : α → Nat)
    (decreases : ∀ x, p x = false → rank (f x) < rank x) (x : α) : α :=
  if _h : p x = true then x else runUntil p f rank decreases (f x)
termination_by rank x
decreasing_by
  apply decreases
  cases hp : p x <;> simp_all

theorem runUntil_spec (p : α → Bool) (f : α → α) (rank : α → Nat)
    (decreases : ∀ x, p x = false → rank (f x) < rank x) (x : α) :
    UntilSpec p f x (runUntil p f rank decreases x) := by
  rw [runUntil]
  split
  · rename_i h
    exact UntilSpec.stop h
  · rename_i h
    have hp : p x = false := by cases hp : p x <;> simp_all
    exact UntilSpec.step hp (runUntil_spec p f rank decreases (f x))
termination_by rank x
decreasing_by exact decreases x hp

theorem runUntil_stops (p : α → Bool) (f : α → α) (rank : α → Nat)
    (decreases : ∀ x, p x = false → rank (f x) < rank x) (x : α) :
    p (runUntil p f rank decreases x) = true :=
  (runUntil_spec p f rank decreases x).stopping

theorem runUntil_invariant (p : α → Bool) (f : α → α) (rank : α → Nat)
    (decreases : ∀ x, p x = false → rank (f x) < rank x) (P : α → Prop)
    (preserve : ∀ x, P x → p x = false → P (f x)) (x : α) (initial : P x) :
    P (runUntil p f rank decreases x) :=
  (runUntil_spec p f rank decreases x).invariant P preserve initial

theorem runUntil_first_hit (p : α → Bool) (f : α → α) (rank : α → Nat)
    (decreases : ∀ x, p x = false → rank (f x) < rank x) (x : α) :
    ∃ n, runUntil p f rank decreases x = f^[n] x ∧
      p (runUntil p f rank decreases x) = true ∧ ∀ k < n, p (f^[k] x) = false :=
  (runUntil_spec p f rank decreases x).first_hit

/-- Termination evidence may vary; first-hit semantics fixes the returned state. -/
theorem runUntil_rank_independent (p : α → Bool) (f : α → α) (r s : α → Nat)
    (hr : ∀ x, p x = false → r (f x) < r x)
    (hs : ∀ x, p x = false → s (f x) < s x) (x : α) :
    runUntil p f r hr x = runUntil p f s hs x :=
  (runUntil_spec p f r hr x).unique (runUntil_spec p f s hs x)

/-- The value of a terminating loop commutes with a compatible interpretation. -/
theorem runUntil_map {β : Type*} (p : α → Bool) (q : β → Bool)
    (f : α → α) (g : β → β) (h : α → β)
    (guard : ∀ x, q (h x) = p x)
    (step : ∀ x, p x = false → h (f x) = g (h x))
    (rank : α → Nat) (targetRank : β → Nat)
    (decreases : ∀ x, p x = false → rank (f x) < rank x)
    (targetDecreases : ∀ x, q x = false → targetRank (g x) < targetRank x) (x : α) :
    h (runUntil p f rank decreases x) = runUntil q g targetRank targetDecreases (h x) :=
  ((runUntil_spec p f rank decreases x).map h guard step).unique
    (runUntil_spec q g targetRank targetDecreases (h x))

/-- The ordinary while convention continues exactly while its test is true. -/
def runWhile (p : α → Bool) (f : α → α) (rank : α → Nat)
    (decreases : ∀ x, p x = true → rank (f x) < rank x) (x : α) : α :=
  runUntil (fun y => !p y) f rank (by intro y hy; exact decreases y (by simpa using hy)) x

theorem runWhile_spec (p : α → Bool) (f : α → α) (rank : α → Nat)
    (decreases : ∀ x, p x = true → rank (f x) < rank x) (x : α) :
    UntilSpec (fun y => !p y) f x (runWhile p f rank decreases x) :=
  runUntil_spec _ _ _ _ _

theorem runWhile_stops (p : α → Bool) (f : α → α) (rank : α → Nat)
    (decreases : ∀ x, p x = true → rank (f x) < rank x) (x : α) :
    p (runWhile p f rank decreases x) = false := by
  simpa using (runWhile_spec p f rank decreases x).stopping

theorem runWhile_invariant (p : α → Bool) (f : α → α) (rank : α → Nat)
    (decreases : ∀ x, p x = true → rank (f x) < rank x) (P : α → Prop)
    (preserve : ∀ x, P x → p x = true → P (f x)) (x : α) (initial : P x) :
    P (runWhile p f rank decreases x) := by
  apply (runWhile_spec p f rank decreases x).invariant P _ initial
  intro y hy hp
  exact preserve y hy (by simpa using hp)

/-- A rank cannot justify continuing at a fixed point. -/
theorem fixed_point_requires_stop (p : α → Bool) (f : α → α) (rank : α → Nat)
    (decreases : ∀ x, p x = false → rank (f x) < rank x) (x : α) (fixed : f x = x) :
    p x = true := by
  cases hp : p x with
  | false =>
      have bad := decreases x hp
      rw [fixed] at bad
      exact False.elim (Nat.lt_irrefl _ bad)
  | true => rfl

theorem identity_loop_has_no_rank (x : α) :
    ¬ ∃ rank : α → Nat, ∀ y, (false : Bool) = false → rank (id y) < rank y := by
  rintro ⟨rank, decreases⟩
  exact Nat.lt_irrefl (rank x) (decreases x rfl)

theorem identity_loop_has_no_result (x y : α) :
    ¬ UntilSpec (fun _ : α => false) id x y := by
  intro h
  have impossible := h.stopping
  cases impossible

end Iteration
