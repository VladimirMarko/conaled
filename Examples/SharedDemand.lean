import Applications.Resources.CallCount
import Applications.Resources.SharedDemand

/-! Connected cases for the qualified shared-demand interpretation of FDSA
chapter 1. Independent expected calculations: five demands for a cost-3 callback
cost 3; leaving a cost-1000 callback unused leaves 1000 units of potential; four
layers of a duplicated recursive result return 16 with 5 shared entries versus
31 unshared entries. These observations describe the defined measured
computations, not an inferred cost semantics for Lean's implementation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SharedDemand
open Resources Resources.SharedDemand
universe u
variable {α : Type u}

/-- Operation and repetition need neither finite identities nor payload equality. -/
theorem arbitrary_payload_repetition (a : α) (work n : Nat) :
    (run (step (fun (_ : Nat) (_ : Unit) => (a, work)))
      (List.replicate (n + 1) 12) empty).2 = work := by
  exact congrArg Prod.snd
    (run_replicate_empty (fun (_ : Nat) (_ : Unit) => (a, work)) 12 n)

/-- Equal payloads do not merge distinct identities: the two misses cost 3 + 5,
and the final request reuses only the first identity's stored computation. -/
theorem equal_values_keep_identities (a : α) :
    let compute : Bool → Unit → Measured α Nat :=
      fun i _ => (a, if i then 5 else 3)
    (run (step compute) [false, true, false] empty).2 = 8 := by
  rfl

private def catalogue (i : Bool) (_ : Unit) : Measured Nat Nat :=
  if i then (99, 1000) else (7, 3)

theorem eager_total : (∑ i, (catalogue i ()).2) = 1003 := by decide

theorem repeat_cheap_cost :
    (run (step catalogue) (List.replicate 5 false) empty).2 = 3 := by
  exact congrArg Prod.snd (run_replicate_empty catalogue false 4)

/-- All demand traces fit the same finite eager catalogue, including repeats. -/
theorem catalogue_bound (requests : List Bool) :
    (run (step catalogue) requests empty).2 ≤ 1003 := by
  calc
    (run (step catalogue) requests empty).2 ≤ ∑ i, (catalogue i ()).2 :=
      run_cost_le_eager catalogue requests
    _ = 1003 := eager_total

/-- The skipped callback has no stored value and retains its full work budget. -/
theorem unused_expensive :
    (run (step catalogue) (List.replicate 5 false) empty).1 true = none ∧
      remaining catalogue (run (step catalogue) (List.replicate 5 false) empty).1 =
        1000 := by
  constructor
  · simpa [Resources.SharedDemand.empty] using congrArg
      (fun r : Measured (Cache Bool Nat) Nat => r.1 true)
      (run_replicate_empty catalogue false 4)
  · have accounting := run_work_remaining catalogue (List.replicate 5 false) empty
    have initial : remaining catalogue empty = 1003 := by
      rw [remaining_empty]
      exact eager_total
    rw [repeat_cheap_cost, initial] at accounting
    omega

/-- The next demanded value agrees with eager evaluation after every prefix,
including prefixes in which that same identity was already requested. -/
theorem demanded_values (requests : List Bool) :
    (request catalogue false (run (step catalogue) requests empty).1).1.2 = 7 ∧
      (request catalogue true (run (step catalogue) requests empty).1).1.2 = 99 :=
  ⟨request_after_run_value catalogue requests false empty (empty_valid catalogue),
    request_after_run_value catalogue requests true empty (empty_valid catalogue)⟩

/-- Intervening demands for any identities do not make a stored callback run again. -/
theorem repeat_after_arbitrary_requests (requests : List Bool) :
    let initial := (request catalogue false empty).1.1
    let final := (run (step catalogue) requests initial).1
    request catalogue false final = ((final, 7), 0) := by
  dsimp only
  apply request_hit
  apply run_preserves_cached
  simp [request_miss catalogue false empty rfl, catalogue]

theorem empty_requests : run (step catalogue) [] empty = (empty, 0) := run_nil _ _

private def noComputations : Empty → Unit → Measured Empty Nat := fun i => nomatch i

/-- Neither the eager catalogue nor the payload type needs an inhabitant. -/
theorem empty_catalogue (requests : List Empty) :
    (run (step noComputations) requests empty).2 = 0 := by
  have bound := run_cost_le_eager noComputations requests
  have total : (∑ i, (noComputations i ()).2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact Empty.elim i
  rw [total] at bound
  omega

namespace Duplication

/-- The body demands one pure child twice under the same sharing identity.
The enclosing recursive entry adds one tick after both demands. -/
def sharedLayer (child : Unit → Measured Nat Nat) : Measured Nat Nat :=
  CallCount.tick <|
    bind (request (fun (_ : Unit) => child) () empty) fun first =>
      bind (request (fun (_ : Unit) => child) () first.1) fun second =>
        pure (first.2 + second.2)

theorem sharedLayer_eq (child : Unit → Measured Nat Nat) :
    sharedLayer child = (2 * (child ()).1, (child ()).2 + 1) := by
  have hit : (Function.update (empty : Cache Unit Nat) () (some (child ()).1)) () =
      some (child ()).1 := by simp
  simp only [sharedLayer,
    request_miss (fun (_ : Unit) => child) () empty rfl, Resources.bind,
    request_hit (fun (_ : Unit) => child) () _ _ hit, Resources.pure, CallCount.tick,
    Nat.add_zero]
  congr 1
  omega

/-- The shared layer has exactly the value and work of an eager let binding:
evaluate the child once, then use its returned value twice. -/
theorem sharedLayer_eager (child : Unit → Measured Nat Nat) :
    sharedLayer child =
      CallCount.tick (bind (child ()) (fun a => pure (a + a))) := by
  rw [sharedLayer_eq, CallCount.primitive_rule]
  simp only [CallCount.tick]
  congr 1
  omega

/-- The unshared interpretation evaluates the child afresh at each occurrence.
The two measured binds therefore both contribute the child's work. -/
def unsharedLayer (child : Unit → Measured Nat Nat) : Measured Nat Nat :=
  CallCount.tick <|
    bind (child ()) fun first =>
      bind (child ()) fun second => pure (first + second)

theorem unsharedLayer_eq (child : Unit → Measured Nat Nat) :
    unsharedLayer child = (2 * (child ()).1, 2 * (child ()).2 + 1) := by
  simp only [unsharedLayer, Resources.bind, Resources.pure, CallCount.tick, Nat.add_zero]
  congr 1 <;> omega

/-- Iterating the actual shared-cache layer, with one terminal entry at zero. -/
def shared : Nat → Measured Nat Nat
  | 0 => CallCount.tick (pure 1)
  | n + 1 => sharedLayer (fun _ => shared n)

/-- Iterating the two-evaluation layer with the same terminal computation. -/
def unshared : Nat → Measured Nat Nat
  | 0 => CallCount.tick (pure 1)
  | n + 1 => unsharedLayer (fun _ => unshared n)

theorem shared_exact (n : Nat) : shared n = (2 ^ n, n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [shared, sharedLayer_eq, ih, Nat.pow_succ, Nat.mul_comm]

theorem unshared_value (n : Nat) : (unshared n).1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [unshared, unsharedLayer_eq, ih, Nat.pow_succ, Nat.mul_comm]

/-- The successor equation avoids concealing natural subtraction at zero. -/
theorem unshared_cost_add_one (n : Nat) : (unshared n).2 + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [unshared, unsharedLayer_eq]
      change (2 * (unshared n).2 + 1) + 1 = 2 ^ ((n + 1) + 1)
      rw [Nat.pow_succ]
      omega

theorem unshared_exact (n : Nat) : unshared n = (2 ^ n, 2 ^ (n + 1) - 1) := by
  apply Prod.ext
  · exact unshared_value n
  · have count := unshared_cost_add_one n
    omega

theorem same_values (n : Nat) : (shared n).1 = (unshared n).1 := by
  rw [shared_exact, unshared_exact]

theorem four_layers : shared 4 = (16, 5) ∧ unshared 4 = (16, 31) :=
  ⟨shared_exact 4, unshared_exact 4⟩

end Duplication
end Examples.SharedDemand
