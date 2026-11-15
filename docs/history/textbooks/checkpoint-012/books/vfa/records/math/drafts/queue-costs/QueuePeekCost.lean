import Batteries.Data.List.Lemmas
import Applications.Resources.Potential

/-!
# Staged traversal counterexample for VFA's observing two-list queue peek

The source is VFA 2.1, ADT.v, TwoListQueueAbs (1078–1141), especially
enq (1097–1098) and peek (1111–1120). The operation returns a value, not a
normalized queue. The staged cost is an explicit count of nonempty list
constructor visits in structural reverse and append. It is not a claim about
compiled running time, garbage collection, allocation, or memoization.

The value specification and the size lower bound are independent of the
instrumented recursions. The counterexample uses only the lower bound and
unchanged queue state; it does not rely on a quadratic closed-form claim.
This file deliberately does not implement the other queue operations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Resources.QueuePeekDraft

universe u
variable {α : Type u}

abbrev Queue (α : Type u) := List α × List α

/-- Source value representation, generalized from natural numbers. -/
def denote (q : Queue α) : List α := q.1 ++ q.2.reverse

def empty : Queue α := ([], [])

/-- Exactly the source enqueue state transition. -/
def enqueue (q : Queue α) (v : α) : Queue α := (q.1, v :: q.2)

/-- The source's three cases, expressed using Lean's default-valued head. -/
def peek (d : α) : Queue α → α
  | ([], []) => d
  | ([], b) => b.reverse.headD d
  | (v :: _, _) => v

theorem peek_relate (d : α) (q : Queue α) :
    peek d q = (denote q).headD d := by
  rcases q with ⟨f, b⟩
  cases f with
  | nil => cases b <;> simp [peek, denote]
  | cons v f => simp [peek, denote]

/-- States obtained by finitely many of the source enqueue operations. -/
inductive EnqueueReachable : Queue α → Prop
  | empty : EnqueueReachable empty
  | enqueue {q : Queue α} : EnqueueReachable q →
      (v : α) → EnqueueReachable (enqueue q v)

def enqueueCopies (v : α) : Nat → Queue α
  | 0 => empty
  | n + 1 => enqueue (enqueueCopies v n) v

theorem enqueueCopies_reachable (v : α) (n : Nat) :
    EnqueueReachable (enqueueCopies v n) := by
  induction n with
  | zero => exact EnqueueReachable.empty
  | succ n ih => exact EnqueueReachable.enqueue ih v

theorem enqueueCopies_shape (v : α) (n : Nat) :
    enqueueCopies v n = ([], List.replicate n v) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [enqueueCopies, enqueue, ih, List.replicate_succ]

/-- Independent size specification: a full reversal of the back list has at
least this many input-cons visits. Nonempty-front peeks do not reverse. -/
def peekReversalInputBound : Queue α → Nat
  | ([], b) => b.length
  | (_ :: _, _) => 0

/-- Instrumentation counts one visit for each nonempty first-argument node.
The result is ordinary append; each visit adds one to the observation. -/
def appendMeasured : List α → List α → List α × Nat
  | [], ys => (ys, 0)
  | x :: xs, ys =>
      let r := appendMeasured xs ys
      (x :: r.1, r.2 + 1)

theorem appendMeasured_value (xs ys : List α) :
    (appendMeasured xs ys).1 = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [appendMeasured, ih]

theorem appendMeasured_cost (xs ys : List α) :
    (appendMeasured xs ys).2 = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [appendMeasured, ih]

/-- Structural reverse, with the append traversal also observed. This is a
particular costed implementation with source reverse's value semantics.
One additional visit is charged for each nonempty reverse input node. -/
def reverseMeasured : List α → List α × Nat
  | [] => ([], 0)
  | x :: xs =>
      let r := reverseMeasured xs
      let a := appendMeasured r.1 [x]
      (a.1, r.2 + a.2 + 1)

theorem reverseMeasured_value (xs : List α) :
    (reverseMeasured xs).1 = xs.reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [reverseMeasured, appendMeasured_value, ih, List.reverse_cons]

/-- The recurrence follows from the two instrumented algorithms and their
erasure proofs; it is not used as the definition of measured cost. -/
theorem reverseMeasured_cost_cons (x : α) (xs : List α) :
    (reverseMeasured (x :: xs)).2 =
      (reverseMeasured xs).2 + xs.length + 1 := by
  simp [reverseMeasured, appendMeasured_cost, reverseMeasured_value]

theorem reverseMeasured_cost_lower (xs : List α) :
    xs.length ≤ (reverseMeasured xs).2 := by
  induction xs with
  | nil => simp [reverseMeasured]
  | cons x xs ih =>
      rw [reverseMeasured_cost_cons]
      simp only [List.length_cons]
      omega

/-- Source peek with an explicit measured reversal in its empty-front branch.
The resulting value is projected separately from the observation. -/
def peekMeasured (d : α) : Queue α → α × Nat
  | ([], []) => (d, 0)
  | ([], b) =>
      let r := reverseMeasured b
      (r.1.headD d, r.2)
  | (v :: _, _) => (v, 0)

theorem peekMeasured_value (d : α) (q : Queue α) :
    (peekMeasured d q).1 = peek d q := by
  rcases q with ⟨f, b⟩
  cases f with
  | nil => cases b <;> simp [peekMeasured, peek, reverseMeasured_value]
  | cons v f => rfl

theorem peekMeasured_relate (d : α) (q : Queue α) :
    (peekMeasured d q).1 = (denote q).headD d := by
  rw [peekMeasured_value, peek_relate]

theorem peekMeasured_cost_lower (d : α) (q : Queue α) :
    peekReversalInputBound q ≤ (peekMeasured d q).2 := by
  rcases q with ⟨f, b⟩
  cases f with
  | nil =>
      cases b with
      | nil => simp [peekReversalInputBound, peekMeasured]
      | cons v b => exact reverseMeasured_cost_lower (v :: b)
  | cons v f => simp [peekReversalInputBound, peekMeasured]

theorem enqueueCopies_peek_lower (d v : α) (n : Nat) :
    n ≤ (peekMeasured d (enqueueCopies v n)).2 := by
  have h := peekMeasured_cost_lower d (enqueueCopies v n)
  simpa [enqueueCopies_shape, peekReversalInputBound] using h

/-- State/observation adapter for Resources.run: reading does not install the
reversed front list. The observed value is already linked by peekMeasured_value. -/
def peekStep (d : α) (q : Queue α) : Queue α × Nat :=
  (q, (peekMeasured d q).2)

theorem peekStep_state (d : α) (q : Queue α) : (peekStep d q).1 = q := rfl

/-- Recursively sequence the actual observed step, threading its resulting state.
This is the Nat-indexed specialization of Resources.run to repeated unit input. -/
def runPeeks (d : α) : Nat → Queue α → Queue α × Nat
  | 0, q => (q, 0)
  | n + 1, q =>
      let s := peekStep d q
      let r := runPeeks d n s.1
      (r.1, s.2 + r.2)

theorem runPeeks_state (d : α) (n : Nat) (q : Queue α) :
    (runPeeks d n q).1 = q := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [runPeeks, peekStep] using ih

/-- Exact repeated-step cost is derived from the executor recurrence. -/
theorem runPeeks_cost (d : α) (n : Nat) (q : Queue α) :
    (runPeeks d n q).2 = n * (peekMeasured d q).2 := by
  induction n with
  | zero => simp [runPeeks]
  | succ n ih => simp [runPeeks, peekStep, ih, Nat.succ_mul, Nat.add_comm]

theorem runPeeks_lower (d v : α) (n repetitions : Nat) :
    repetitions * n ≤ (runPeeks d repetitions (enqueueCopies v n)).2 := by
  rw [runPeeks_cost]
  exact Nat.mul_le_mul_left repetitions (enqueueCopies_peek_lower d v n)

/-- The staged executor is the actual conaled measured workload executor on
repeated unit inputs, including both the queue state and observation. -/
theorem runPeeks_eq_resourcesRun (d : α) (n : Nat) (q : Queue α) :
    runPeeks d n q =
      _root_.Resources.run (fun _ : Unit => peekStep d) (List.replicate n ()) q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
      simp only [runPeeks, List.replicate_succ, _root_.Resources.run_cons, ← ih]

/-- Charge the actual measured traversal at each state. The existing potential
accounting API gives exact accounting; this charge is not uniformly constant. -/
theorem resources_exact_accounting (potential : Queue α → Nat) (d : α)
    (inputs : List Unit) (q : Queue α) :
    (_root_.Resources.run (fun _ : Unit => peekStep d) inputs q).2 +
        potential (_root_.Resources.run (fun _ : Unit => peekStep d) inputs q).1 =
      potential q + _root_.Resources.budget (fun _ : Unit => peekStep d)
        (fun _ s => (peekMeasured d s).2) inputs q := by
  apply _root_.Resources.run_potential_exact
  intro _ s
  simp only [peekStep, Nat.add_comm]

/-- Exact unchanged-state specialization of Resources.run_potential's local
inequality. A state-only potential cannot reduce a self-loop's required charge. -/
theorem unchanged_potential_iff (potential cost charge : Nat) :
    cost + potential ≤ potential + charge ↔ cost ≤ charge := by omega

theorem peek_potential_iff (potential : Queue α → Nat) (d : α)
    (q : Queue α) (charge : Nat) :
    (peekStep d q).2 + potential (peekStep d q).1 ≤ potential q + charge ↔
      (peekMeasured d q).2 ≤ charge := by
  exact unchanged_potential_iff (potential q) (peekMeasured d q).2 charge

/-- For every proposed constant, enqueue from empty gives a reachable witness
whose observing peek cannot obey that charge with any state-only potential. -/
theorem no_uniform_local_charge (potential : Queue α → Nat) (d v : α) :
    ¬ ∃ charge : Nat, ∀ q : Queue α, EnqueueReachable q →
      (peekStep d q).2 + potential (peekStep d q).1 ≤ potential q + charge := by
  rintro ⟨charge, bound⟩
  have hc := (peek_potential_iff potential d (enqueueCopies v (charge + 1)) charge).mp
    (bound _ (enqueueCopies_reachable v (charge + 1)))
  have hl := enqueueCopies_peek_lower d v (charge + 1)
  omega

/-- Both boundary potentials cancel because the repeated observations preserve
the entire state. This is the exact shape of Resources.run_constant_charge. -/
theorem runPeeks_potential_iff (potential : Queue α → Nat) (d : α)
    (q : Queue α) (repetitions charge : Nat) :
    (runPeeks d repetitions q).2 + potential (runPeeks d repetitions q).1 ≤
        potential q + charge * repetitions ↔
      (runPeeks d repetitions q).2 ≤ charge * repetitions := by
  rw [runPeeks_state]
  exact unchanged_potential_iff (potential q) _ _

/-- Even if a proposed bound drops the final potential and grants all the
initial credit, a sufficiently long sequence on a fixed reachable queue
exceeds that credit plus a uniform constant charge per observation. -/
theorem repeated_peeks_exhaust_initial_credit
    (potential : Queue α → Nat) (d v : α) (charge : Nat) :
    ∃ q : Queue α, EnqueueReachable q ∧ ∃ repetitions : Nat,
      0 < repetitions ∧
      potential q + charge * repetitions < (runPeeks d repetitions q).2 := by
  let q := enqueueCopies v (charge + 1)
  let repetitions := potential q + 1
  refine ⟨q, enqueueCopies_reachable v (charge + 1), repetitions, ?_, ?_⟩
  · dsimp [repetitions]
    omega
  · have hl := runPeeks_lower d v (charge + 1) repetitions
    have hs : potential q + charge * repetitions < repetitions * (charge + 1) := by
      rw [Nat.mul_add repetitions charge 1, Nat.mul_one repetitions,
        Nat.mul_comm repetitions charge]
      dsimp [repetitions]
      omega
    exact Nat.lt_of_lt_of_le hs hl

/-- The same reachable counterexample consumes conaled's actual run and budget
interfaces. Even all initial credit cannot fund arbitrary repeated peeks at a
uniform constant charge. -/
theorem resources_peeks_exhaust_initial_credit
    (potential : Queue α → Nat) (d v : α) (charge : Nat) :
    ∃ q : Queue α, EnqueueReachable q ∧ ∃ repetitions : Nat,
      0 < repetitions ∧
      potential q + _root_.Resources.budget (fun _ : Unit => peekStep d)
          (fun _ _ => charge) (List.replicate repetitions ()) q <
        (_root_.Resources.run (fun _ : Unit => peekStep d)
          (List.replicate repetitions ()) q).2 := by
  obtain ⟨q, hq, repetitions, positive, exceeds⟩ :=
    repeated_peeks_exhaust_initial_credit potential d v charge
  refine ⟨q, hq, repetitions, positive, ?_⟩
  simpa only [_root_.Resources.budget_constant, List.length_replicate,
    ← runPeeks_eq_resourcesRun] using exceeds

end Applications.Resources.QueuePeekDraft

namespace Examples.QueuePeekCostDraft

open Applications.Resources.QueuePeekDraft

/-- Nontrivial value order: enqueue 4, 9, 2 keeps reversed back storage. -/
theorem enqueue_order_and_peek :
    let q := enqueue (enqueue (enqueue (empty : Queue Nat) 4) 9) 2
    EnqueueReachable q ∧ q = ([], [2, 9, 4]) ∧
      peek 99 q = 4 ∧ peekMeasured 99 q = (4, 6) ∧
      runPeeks 99 3 q = (q, 18) := by
  refine ⟨?_, ?_⟩
  · exact EnqueueReachable.enqueue
      (EnqueueReachable.enqueue
        (EnqueueReachable.enqueue EnqueueReachable.empty 4) 9) 2
  · decide

theorem empty_observation :
    peekMeasured 99 (empty : Queue Nat) = (99, 0) ∧
      runPeeks 99 4 empty = (empty, 0) := by decide

/-- A nonempty front does not inspect the back, even if it is nonempty. -/
theorem front_observation :
    peekMeasured 99 ([4, 9], [2, 7, 8]) = (4, 0) ∧
      runPeeks 99 3 ([4, 9], [2, 7, 8]) = (([4, 9], [2, 7, 8]), 0) := by decide

/-- Arbitrarily large stored credit does not reduce a self-loop's local charge. -/
theorem stored_credit_cancels :
    ¬ ((peekStep 99 (enqueueCopies 4 3)).2 + 1000 ≤ 1000 + 2) := by decide

/-- Concrete reusable-client consequence: the tempting back-length potential
cannot justify a uniform constant observing-peek charge. -/
theorem back_length_potential_fails :
    ¬ ∃ charge : Nat, ∀ q : Queue Nat, EnqueueReachable q →
      (peekStep 0 q).2 + (peekStep 0 q).1.2.length ≤ q.2.length + charge := by
  exact no_uniform_local_charge (fun q : Queue Nat => q.2.length) 0 7

/-- A connected existing-workload client: the source enqueue example observes
18 visits through Resources.run, while its constant-charge budget is 6 and
even the additional initial back-length credit is insufficient. -/
theorem resource_workload_observation :
    let q := enqueue (enqueue (enqueue (empty : Queue Nat) 4) 9) 2
    let step : Unit → Queue Nat → _root_.Resources.Measured (Queue Nat) Nat :=
      fun _ => peekStep 99
    let inputs := List.replicate 3 ()
    _root_.Resources.run step inputs q = (q, 18) ∧
      _root_.Resources.budget step (fun _ _ => 2) inputs q = 6 ∧
      q.2.length + _root_.Resources.budget step (fun _ _ => 2) inputs q <
        (_root_.Resources.run step inputs q).2 := by
  dsimp only
  rw [← runPeeks_eq_resourcesRun, enqueue_order_and_peek.2.2.2.2,
    _root_.Resources.budget_constant]
  decide

end Examples.QueuePeekCostDraft
