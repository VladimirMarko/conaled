import Applications.Sequences.SourceQueue
import Applications.Resources.ListAppend
import Applications.Resources.ListReversal
import Applications.Resources.FIFOContracts

/-!
# Source queue executions and their separate work models

The VFA ADT pair queue leaves every observing peek's state unchanged. Both
measured realizations below retain its three source branches, including the
truly empty branch that never reverses. Their reversal callback returns the
list actually used by the queue operation. The source structural reversal
uses ListReversal.naiveRun; the distinct linear realization uses the existing
accumulator reverseRun. Each queue invocation adds one dispatch unit.

Structural reversal counts recursive reverse and append entries, including
their terminating nil entries. Linear reversal counts accumulator entries.
These are explicit abstract models, not claims about Coq extraction, Lean
native execution, allocation, physical sharing, or stack usage.

The positive constant-charge theorem concerns sequential enqueue/dequeue
histories in the linear realization, with initial and final back-list credit.
It excludes observing peek. Repeated peeks execute the same costly reversal
again: no state-only potential gives a uniform local charge, and even an
arbitrary finite initial credit is exhausted by a reachable example.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.SourceQueue
universe u
variable {α : Type u}
open Sequences.SourceQueue
open Sequences.AbstractFIFO (Command)

/-- Copied prefix cells plus one queue dispatch; the append result is retained. -/
def listEnqueueRun (queue : List α) (value : α) : Measured (List α) Nat :=
  CallCount.tick (ListAppend.copies queue [value])

theorem listEnqueueRun_exact (queue : List α) (value : α) :
    listEnqueueRun queue value = (queue ++ [value], queue.length + 1) := by
  simp [listEnqueueRun, ListAppend.copies_exact, CallCount.tick]

theorem listEnqueueRun_value (queue : List α) (value : α) :
    (listEnqueueRun queue value).1 = (lists α).enqueue queue value := by
  rw [listEnqueueRun_exact]
  rfl

/-- A constant queue entry constructs the actual new pair. -/
def enqueueRun (queue : TwoList α) (value : α) : Measured (TwoList α) Nat :=
  (twoListEnqueue queue value, 1)

@[simp] theorem enqueueRun_exact (front back : List α) (value : α) :
    enqueueRun (front, back) value = ((front, value :: back), 1) := rfl

/-- Reverse is executed only for an empty front and a nonempty back. -/
def dequeueUsing (reverse : List α → Measured (List α) Nat) :
    TwoList α → Measured (TwoList α) Nat
  | ([], []) => (([], []), 1)
  | ([], value :: back) =>
      bind (reverse (value :: back)) fun reversed =>
        (match reversed with | [] => ([], []) | _ :: front => (front, []), 1)
  | (_ :: front, back) => ((front, back), 1)

/-- The reversal's actual result supplies the observed head. -/
def peekUsing (reverse : List α → Measured (List α) Nat) (default : α) :
    TwoList α → Measured α Nat
  | ([], []) => (default, 1)
  | ([], value :: back) =>
      bind (reverse (value :: back)) fun reversed =>
        (match reversed with | [] => default | value :: _ => value, 1)
  | (value :: _, _) => (value, 1)

@[simp] theorem dequeueUsing_empty (reverse : List α → Measured (List α) Nat) :
    dequeueUsing reverse twoListEmpty = (twoListEmpty, 1) := rfl

@[simp] theorem dequeueUsing_front (reverse : List α → Measured (List α) Nat)
    (value : α) (front back : List α) :
    dequeueUsing reverse (value :: front, back) = ((front, back), 1) := rfl

theorem dequeueUsing_back (reverse : List α → Measured (List α) Nat)
    (value : α) (back : List α) :
    dequeueUsing reverse ([], value :: back) =
      (((reverse (value :: back)).1.tail, []), (reverse (value :: back)).2 + 1) := by
  simp only [dequeueUsing, bind]
  cases (reverse (value :: back)).1 <;> rfl

@[simp] theorem peekUsing_empty (reverse : List α → Measured (List α) Nat) (default : α) :
    peekUsing reverse default twoListEmpty = (default, 1) := rfl

@[simp] theorem peekUsing_front (reverse : List α → Measured (List α) Nat)
    (default value : α) (front back : List α) :
    peekUsing reverse default (value :: front, back) = (value, 1) := rfl

theorem peekUsing_back (reverse : List α → Measured (List α) Nat)
    (default value : α) (back : List α) :
    peekUsing reverse default ([], value :: back) =
      ((reverse (value :: back)).1.headD default, (reverse (value :: back)).2 + 1) := by
  simp only [peekUsing, bind]
  cases (reverse (value :: back)).1 <;> rfl

theorem dequeueUsing_value (reverse : List α → Measured (List α) Nat)
    (erases : ∀ values, (reverse values).1 = values.reverse) (queue : TwoList α) :
    (dequeueUsing reverse queue).1 = twoListDequeue queue := by
  rcases queue with ⟨front, back⟩
  cases front with
  | nil =>
      cases back with
      | nil => rfl
      | cons value back => rw [dequeueUsing_back, twoListDequeue_back, erases]
  | cons value front => rfl

theorem peekUsing_value (reverse : List α → Measured (List α) Nat)
    (erases : ∀ values, (reverse values).1 = values.reverse)
    (default : α) (queue : TwoList α) :
    (peekUsing reverse default queue).1 = twoListPeek default queue := by
  rcases queue with ⟨front, back⟩
  cases front with
  | nil =>
      cases back with
      | nil => rfl
      | cons value back => rw [peekUsing_back, twoListPeek_back, erases]
  | cons value front => rfl

def dequeueRun : TwoList α → Measured (TwoList α) Nat :=
  dequeueUsing ListReversal.naiveRun

def peekRun (default : α) : TwoList α → Measured α Nat :=
  peekUsing ListReversal.naiveRun default

def linearDequeueRun : TwoList α → Measured (TwoList α) Nat :=
  dequeueUsing (fun values => SymmetricCosts.reverseRun values [])

def linearPeekRun (default : α) : TwoList α → Measured α Nat :=
  peekUsing (fun values => SymmetricCosts.reverseRun values []) default

theorem dequeueRun_value (queue : TwoList α) :
    (dequeueRun queue).1 = twoListDequeue queue :=
  dequeueUsing_value _ ListReversal.naiveRun_value queue

theorem peekRun_value (default : α) (queue : TwoList α) :
    (peekRun default queue).1 = twoListPeek default queue :=
  peekUsing_value _ ListReversal.naiveRun_value default queue

theorem linearDequeueRun_value (queue : TwoList α) :
    (linearDequeueRun queue).1 = twoListDequeue queue := by
  apply dequeueUsing_value
  intro values
  simp [SymmetricCosts.reverseRun_value]

theorem linearPeekRun_value (default : α) (queue : TwoList α) :
    (linearPeekRun default queue).1 = twoListPeek default queue := by
  apply peekUsing_value
  intro values
  simp [SymmetricCosts.reverseRun_value]

theorem dequeueRun_back (value : α) (back : List α) :
    dequeueRun ([], value :: back) =
      (((value :: back).reverse.tail, []), (ListReversal.naiveRun (value :: back)).2 + 1) := by
  rw [dequeueRun, dequeueUsing_back, ListReversal.naiveRun_value]

theorem peekRun_back (default value : α) (back : List α) :
    peekRun default ([], value :: back) =
      ((value :: back).reverse.headD default, (ListReversal.naiveRun (value :: back)).2 + 1) := by
  rw [peekRun, peekUsing_back, ListReversal.naiveRun_value]

/-- The structural reverse's triangular call count, plus queue dispatch. -/
theorem peekRun_back_double_cost (default value : α) (back : List α) :
    2 * (peekRun default ([], value :: back)).2 =
      ((value :: back).length + 1) * ((value :: back).length + 2) + 2 := by
  rw [peekRun_back]
  have count := ListReversal.naiveRun_double_cost (value :: back)
  change 2 * ((ListReversal.naiveRun (value :: back)).2 + 1) = _
  omega

/-- Terminal reversal/append calls and the queue dispatch omitted by the
historical constructor-visit tariff. Empty and front peeks only dispatch. -/
def peekCallOverhead : TwoList α → Nat
  | ([], []) => 1
  | ([], value :: back) => (value :: back).length + 2
  | (_ :: _, _) => 1

/-- The same observing peek, with the historical zero-terminal, zero-dispatch
tariff. Its value comes from the current measured source execution. -/
def constructorPeekRun (default : α) (queue : TwoList α) : Measured α Nat :=
  ((peekRun default queue).1, (peekRun default queue).2 - peekCallOverhead queue)

@[simp] theorem constructorPeekRun_empty (default : α) :
    constructorPeekRun default twoListEmpty = (default, 0) := rfl

@[simp] theorem constructorPeekRun_front (default value : α) (front back : List α) :
    constructorPeekRun default (value :: front, back) = (value, 0) := rfl

theorem constructorPeekRun_back (default value : α) (back : List α) :
    constructorPeekRun default ([], value :: back) =
      ((value :: back).reverse.headD default, ListReversal.constructorVisits (value :: back)) := by
  simp only [constructorPeekRun, peekRun_back, peekCallOverhead]
  rw [ListReversal.naiveRun_cost_eq_constructorVisits]
  congr 1
  omega

theorem constructorPeekRun_value (default : α) (queue : TwoList α) :
    (constructorPeekRun default queue).1 = twoListPeek default queue :=
  peekRun_value default queue

/-- Exact recovery on every raw state, including branches which never reverse.
The correction depends on the input state, not only the scalar cost. -/
theorem peekRun_cost_eq_constructorPeekRun (default : α) (queue : TwoList α) :
    (peekRun default queue).2 =
      (constructorPeekRun default queue).2 + peekCallOverhead queue := by
  rcases queue with ⟨front, back⟩
  cases front with
  | nil =>
      cases back with
      | nil => rfl
      | cons value back =>
          rw [peekRun_back, constructorPeekRun_back]
          simp only [peekCallOverhead]
          rw [ListReversal.naiveRun_cost_eq_constructorVisits]
          omega
  | cons value front => rfl

theorem linearDequeueRun_back (value : α) (back : List α) :
    linearDequeueRun ([], value :: back) =
      (((value :: back).reverse.tail, []), (value :: back).length + 2) := by
  simp [linearDequeueRun, dequeueUsing_back, SymmetricCosts.reverseRun_value,
    SymmetricCosts.reverseRun_work, Nat.add_assoc]

theorem linearPeekRun_back (default value : α) (back : List α) :
    linearPeekRun default ([], value :: back) =
      ((value :: back).reverse.headD default, (value :: back).length + 2) := by
  simp [linearPeekRun, peekUsing_back, SymmetricCosts.reverseRun_value,
    SymmetricCosts.reverseRun_work, Nat.add_assoc]

theorem peek_realizations_agree (default : α) (queue : TwoList α) :
    (peekRun default queue).1 = (linearPeekRun default queue).1 := by
  rw [peekRun_value, linearPeekRun_value]

theorem linearPeekRun_cost_le (default : α) (queue : TwoList α) :
    (linearPeekRun default queue).2 ≤ (peekRun default queue).2 := by
  rcases queue with ⟨front, back⟩
  cases front with
  | nil =>
      cases back with
      | nil => rfl
      | cons value back =>
          change (peekUsing _ _ _).2 ≤ (peekUsing _ _ _).2
          rw [peekUsing_back, peekUsing_back]
          exact Nat.add_le_add_right (ListReversal.accumulator_cost_le _ []) 1
  | cons value front => rfl

theorem linearPeekRun_back_cost_lt (default value : α) (back : List α) :
    (linearPeekRun default ([], value :: back)).2 < (peekRun default ([], value :: back)).2 := by
  change (peekUsing _ _ _).2 < (peekUsing _ _ _).2
  rw [peekUsing_back, peekUsing_back]
  exact Nat.add_lt_add_right (ListReversal.accumulator_cost_lt _ [] (by simp)) 1

/-- This lower bound concerns the current call tariff; `constructorVisits`
separately recovers the historical zero-terminal count. -/
theorem naiveRun_length_le (values : List α) : values.length ≤ (ListReversal.naiveRun values).2 := by
  have bound := ListReversal.accumulator_cost_le values []
  rw [SymmetricCosts.reverseRun_work] at bound
  omega

theorem peekUsing_back_length_le (reverse : List α → Measured (List α) Nat)
    (work : ∀ values, values.length ≤ (reverse values).2) (default : α) (back : List α) :
    back.length ≤ (peekUsing reverse default ([], back)).2 := by
  cases back with
  | nil => simp
  | cons value back =>
      rw [peekUsing_back]
      exact Nat.le_trans (work _) (Nat.le_add_right _ _)

theorem peekRun_back_length_le (default : α) (back : List α) :
    back.length ≤ (peekRun default ([], back)).2 :=
  peekUsing_back_length_le _ naiveRun_length_le default back

theorem linearPeekRun_back_length_le (default : α) (back : List α) :
    back.length ≤ (linearPeekRun default ([], back)).2 := by
  apply peekUsing_back_length_le
  intro values
  rw [SymmetricCosts.reverseRun_work]
  omega

/-! ## Sequential enqueue/dequeue accounting for linear reversal -/

def backPotential (queue : TwoList α) : Nat := queue.2.length

def linearStep : Command α → TwoList α → Measured (TwoList α) Nat
  | .enqueue value, queue => enqueueRun queue value
  | .delete, queue => linearDequeueRun queue

theorem linearStep_value (command : Command α) (queue : TwoList α) :
    (linearStep command queue).1 =
      Sequences.AbstractFIFO.step (twoListFIFO α) command queue := by
  cases command with
  | enqueue value => rfl
  | delete => exact linearDequeueRun_value queue

def linearInstrumentation : FIFOContracts.Instrumentation (twoListFIFO α) where
  measured := linearStep
  erases := linearStep_value

theorem linearStep_potential (command : Command α) (queue : TwoList α) :
    (linearStep command queue).2 + backPotential (linearStep command queue).1 ≤
      backPotential queue + 2 := by
  rcases queue with ⟨front, back⟩
  cases command with
  | enqueue value => simp [linearStep, enqueueRun, twoListEnqueue, backPotential]; omega
  | delete =>
      cases front with
      | nil =>
          cases back with
          | nil => simp [linearStep, linearDequeueRun, dequeueUsing, backPotential]
          | cons value back => simp [linearStep, linearDequeueRun_back, backPotential]
      | cons value front => simp [linearStep, linearDequeueRun, backPotential]; omega

/-- Final credit is retained; arbitrary raw initial pairs carry their back length. -/
theorem run_linearStep_potential (commands : List (Command α)) (queue : TwoList α) :
    (Resources.run linearStep commands queue).2 +
        backPotential (Resources.run linearStep commands queue).1 ≤
      backPotential queue + 2 * commands.length :=
  run_constant_charge linearStep backPotential 2 linearStep_potential commands queue

theorem run_linearStep_cost_le (commands : List (Command α)) (queue : TwoList α) :
    (Resources.run linearStep commands queue).2 ≤ backPotential queue + 2 * commands.length := by
  have bound := run_linearStep_potential commands queue
  omega

theorem run_linearStep_twoListEmpty_cost_le (commands : List (Command α)) :
    (Resources.run linearStep commands (twoListEmpty : TwoList α)).2 ≤ 2 * commands.length := by
  simpa [backPotential, twoListEmpty] using run_linearStep_cost_le commands twoListEmpty

theorem run_linearStep_value (commands : List (Command α)) (queue : TwoList α) :
    (Resources.run linearStep commands queue).1 =
      Sequences.AbstractFIFO.run (twoListFIFO α) commands queue :=
  FIFOContracts.run_erases linearInstrumentation commands queue

theorem run_linearStep_decode (commands : List (Command α)) (queue : TwoList α) :
    twoListDecode (Resources.run linearStep commands queue).1 =
      Sequences.AbstractFIFO.run (Sequences.AbstractFIFO.lists α) commands (twoListDecode queue) := by
  rw [run_linearStep_value, twoList_run_decode]

theorem linear_accounting :
    FIFOContracts.Accounting (twoListFIFO α) linearInstrumentation twoListDecode
      (fun _ _ => 2) (fun queue credit => backPotential queue ≤ credit) where
  behavior := twoList_simulation α
  certificate := ⟨backPotential, fun _ _ bound => bound, linearStep_potential⟩

/-- The existing public client contract needs only a certified initial credit. -/
theorem linear_client_bound (commands : List (Command α)) (queue : TwoList α)
    (credit : Nat) (initial : backPotential queue ≤ credit) :
    (Resources.run linearStep commands queue).2 ≤ credit +
      FIFOContracts.abstractBudget (fun _ _ => 2) commands (twoListDecode queue) :=
  FIFOContracts.client_bound linear_accounting commands queue credit initial

/-- Sequential composition uses the initial credit once. -/
theorem linear_sequential_bound (first second : List (Command α)) (queue : TwoList α) :
    (bind (Resources.run linearStep first queue) (Resources.run linearStep second)).2 ≤
      backPotential queue + 2 * (first.length + second.length) := by
  rw [← Resources.run_append]
  simpa only [List.length_append] using run_linearStep_cost_le (first ++ second) queue

/-! ## Observing peeks cannot spend unchanged-state potential -/

/-- Execute peek and keep its unchanged queue state for the common executor. -/
def peekStepUsing (reverse : List α → Measured (List α) Nat) (default : α)
    (queue : TwoList α) : Measured (TwoList α) Nat :=
  bind (peekUsing reverse default queue) (fun _ => pure queue)

theorem peekStepUsing_exact (reverse : List α → Measured (List α) Nat)
    (default : α) (queue : TwoList α) :
    peekStepUsing reverse default queue = (queue, (peekUsing reverse default queue).2) := by
  simp [peekStepUsing, bind, pure]

/-- A wrapper around the shared executor, not another history interpreter. -/
def runPeeksUsing (reverse : List α → Measured (List α) Nat) (default : α)
    (count : Nat) (queue : TwoList α) : Measured (TwoList α) Nat :=
  Resources.run (fun _ : Unit => peekStepUsing reverse default) (List.replicate count ()) queue

theorem run_peekStepUsing (reverse : List α → Measured (List α) Nat)
    (default : α) (inputs : List Unit) (queue : TwoList α) :
    Resources.run (fun _ : Unit => peekStepUsing reverse default) inputs queue =
      (queue, inputs.length * (peekUsing reverse default queue).2) := by
  induction inputs with
  | nil => simp [Resources.run, pure]
  | cons input inputs ih =>
      simp [Resources.run, peekStepUsing_exact, bind, ih, Nat.add_mul, Nat.add_comm]

theorem runPeeksUsing_exact (reverse : List α → Measured (List α) Nat)
    (default : α) (count : Nat) (queue : TwoList α) :
    runPeeksUsing reverse default count queue =
      (queue, count * (peekUsing reverse default queue).2) := by
  simp [runPeeksUsing, run_peekStepUsing]

/-- Observing peek retains the entire raw state under the constructor tariff. -/
def constructorPeekStep (default : α) (queue : TwoList α) : Measured (TwoList α) Nat :=
  (queue, (constructorPeekRun default queue).2)

/-- The historical observations run through the same shared history executor. -/
theorem run_constructorPeekStep (default : α) (inputs : List Unit) (queue : TwoList α) :
    Resources.run (fun _ : Unit => constructorPeekStep default) inputs queue =
      (queue, inputs.length * (constructorPeekRun default queue).2) := by
  induction inputs with
  | nil => simp [Resources.run, pure]
  | cons input inputs ih =>
      simp [Resources.run, constructorPeekStep, bind, ih, Nat.add_mul, Nat.add_comm]

/-- Every repeated observing peek pays the same terminal/dispatch difference;
neither execution installs the reversed front list. -/
theorem run_peekStepUsing_cost_eq_constructor (default : α) (inputs : List Unit) (queue : TwoList α) :
    (Resources.run (fun _ : Unit => peekStepUsing ListReversal.naiveRun default) inputs queue).2 =
      (Resources.run (fun _ : Unit => constructorPeekStep default) inputs queue).2 +
        inputs.length * peekCallOverhead queue := by
  rw [run_peekStepUsing, run_constructorPeekStep]
  change inputs.length * (peekRun default queue).2 = _
  rw [peekRun_cost_eq_constructorPeekRun, Nat.mul_add]

theorem peek_local_charge_iff (reverse : List α → Measured (List α) Nat)
    (default : α) (potential : TwoList α → Nat) (charge : Nat) (queue : TwoList α) :
    (peekStepUsing reverse default queue).2 + potential (peekStepUsing reverse default queue).1 ≤
        potential queue + charge ↔ (peekUsing reverse default queue).2 ≤ charge := by
  rw [peekStepUsing_exact]
  change (peekUsing reverse default queue).2 + potential queue ≤
    potential queue + charge ↔ (peekUsing reverse default queue).2 ≤ charge
  omega

/-- Reachability uses the existing source FIFO executor and only enqueue commands. -/
def EnqueueReachable (queue : TwoList α) : Prop :=
  ∃ values : List α,
    Sequences.AbstractFIFO.run (twoListFIFO α) (values.map Command.enqueue) twoListEmpty = queue

theorem replicate_reachable (count : Nat) (value : α) :
    EnqueueReachable ([], List.replicate count value) := by
  refine ⟨List.replicate count value, ?_⟩
  simpa only [List.map_replicate] using twoList_run_replicate_enqueue count value

theorem no_uniform_peek_charge (reverse : List α → Measured (List α) Nat)
    (work : ∀ values, values.length ≤ (reverse values).2)
    (default value : α) (potential : TwoList α → Nat) :
    ¬ ∃ charge : Nat, ∀ queue, EnqueueReachable queue →
      (peekStepUsing reverse default queue).2 + potential (peekStepUsing reverse default queue).1 ≤
        potential queue + charge := by
  rintro ⟨charge, charged⟩
  have upper := (peek_local_charge_iff reverse default potential charge
    ([], List.replicate (charge + 1) value)).mp
      (charged _ (replicate_reachable _ _))
  have lower := peekUsing_back_length_le reverse work default (List.replicate (charge + 1) value)
  rw [List.length_replicate] at lower
  omega

/-- Even arbitrary finite initial credit is defeated by enough actual peeks. -/
theorem peeks_exceed_initial_credit (reverse : List α → Measured (List α) Nat)
    (work : ∀ values, values.length ≤ (reverse values).2)
    (default value : α) (initialCredit : TwoList α → Nat) (charge : Nat) :
    ∃ queue, EnqueueReachable queue ∧ ∃ count, 0 < count ∧
      initialCredit queue + charge * count < (runPeeksUsing reverse default count queue).2 := by
  let queue : TwoList α := ([], List.replicate (charge + 1) value)
  let count := initialCredit queue + 1
  have lower : charge + 1 ≤ (peekUsing reverse default queue).2 := by
    simpa only [List.length_replicate] using
      peekUsing_back_length_le reverse work default (List.replicate (charge + 1) value)
  refine ⟨queue, replicate_reachable _ _, count, by dsimp [count]; omega, ?_⟩
  rw [runPeeksUsing_exact]
  change initialCredit queue + charge * count < count * (peekUsing reverse default queue).2
  calc
    initialCredit queue + charge * count < count * (charge + 1) := by
      dsimp [count]
      nlinarith
    _ ≤ count * (peekUsing reverse default queue).2 := Nat.mul_le_mul_left count lower

theorem source_no_uniform_peek_charge (default value : α) (potential : TwoList α → Nat) :
    ¬ ∃ charge : Nat, ∀ queue, EnqueueReachable queue →
      (peekStepUsing ListReversal.naiveRun default queue).2 +
          potential (peekStepUsing ListReversal.naiveRun default queue).1 ≤
        potential queue + charge :=
  no_uniform_peek_charge _ naiveRun_length_le default value potential

theorem source_peeks_exceed_initial_credit (default value : α)
    (initialCredit : TwoList α → Nat) (charge : Nat) :
    ∃ queue, EnqueueReachable queue ∧ ∃ count, 0 < count ∧
      initialCredit queue + charge * count <
        (runPeeksUsing ListReversal.naiveRun default count queue).2 :=
  peeks_exceed_initial_credit _ naiveRun_length_le default value initialCredit charge

theorem linear_no_uniform_peek_charge (default value : α) (potential : TwoList α → Nat) :
    ¬ ∃ charge : Nat, ∀ queue, EnqueueReachable queue →
      (peekStepUsing (fun values => SymmetricCosts.reverseRun values []) default queue).2 +
          potential (peekStepUsing (fun values => SymmetricCosts.reverseRun values []) default queue).1 ≤
        potential queue + charge := by
  apply no_uniform_peek_charge _ _ default value potential
  intro values
  rw [SymmetricCosts.reverseRun_work]
  omega

theorem linear_peeks_exceed_initial_credit (default value : α)
    (initialCredit : TwoList α → Nat) (charge : Nat) :
    ∃ queue, EnqueueReachable queue ∧ ∃ count, 0 < count ∧
      initialCredit queue + charge * count <
        (runPeeksUsing (fun values => SymmetricCosts.reverseRun values []) default count queue).2 := by
  apply peeks_exceed_initial_credit _ _ default value initialCredit charge
  intro values
  rw [SymmetricCosts.reverseRun_work]
  omega

def peekSquare (default : α) :=
  erasureSquare (peekRun default) (twoListPeek default) (peekRun_value default)

def linearPeekSquare (default : α) :=
  erasureSquare (linearPeekRun default) (twoListPeek default) (linearPeekRun_value default)

end Resources.SourceQueue
