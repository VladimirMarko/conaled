import Applications.Resources.Measured
import Applications.Optimization.Transport
import Mathlib.Tactic

/-! Resource observations for the bounded structured-matrix machine. Events are
abstract operations; tariffs state target assumptions rather than Lean timings.
Retained storage and peak live storage are not additive execution events. -/
namespace StructuredLinear.Costs

inductive Event where
  | traversal | inputRead | outputRead | coefficientRead | index
  | scalarMul | scalarAdd | outputWrite | construct | scan
  deriving DecidableEq

abbrev Work := Event → Nat

def tick (e : Event) (n : Nat := 1) : Work := fun f => if e = f then n else 0

/-- Traverse each stored element once, recording the work at the executed step. -/
def measuredFold {S A : Type*} (step : S → A → S) (charge : A → Work) :
    List A → S → Resources.Measured S Work
  | [], s => (s, 0)
  | a :: as, s => Resources.bind (step s a, charge a) (measuredFold step charge as)

@[simp] theorem fold_erases {S A : Type*} (step : S → A → S) (charge : A → Work)
    (as : List A) (s : S) : (measuredFold step charge as s).1 = as.foldl step s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simpa [measuredFold, Resources.bind] using ih (step s a)

@[simp] theorem fold_cost {S A : Type*} (step : S → A → S) (charge : A → Work)
    (as : List A) (s : S) :
    (measuredFold step charge as s).2 = (as.map charge).sum := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp [measuredFold, Resources.bind, ih]

theorem fold_cost_uniform {S A : Type*} (step : S → A → S) (charge : Work)
    (as : List A) (s : S) (e : Event) :
    (measuredFold step (fun _ => charge) as s).2 e = as.length * charge e := by
  induction as generalizing s with
  | nil => simp [measuredFold]
  | cons a as ih => simp [measuredFold, Resources.bind, ih, Nat.add_mul, Nat.add_comm]

/-- Materialization traverses the source and allocates each destination element. -/
def measuredMap {A B : Type*} (f : A → B) (charge : A → Work) :
    List A → Resources.Measured (List B) Work
  | [] => ([], 0)
  | a :: as =>
    let rest := measuredMap f charge as
    (f a :: rest.1, charge a + rest.2)

@[simp] theorem map_erases {A B : Type*} (f : A → B) (charge : A → Work) (as : List A) :
    (measuredMap f charge as).1 = as.map f := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [measuredMap, ih]

@[simp] theorem map_cost {A B : Type*} (f : A → B) (charge : A → Work) (as : List A) :
    (measuredMap f charge as).2 = (as.map charge).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [measuredMap, ih]

theorem map_cost_uniform {A B : Type*} (f : A → B) (charge : Work)
    (as : List A) (e : Event) :
    (measuredMap f (fun _ => charge) as).2 e = as.length * charge e := by
  induction as with
  | nil => simp [measuredMap]
  | cons a as ih => simp [measuredMap, ih, Nat.add_mul, Nat.add_comm]

def events : List Event := [.traversal, .inputRead, .outputRead, .coefficientRead,
  .index, .scalarMul, .scalarAdd, .outputWrite, .construct, .scan]

def tariff (prices : Work) (work : Work) : Nat :=
  (events.map (fun e => prices e * work e)).sum

theorem tariff_add (prices a b : Work) :
    tariff prices (a + b) = tariff prices a + tariff prices b := by
  simp [tariff, events, Nat.mul_add]
  omega

/-- Sequence measured executions, retaining the observations in input order. -/
def traverse {X Y : Type*} (apply : X → Resources.Measured Y Work) :
    List X → Resources.Measured (List Y) Work
  | [] => ([], 0)
  | x :: xs =>
    let head := apply x
    let tail := traverse apply xs
    (head.1 :: tail.1, head.2 + tail.2)

@[simp] theorem traverse_value {X Y : Type*} (apply : X → Resources.Measured Y Work)
    (xs : List X) : (traverse apply xs).1 = xs.map (fun x => (apply x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [traverse, ih]

@[simp] theorem traverse_cost {X Y : Type*} (apply : X → Resources.Measured Y Work)
    (xs : List X) : (traverse apply xs).2 = (xs.map (fun x => (apply x).2)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [traverse, ih]

theorem traverse_cost_uniform {X Y : Type*} (apply : X → Resources.Measured Y Work)
    (charge : Work) (h : ∀ x, (apply x).2 = charge) (xs : List X) (e : Event) :
    (traverse apply xs).2 e = xs.length * charge e := by
  induction xs with
  | nil => simp [traverse]
  | cons x xs ih => simp [traverse, h, ih, Nat.add_mul, Nat.add_comm]

/-- A measured preparation followed by a finite workload. Inputs may differ. -/
def workload {P X Y : Type*} (prepare : Resources.Measured P Work)
    (apply : P → X → Resources.Measured Y Work) (inputs : List X) :
    Resources.Measured (List Y) Work :=
  Resources.bind prepare fun p => traverse (apply p) inputs

theorem workload_cost {P X Y : Type*} (prepare : Resources.Measured P Work)
    (apply : P → X → Resources.Measured Y Work) (inputs : List X) :
    (workload prepare apply inputs).2 =
      prepare.2 + (inputs.map (fun x => (apply prepare.1 x).2)).sum := by
  simp [workload, Resources.bind]

theorem workload_erases {P X Y : Type*} (prepare : Resources.Measured P Work)
    (apply : P → X → Resources.Measured Y Work) (inputs : List X) :
    (workload prepare apply inputs).1 = inputs.map (fun x => (apply prepare.1 x).1) := by
  simp [workload, Resources.bind]

theorem workload_repeat_cost {P X Y : Type*} (prepare : Resources.Measured P Work)
    (apply : P → X → Resources.Measured Y Work) (x : X) (n : Nat) (e : Event) :
    (workload prepare apply (List.replicate n x)).2 e =
      prepare.2 e + n * (apply prepare.1 x).2 e := by
  simp [workload_cost, List.sum_replicate, nsmul_eq_mul]

/-- Target support is an independent feasibility condition, never a zero cost. -/
inductive Format where | dense | coordinate | diagonal
  deriving DecidableEq

structure Target where
  supports : Format → Prop
  randomAccess : Prop
  capacity : Nat

/-- Candidate storage format, workload observations, and a declared workspace
allowance. Application vectors have their own fixed dense format. -/
structure Plan where
  storageFormat : Format
  preparation : Work
  application : Work
  retained : Nat
  workspace : Nat

def eligible (target : Target) (p : Plan) : Prop :=
  target.supports p.storageFormat ∧ target.randomAccess ∧ p.retained + p.workspace ≤ target.capacity

def objective (prices : Work) (repetitions : Nat) (p : Plan) : Nat :=
  tariff prices (p.preparation + fun e => repetitions * p.application e)

/-- Repricing transports a least-cost result only when it is monotone and
agrees on every admitted candidate. No coverage beyond the image is claimed. -/
theorem transport_choice {C : Type*} (admitted : Set C) (realize : C → Plan)
    (sourceCost : C → Nat) (prices : Work) (n : Nat) (h : Nat → Nat)
    (monotone : Monotone h)
    (agreement : ∀ c ∈ admitted, objective prices n (realize c) = h (sourceCost c))
    {c : C} (best : c ∈ Optimization.minimizers admitted sourceCost) :
    realize c ∈ Optimization.minimizers (realize '' admitted) (objective prices n) :=
  Optimization.minimizer_image realize h monotone agreement best

end StructuredLinear.Costs
