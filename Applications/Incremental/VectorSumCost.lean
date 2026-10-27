import Applications.Incremental.VectorSum
import Applications.Resources.Workload
import Applications.Resources.Growth
import Mathlib.Algebra.BigOperators.Fin

/-! An abstract unit-cost indexed-store interpreter. Each primitive below is
one modeled operation. Scalar arguments are registers; tuples, control and
index arithmetic are uncharged. Indexed storage is owned and mutable in this
model; functional update here specifies its contents, not Lean runtime cost. -/
namespace Incremental.VectorSum.Cost
open Resources
variable {G : Type} [AddCommGroup G] {n : Nat}

def read (v : Values G n) (i : Fin n) : Measured G Nat := (v i, 1)
def write (v : Values G n) (i : Fin n) (x : G) : Measured (Values G n) Nat :=
  (Function.update v i x, 1)
def add (x y : G) : Measured G Nat := (x + y, 1)
def sub (x y : G) : Measured G Nat := (x - y, 1)
def store (x : G) : Measured G Nat := (x, 1)
def emit (x : G) : Measured G Nat := (x, 1)

/-- Materialize an input supplied through a unit-cost indexed reader. Writing
one new cell costs one operation; the resulting store is owned by this run. -/
def prepend (x : G) (v : Values G n) : Measured (Values G (n + 1)) Nat :=
  (Fin.cons x v, 1)

def copy : {n : Nat} → Values G n → Measured (Values G n) Nat
  | 0, v => Resources.pure v
  | _ + 1, v => Resources.bind (read v 0) fun x =>
      Resources.bind (copy (fun i => v i.succ)) fun t => prepend x t

omit [AddCommGroup G] in
theorem copy_value (v : Values G n) : (copy v).1 = v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [copy, Resources.bind, read, prepend, ih]
    exact Fin.cons_self_tail v

omit [AddCommGroup G] in
theorem copy_cost (v : Values G n) : (copy v).2 = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [copy, Resources.bind, read, prepend, ih]; omega

/-- Reading each indexed cell once and adding it once. -/
def scan : {n : Nat} → Values G n → Measured G Nat
  | 0, _ => Resources.pure 0
  | _ + 1, v => Resources.bind (read v 0) fun x =>
      Resources.bind (scan (fun i => v i.succ)) fun s => add x s

theorem scan_value (v : Values G n) : (scan v).1 = total v := by
  induction n with
  | zero => simp [scan, Resources.pure, total]
  | succ n ih => simp [scan, Resources.bind, read, add, ih, total, Fin.sum_univ_succ]

theorem scan_cost (v : Values G n) : (scan v).2 = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [scan, Resources.bind, read, add, ih]; omega

/-- The caller transfers ownership of the n indexed cells. Only the sum cache
is newly retained; an interpreter that copies input must charge that copy. -/
def init (v : Values G n) : Measured (State G n) Nat :=
  Resources.bind (scan v) fun s => Resources.bind (store s) fun t => Resources.pure ⟨v, t⟩

def step (a : Assignment G n) (s : State G n) : Measured (State G n) Nat :=
  Resources.bind (read s.values a.1) fun old =>
  Resources.bind (sub a.2 old) fun d =>
  Resources.bind (add s.sum d) fun t =>
  Resources.bind (write s.values a.1 a.2) fun v =>
  Resources.bind (store t) fun u => Resources.pure ⟨v, u⟩

@[simp] theorem step_value (a : Assignment G n) (s : State G n) :
    (step a s).1 = VectorSum.step s a := rfl

@[simp] theorem step_cost (a : Assignment G n) (s : State G n) : (step a s).2 = 5 := rfl

/-- Boundary conversion is one subtraction after the ordered patch. -/
def repair (s : State G n) (p : Patch G n) : Measured (State G n × G) Nat :=
  Resources.bind (run step p s) fun t => Resources.bind (sub t.sum s.sum) fun d => Resources.pure (t, d)

def observe (s : State G n) : Measured G Nat := emit s.sum

theorem init_value (v : Values G n) : (init v).1 = VectorSum.init v := by
  simp [init, Resources.bind, store, Resources.pure, scan_value, VectorSum.init]

theorem init_cost (v : Values G n) : (init v).2 = 2 * n + 1 := by
  simp [init, Resources.bind, store, Resources.pure, scan_cost]

theorem patch_value (s : State G n) (p : Patch G n) :
    (run step p s).1 = patch s p := by
  rw [run_state]; rfl

theorem patch_cost (s : State G n) (p : Patch G n) :
    (run step p s).2 = 5 * p.length := by
  induction p generalizing s with
  | nil => rfl
  | cons a p ih => simp [run_cons, ih]; omega

theorem repair_value (s : State G n) (p : Patch G n) :
    (repair s p).1 = (realization G n).repair s p := by
  simp [repair, Resources.bind, sub, Resources.pure, patch_value]

theorem repair_cost (s : State G n) (p : Patch G n) :
    (repair s p).2 = 5 * p.length + 1 := by
  simp [repair, Resources.bind, sub, Resources.pure, patch_cost]

omit [AddCommGroup G] in
theorem observe_cost (s : State G n) : (observe s).2 = 1 := rfl

/-- The scalar consumer also charges cache maintenance and the emitted
boundary delta's addition. Its observation is charged separately. -/
def doubleInit (x : G) : Measured G Nat := Resources.bind (add x x) store

def doubleRepair (s d : G) : Measured (G × G) Nat :=
  Resources.bind (add d d) fun e => Resources.bind (add s e) fun t => Resources.bind (store t) fun u => Resources.pure (u, e)

def composedInit (v : Values G n) : Measured (State G n × G) Nat :=
  Resources.bind (init v) fun s => Resources.bind (observe s) fun x =>
    Resources.bind (doubleInit x) fun t => Resources.pure (s, t)

def composedRepair (s : State G n × G) (p : Patch G n) :
    Measured ((State G n × G) × G) Nat :=
  Resources.bind (repair s.1 p) fun t => Resources.bind (doubleRepair s.2 t.2) fun u => Resources.pure ((t.1, u.1), u.2)

theorem composedInit_value (v : Values G n) :
    (composedInit v).1 = (doubled G n).init v := by
  simp [composedInit, Resources.bind, init_value, observe, emit, doubleInit, add, store, Resources.pure,
    realization, doubleRealization]

theorem composedInit_cost (v : Values G n) : (composedInit v).2 = 2 * n + 4 := by
  simp [composedInit, Resources.bind, init_cost, observe, emit, doubleInit, add, store, Resources.pure]

theorem composedRepair_value (s : State G n × G) (p : Patch G n) :
    (composedRepair s p).1 = (doubled G n).repair s p := by
  simp [composedRepair, Resources.bind, repair_value, doubleRepair, add, store, Resources.pure,
    doubleRealization]

theorem composedRepair_cost (s : State G n × G) (p : Patch G n) :
    (composedRepair s p).2 = 5 * p.length + 4 := by
  simp [composedRepair, Resources.bind, repair_cost, doubleRepair, add, store, Resources.pure]

/-- Each workload entry repairs the state and emits one scalar observation.
Outputs are streamed, rather than retained in a growing output list. -/
def batch (p : Patch G n) (s : State G n × G) : Measured (State G n × G) Nat :=
  Resources.bind (composedRepair s p) fun t => Resources.bind (emit t.1.2) fun _ => Resources.pure t.1

def workload (v : Values G n) (ps : List (Patch G n)) : Measured (State G n × G) Nat :=
  Resources.bind (composedInit v) (run batch ps)

def assignments (ps : List (Patch G n)) : Nat := (ps.map List.length).sum

theorem batches_cost (s : State G n × G) (ps : List (Patch G n)) :
    (run batch ps s).2 = 5 * assignments ps + 5 * ps.length := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp [run_cons, batch, Resources.bind, emit, Resources.pure, composedRepair_cost, ih, assignments]
    omega

theorem workload_cost (v : Values G n) (ps : List (Patch G n)) :
    (workload v ps).2 = 2 * n + 4 + 5 * assignments ps + 5 * ps.length := by
  simp [workload, Resources.bind, composedInit_cost, batches_cost]; omega

theorem workload_bound (v : Values G n) (ps : List (Patch G n)) :
    (workload v ps).2 ≤ 5 * (n + assignments ps + ps.length + 1) := by
  rw [workload_cost]; omega

theorem workload_valid (v : Values G n) (ps : List (Patch G n)) :
    Stateful.CompValid (realization G n) (doubleRealization G) Valid
      (fun x s => s = x + x) (ps.foldl applyPatch v) (workload v ps).1 := by
  have h : ∀ ps (v : Values G n) s,
      Stateful.CompValid (realization G n) (doubleRealization G) Valid
        (fun x s => s = x + x) v s →
      Stateful.CompValid (realization G n) (doubleRealization G) Valid
        (fun x s => s = x + x) (ps.foldl applyPatch v) (run batch ps s).1 := by
    intro ps
    induction ps with
    | nil => intro v s hs; exact hs
    | cons p ps ih =>
      intro v s hs
      apply ih
      simp only [batch, Resources.bind, emit, Resources.pure]
      rw [composedRepair_value]
      exact doubled_laws.repair v s p hs
  simpa [workload, Resources.bind, composedInit_value] using h ps v _ (doubled_laws.init v)

/-- Charged conversion followed by initialization. An arbitrary mathematical
function needs a reader realization before this cost contract applies. -/
def materializedInit (v : Values G n) : Measured (State G n × G) Nat :=
  Resources.bind (copy v) composedInit

theorem materializedInit_value (v : Values G n) :
    (materializedInit v).1 = (doubled G n).init v := by
  simp only [materializedInit, Resources.bind, composedInit_value, copy_value]

theorem materializedInit_cost (v : Values G n) :
    (materializedInit v).2 = 4 * n + 4 := by
  simp [materializedInit, Resources.bind, copy_cost, composedInit_cost]; omega

/-- One cell per input index, and two scalar cache cells for the composition.
This is the abstract store layout, independent of Lean's object representation. -/
abbrev Slot (n : Nat) := Fin n ⊕ Fin 2

def contents (s : State G n × G) : Slot n → G
  | .inl i => s.1.values i
  | .inr i => if i = 0 then s.1.sum else s.2

def decodeContents (memory : Slot n → G) : State G n × G :=
  (⟨fun i => memory (.inl i), memory (.inr 0)⟩, memory (.inr 1))

omit [AddCommGroup G] in
theorem decode_contents (s : State G n × G) : decodeContents (contents s) = s := by
  rcases s with ⟨⟨v, t⟩, u⟩
  simp [decodeContents, contents]

theorem slot_count (n : Nat) : Fintype.card (Slot n) = n + 2 := by
  simp [Slot]

/-- Exact slot counts of the owned indexed store and scalar caches, independent
of patch length. Input patch storage and streamed outputs belong to the caller. -/
def retainedSlots (n : Nat) : Nat := Fintype.card (Fin n ⊕ Unit)
def composedRetainedSlots (n : Nat) : Nat := Fintype.card (Slot n)

theorem retained_linear (n : Nat) : composedRetainedSlots n ≤ 2 * (n + 1) := by
  simp only [composedRetainedSlots, slot_count]; omega

theorem initialization_bigO : Asymptotics.IsBigO Filter.atTop
    (fun n => ((2 * n + 4 : Nat) : ℝ)) (fun n => (n : ℝ)) :=
  Resources.isBigO_of_nat_bound _ _ 6 1 (by intro n hn; omega)

theorem repair_bigO : Asymptotics.IsBigO Filter.atTop
    (fun k => ((5 * k + 4 : Nat) : ℝ)) (fun k => (k : ℝ)) :=
  Resources.isBigO_of_nat_bound _ _ 9 1 (by intro k hk; omega)

end Incremental.VectorSum.Cost
