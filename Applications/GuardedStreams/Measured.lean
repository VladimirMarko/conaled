import Applications.GuardedStreams.Execution

namespace Applications.GuardedStreams
open SquareKit.GuardedStreamCompiler
open SquareKit.GuardedStreamCompiler.Execution
open SquareKit.GuardedStreamCompiler.Examples

/-- Coefficient operations, inspected list cells, and allocated list/header cells.
These are source-level events, not machine instruction or byte counts. -/
abbrev Work := Nat × (Nat × Nat)
abbrev Measured (A : Type) := Resources.Measured A Work

def charge (a : A) (w : Work) : Measured A := (a, w)

def read (xs : List Nat) (i : Nat) : Measured Nat :=
  match xs, i with
  | [], _ => (0, 0)
  | a :: _, 0 => (a, (0, 1, 0))
  | _ :: xs, i + 1 => Resources.bind (charge () (0, 1, 0)) (fun _ => read xs i)

def length : List Nat → Measured Nat
  | [] => (0, 0)
  | _ :: xs => Resources.bind (length xs) (fun n => (n + 1, (0, 1, 0)))

def snoc : List Nat → Nat → Measured (List Nat)
  | [], a => ([a], (0, 0, 1))
  | x :: xs, a => Resources.bind (snoc xs a) (fun ys => (x :: ys, (0, 1, 1)))

def copy : Nat → List Nat → Measured (List Nat)
  | 0, _ => ([], 0)
  | _ + 1, [] => ([], 0)
  | n + 1, x :: xs => Resources.bind (copy n xs) (fun ys => (x :: ys, (0, 1, 1)))

@[simp] theorem read_value (xs : List Nat) (i : Nat) : (read xs i).1 = history 0 xs i := by
  induction xs generalizing i with
  | nil => simp [read, history]
  | cons x xs ih => cases i <;> simp [read, history, Resources.bind, ih]

@[simp] theorem length_value (xs : List Nat) : (length xs).1 = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [length, Resources.bind, ih]

@[simp] theorem snoc_value (xs : List Nat) (a : Nat) : (snoc xs a).1 = xs ++ [a] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [snoc, Resources.bind, ih]

@[simp] theorem copy_value (n : Nat) (xs : List Nat) : (copy n xs).1 = xs.take n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => cases xs <;> simp [copy, Resources.bind, ih]

/-- Syntax is actually evaluated. History and prior-definition reads carry their
traversal observations; the coordinate parameter is an explicit primitive input. -/
def evalMeasured (p : Nat → Measured Nat) (r h : Nat → Measured Nat) :
    Program → Nat → Measured Nat
  | .recur, n => h n
  | .param _, n => p n
  | .ref _, n => r n
  | .delay b _, 0 => (if b then 1 else 0, (1, 0, 0))
  | .delay _ t, n + 1 => evalMeasured p r h t n
  | .app _ t, n => Resources.bind (p n) fun x =>
      Resources.bind (evalMeasured p r h t n) fun y => (x + y, (1, 0, 0))
  | .zip _ t u, n => Resources.bind (evalMeasured p r h t n) fun x =>
      Resources.bind (evalMeasured p r h u n) fun y => (x + y, (1, 0, 0))

theorem evalMeasured_value (p r h : Nat → Measured Nat) (t : Program) (n : Nat) :
    (evalMeasured p r h t n).1 =
      (inputs (fun i => (p i).1) (fun i => (r i).1)).eval t (fun i => (h i).1) n := by
  induction t generalizing n with
  | recur | param | ref => rfl
  | delay b t ih => cases n <;> simp [evalMeasured, eval, inputs, ih]
  | app o t ih => simp [evalMeasured, eval, inputs, Resources.bind, ih]
  | zip o t u ih jh => simp [evalMeasured, eval, inputs, Resources.bind, ih, jh]

def appendProgram (refs : List Nat) (t : Program) (xs : List Nat) : Measured (List Nat) :=
  Resources.bind (length xs) fun n =>
    Resources.bind (evalMeasured (fun _ => (0, (1, 0, 0))) (read refs) (read xs) t n)
      (snoc xs)

theorem appendProgram_value (refs : List Nat) (t : Program) (xs : List Nat) :
    (appendProgram refs t xs).1 =
      ((inputs (fun _ => 0) (history 0 refs)).step t 0 xs).2 := by
  simp only [appendProgram, Resources.bind_value, length_value, snoc_value, evalMeasured_value,
    read_value, step]

/-- Header allocation is counted at the actual state constructor. -/
def tickMeasured (s : State) : Measured State :=
  Resources.bind (appendProgram [] onesBody s.ones) fun os =>
  Resources.bind (appendProgram s.ones sumsSource s.sums) fun ss =>
  Resources.bind (appendProgram s.sums triangularBody s.triangular) fun ts =>
    (⟨os, ss, ts⟩, (0, 0, 1))

@[simp] theorem tickMeasured_value (s : State) : (tickMeasured s).1 = tick s := by
  simp only [tickMeasured, Resources.bind_value, appendProgram_value, tick]
  rfl

def setup : Measured State := (empty, (0, 0, 1))

def extendMeasured : Nat → State → Measured State
  | 0, s => Resources.pure s
  | n + 1, s => Resources.bind (tickMeasured s) (extendMeasured n)

@[simp] theorem extendMeasured_value (n : Nat) (s : State) :
    (extendMeasured n s).1 = extend n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [extendMeasured, extend, Resources.bind, ih]

/-- Each baseline request starts afresh. Empty output needs no state allocation. -/
def recompute : Nat → Measured (List Nat)
  | 0 => ([], 0)
  | n + 1 => Resources.bind setup fun s =>
      Resources.bind (extendMeasured (n + 1) s) fun t => copy (n + 1) t.triangular

/-- Smaller and repeated demands copy an existing prefix; larger demands extend
only the missing suffix. Measuring length and the output copy is intentional. -/
def retain (n : Nat) (s : State) : Measured (List Nat × State) :=
  Resources.bind (length s.triangular) fun k =>
  Resources.bind (extendMeasured (n - k) s) fun t =>
  Resources.bind (copy n t.triangular) fun out => Resources.pure (out, t)

theorem recompute_value (n : Nat) :
    (recompute n).1 = (List.range n).map Examples.triangular := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [recompute, Resources.bind_value, setup, extendMeasured_value, copy_value]
    rw [computed_prefix]
    simp

theorem retain_state (n : Nat) (s : State) :
    (retain n s).1.2 = extend (n - s.triangular.length) s := by
  simp [retain, Resources.bind, Resources.pure]

theorem retain_valid (n : Nat) (s : State) (h : Valid s) : Valid (retain n s).1.2 := by
  rw [retain_state]
  exact extend_valid _ _ h

theorem retain_length (n : Nat) (s : State) :
    (retain n s).1.2.triangular.length = max s.triangular.length n := by
  rw [retain_state, extend_length]
  omega

theorem retain_value (n : Nat) (s : State) (h : Valid s) :
    (retain n s).1.1 = (List.range n).map Examples.triangular := by
  simp only [retain, Resources.bind_value, length_value, extendMeasured_value, copy_value, Resources.pure]
  rw [prefix_eq (extend_valid _ s h).triangular, ← List.map_take, List.take_range, extend_length]
  congr 2
  omega

theorem repeated_state (n : Nat) (s : State) (h : n ≤ s.triangular.length) :
    (retain n s).1.2 = s := by
  rw [retain_state, Nat.sub_eq_zero_of_le h]
  rfl


/-- The workload consumes each returned prefix before the next request. The
measured copy is still performed; output persistence belongs to the caller. -/
def retainedStep (n : Nat) (s : State) : Measured State :=
  Resources.bind (retain n s) (fun r => Resources.pure r.2)

def retainedWorkload (ns : List Nat) : Measured State :=
  Resources.bind setup (Resources.run retainedStep ns)

def recomputedStep (n : Nat) (_ : Unit) : Measured Unit :=
  Resources.bind (recompute n) (fun _ => Resources.pure ())

def recomputedWorkload (ns : List Nat) : Measured Unit :=
  Resources.run recomputedStep ns ()

theorem workload_valid (ns : List Nat) : Valid (retainedWorkload ns).1 := by
  apply Resources.run_invariant retainedStep Valid
  · intro n s h
    exact retain_valid n s h
  · exact empty_valid

theorem workload_append (ns ms : List Nat) (s : State) :
    Resources.run retainedStep (ns ++ ms) s =
      Resources.bind (Resources.run retainedStep ns s) (Resources.run retainedStep ms) :=
  Resources.run_append _ _ _ _

theorem workload_reweight {D : Type} [AddMonoid D] (tariff : Work →+ D)
    (ns : List Nat) (s : State) :
    Resources.reweight tariff (Resources.run retainedStep ns s) =
      Resources.run (fun n s => Resources.reweight tariff (retainedStep n s)) ns s :=
  Resources.reweight_run tariff retainedStep ns s

/-- Retained list cells plus one header, excluding caller-owned emitted outputs
and obsolete persistent versions. This grows with the largest demand. -/
def live (s : State) : Nat := s.ones.length + s.sums.length + s.triangular.length + 1

theorem live_valid (s : State) (h : Valid s) : live s = 3 * s.triangular.length + 1 := by
  unfold live
  rw [h.lengths₁, h.lengths₂]
  omega

theorem live_after (n : Nat) (s : State) (h : Valid s) :
    live (retain n s).1.2 = 3 * max s.triangular.length n + 1 := by
  rw [live_valid _ (retain_valid n s h), retain_length]

theorem length_cost (xs : List Nat) : (length xs).2 = (0, xs.length, 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [length, Resources.bind, ih, Prod.mk_add_mk]

theorem snoc_cost (xs : List Nat) (a : Nat) :
    (snoc xs a).2 = (0, xs.length, xs.length + 1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [snoc, Resources.bind, ih, Prod.mk_add_mk]

theorem copy_cost (n : Nat) (xs : List Nat) :
    (copy n xs).2 = (0, min n xs.length, min n xs.length) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => cases xs <;> simp [copy, Resources.bind, ih, Prod.mk_add_mk]; rfl

end Applications.GuardedStreams
