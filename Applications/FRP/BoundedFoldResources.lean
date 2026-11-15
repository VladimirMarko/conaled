import Applications.FRP.BoundedFold

/-! Owned list cells and iteration arenas. Allocation traces are proof data;
`execute` retains neither a trace nor a history of outputs. -/
namespace FRPSpec.BoundedFold
open Applications.Circuits Progress Progress.Feedback

/-- Two cells per list node, a terminator, old state, accumulator, bounded cursor,
and control frame. The whole batch remains owned throughout its tick. -/
def resident (n : Nat) := 2*n + 5

def storage (capacity : Nat) := resident capacity + code.arena + 2

def work (n : Nat) := n * (code.work + 3) + 3

/-- Every internal circuit allocation prefix, then a result copy while the old
accumulator and arena remain live, then reclamation before the next iteration. -/
def iterationTrace (owned : Nat) : List Nat :=
  ((List.range (code.allocations.length+1)).map
    (fun k => resident owned + (code.allocations.take k).sum)) ++
    [resident owned + code.arena + 1, resident owned]

def liveTrace (owned : Nat) (s : Bool) : List Bool → List Nat
  | [] => [resident owned + 2, 1]
  | x::xs => iterationTrace owned ++ liveTrace owned (code.execute (((),s),x)) xs

/-- This judgment follows actual body executions and the lifetime transitions.
The final two cells copy output and next state before acceptance releases batch,
old state, accumulator, cursor and frame. The remaining cell is next state. -/
inductive Executes (owned : Nat) : List Bool → Bool → Bool → Nat → List Nat → Prop where
  | done (s : Bool) : Executes owned [] s s 3 [resident owned + 2, 1]
  | step {x xs s next result w trace}
      (fits : (x::xs).length ≤ owned)
      (body : Circuit.Executes code (((),s),x) next code.work code.arena)
      (rest : Executes owned xs next result w trace) :
      Executes owned (x::xs) s result (code.work + 3 + w) (iterationTrace owned ++ trace)

theorem executes (owned : Nat) (xs : List Bool) (s : Bool) (fits : xs.length ≤ owned) :
    Executes owned xs s (execute s xs) (work xs.length) (liveTrace owned s xs) := by
  induction xs generalizing s with
  | nil => exact .done s
  | cons x xs ih =>
    have h := Executes.step fits (code.executes (((),s),x))
      (ih (code.execute (((),s),x)) (by simp only [List.length_cons] at fits; omega))
    simpa only [execute, List.foldl_cons, List.length_cons, work, Nat.add_mul,
      Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, liveTrace] using h

theorem Executes.result {owned xs s r w trace} (h : Executes owned xs s r w trace) :
    r = execute s xs ∧ w = work xs.length ∧ trace = liveTrace owned s xs := by
  induction h with
  | done => exact ⟨rfl,rfl,rfl⟩
  | step _ hb hr ih =>
    obtain ⟨rfl,_,_⟩ := hb.result
    obtain ⟨rfl,rfl,rfl⟩ := ih
    refine ⟨rfl,?_,rfl⟩
    simp [work, Nat.add_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem iteration_bound (h : owned ≤ capacity) (v : Nat) (hv : v ∈ iterationTrace owned) :
    v ≤ storage capacity := by
  simp only [iterationTrace, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with ⟨k,_,rfl⟩ | hcopy | hreclaim
  · have hk := code.arena_prefix k
    simp only [storage, resident] at *
    omega
  · subst v; unfold storage resident; omega
  · subst v; unfold storage resident; omega

theorem trace_bound (h : owned ≤ capacity) (xs : List Bool) (s : Bool)
    (v : Nat) (hv : v ∈ liveTrace owned s xs) : v ≤ storage capacity := by
  induction xs generalizing s with
  | nil =>
    simp only [liveTrace,List.mem_cons,List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> unfold storage resident <;> omega
  | cons x xs ih =>
    simp only [liveTrace,List.mem_append] at hv
    exact hv.elim (iteration_bound h v) (ih _)

/-- One bound for every tick and every allocation point, with no prefix length
in its right hand side. Capacity is fixed installation data. -/
theorem uniform (input : Stream (Batch capacity)) (n : Nat) :
    ∃ trace, Executes (input n).val.length (input n).val
      (state (machine capacity) input n) (state (machine capacity) input (n+1))
      (work (input n).val.length) trace ∧ ∀ v ∈ trace, v ≤ storage capacity := by
  exact ⟨_,executes _ _ _ (Nat.le_refl _),trace_bound (input n).property _ _⟩

theorem work_bound (b : Batch capacity) : work b.val.length ≤ work capacity := by
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ b.property) _

/-- Input/scheduler/sink delays are finite premises, not a supplied completion
schedule. Input is already admitted; ingestion has its separate bounded cost. -/
abbrev Environment := Indefinite.Program.Environment

def duration (env : Environment) (input : Stream (Batch capacity)) (n : Nat) :=
  env.inputWait n + env.schedulerWait n + work (input n).val.length + env.sinkWait n + 1

def starts (env : Environment) (input : Stream (Batch capacity)) : Nat → Nat
  | 0 => 0
  | n+1 => starts env input n + duration env input n

inductive Round (inputWait schedulerWait sinkWait : Nat) :
    Nat → List Bool → Bool → Bool → Bool → Nat → Prop where
  | service {xs s next start w trace} (eval : Executes xs.length xs s next w trace) :
      Round inputWait schedulerWait sinkWait start xs s s next
        (start + (inputWait + schedulerWait + w + sinkWait + 1))

theorem scheduled (env : Environment) (input : Stream (Batch capacity)) (n : Nat) :
    Round (env.inputWait n) (env.schedulerWait n) (env.sinkWait n)
      (starts env input n) (input n).val (state (machine capacity) input n)
      (output (machine capacity) input n) (state (machine capacity) input (n+1))
      (starts env input (n+1)) := .service (executes _ _ _ (Nat.le_refl _))

theorem productive (env : Environment) (input : Stream (Batch capacity)) (deadline : Nat) :
    ∃ n, deadline < starts env input (n+1) ∧
      Round (env.inputWait n) (env.schedulerWait n) (env.sinkWait n)
        (starts env input n) (input n).val (state (machine capacity) input n)
        (output (machine capacity) input n) (state (machine capacity) input (n+1))
        (starts env input (n+1)) := by
  have lower : ∀ n, n ≤ starts env input n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => simp only [starts,duration]; omega
  exact ⟨deadline,by have := lower (deadline+1); omega,scheduled env input deadline⟩

/-- These failures are representation-specific. Unary exact naturals and exact
retained histories require one cell per constructor; parity summaries do not. -/
theorem growing_counter : ¬ ∃ bound : Nat, ∀ n : Nat, (List.replicate n ()).length ≤ bound := by
  rintro ⟨bound,h⟩
  have hb := h (bound+1)
  simp only [List.length_replicate] at hb
  omega

theorem retained_history : ¬ ∃ bound : Nat, ∀ xs : List Bool, xs.length ≤ bound := by
  rintro ⟨bound,h⟩
  have := h (List.replicate (bound+1) false)
  simp only [List.length_replicate] at this
  omega

/-- Every list terminates by `visits`; no single work bound covers all lists. -/
theorem unbounded_iteration : ¬ ∃ bound : Nat, ∀ xs : List Bool, work xs.length ≤ bound := by
  rintro ⟨bound,h⟩
  have hb := h (List.replicate (bound+1) false)
  simp only [List.length_replicate,work] at hb
  have : 1 ≤ code.work + 3 := by omega
  have hm := Nat.mul_le_mul_left (bound+1) this
  omega

end FRPSpec.BoundedFold
