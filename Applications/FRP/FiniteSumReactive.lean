import Applications.FRP.FiniteSumAdmission

/-! Initialized sum programs become the existing finite-circuit service class.
Admission rejects noncanonical external values before executing a tick. -/
namespace FRPSpec.FiniteSum
open Applications.Circuits Progress.Feedback

structure Source (a b s : Ty) where
  seed : Term [] s
  body : Term [a,s] (.prod b s)

namespace Source
variable {a b s : Ty}

def meaning (p : Source a b s) : Initialized (Value a) (Value b) (Value s) where
  initial := eval p.seed ()
  step := fun (x,st) => eval p.body (((),st),x)

/-- Reuse the initialized circuit wrapper; the only new compiler is `lower`. -/
def compiled (p : Source a b s) :
    ReactiveCompiler.Compiled Circuit.target a.storage b.storage s.storage :=
  ⟨lower p.seed,lower p.body⟩

def program (p : Source a b s) : Indefinite.Program a.storage b.storage s.storage :=
  Indefinite.Program.compiled p.compiled

@[simp] theorem initial_correct (p : Source a b s) :
    p.program.initial = encode p.meaning.initial := lower_correct p.seed ()

@[simp] theorem step_correct (p : Source a b s) (x : Value a) (st : Value s) :
    p.program.machine.step (encode x,encode st) =
      (encode (p.meaning.step (x,st)).1,encode (p.meaning.step (x,st)).2) :=
  lower_correct p.body (((),st),x)

/-- The relation covers arbitrary accepted external lists, preserving order and
final retained state. The source runner never invokes circuit execution. -/
theorem run_correct (p : Source a b s) (xs : List (Value a)) (raw : List (Bits a))
    (inputs : List.Forall₂ (fun x bits => decode a bits = some x) xs raw) :
    List.Forall₂ (fun y bits => decode b bits = some y)
      (run p.meaning.mealy p.meaning.initial xs).1
      (run p.program.machine.mealy p.program.initial raw).1 ∧
    decode s (run p.program.machine.mealy p.program.initial raw).2 =
      some (run p.meaning.mealy p.meaning.initial xs).2 := by
  refine run_related p.meaning.mealy p.program.machine.mealy
    (fun x bits => decode a bits = some x)
    (fun st bits => decode s bits = some st)
    (fun y bits => decode b bits = some y) ?_ inputs ?_
  · intro x bits st stored hx hs
    have hx' := (decode_iff a bits x).mp hx
    have hs' := (decode_iff s stored st).mp hs
    subst bits; subst stored
    change decode b (p.program.machine.step (encode x,encode st)).1 = _ ∧
      decode s (p.program.machine.step (encode x,encode st)).2 = _
    rw [p.step_correct]
    exact ⟨decode_encode b _,decode_encode s _⟩
  · rw [p.initial_correct]; exact decode_encode s _

theorem encoded_inputs (xs : List (Value a)) :
    List.Forall₂ (fun x bits => decode a bits = some x) xs (xs.map encode) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (decode_encode a x) ih

/-- One bounded external admission. Failure does not advance or reset state. -/
def tick (p : Source a b s) (input : Bits a) (state : Bits s) :
    Option (Bits b × Bits s) :=
  if (checks a s).execute (input,state) then some (p.program.body.execute (input,state)) else none

theorem tick_encoded (p : Source a b s) (x : Value a) (st : Value s) :
    p.tick (encode x) (encode st) = some
      (encode (p.meaning.step (x,st)).1,encode (p.meaning.step (x,st)).2) := by
  have hc := (checks_correct a s (encode x) (encode st)).mpr
    ⟨valid_encode a x,valid_encode s st⟩
  simp only [tick, hc, ↓reduceIte]
  exact congrArg some (p.step_correct x st)

theorem tick_reject (p : Source a b s) (input : Bits a) (state : Bits s) :
    p.tick input state = none ↔ ¬ (Valid a input ∧ Valid s state) := by
  by_cases hc : (checks a s).execute (input,state) = true
  · have hv := (checks_correct a s input state).mp hc
    simp [tick, hc, hv]
  · have hv : ¬ (Valid a input ∧ Valid s state) := fun h =>
      hc ((checks_correct a s input state).mpr h)
    simp [tick, hc, hv]

theorem tick_preserves (p : Source a b s) (input : Bits a) (state : Bits s)
    (hi : Valid a input) (hs : Valid s state) :
    Valid b (p.program.body.execute (input,state)).1 ∧
      Valid s (p.program.body.execute (input,state)).2 := by
  rw [← hi, ← hs]
  change Valid b (p.program.machine.step _).1 ∧ Valid s (p.program.machine.step _).2
  rw [p.step_correct]
  exact ⟨valid_encode b _,valid_encode s _⟩

/-- The checked tick has one branch dispatch, a validator run and, on success,
one transition run. No source evaluator occurs in this operational contract. -/
inductive TickExecutes (p : Source a b s) (input : Bits a) (st : Bits s) :
    Option (Bits b × Bits s) → Nat → Nat → Prop where
  | accept (hc : Circuit.Executes (checks a s) (input,st) true wc ac)
      (hb : Circuit.Executes p.program.body (input,st) result wb ab) :
      TickExecutes p input st (some result) (wc + wb + 1) (ac + ab + 1)
  | reject (hc : Circuit.Executes (checks a s) (input,st) false wc ac) :
      TickExecutes p input st none (wc + 1) (ac + 1)

def tickWork (p : Source a b s) : Nat := (checks a s).work + p.program.body.work + 1
def tickArena (p : Source a b s) : Nat := (checks a s).arena + p.program.body.arena + 1

theorem accepted_tick (p : Source a b s) (input : Bits a) (st : Bits s)
    (hi : Valid a input) (hs : Valid s st) :
    TickExecutes p input st (p.tick input st) p.tickWork p.tickArena := by
  have h := (checks_correct a s input st).mpr ⟨hi,hs⟩
  have hc := (checks a s).executes (input,st)
  rw [h] at hc
  simp only [tick, h, ↓reduceIte]
  exact .accept hc (p.program.body.executes _)

theorem rejected_tick (p : Source a b s) (input : Bits a) (st : Bits s)
    (h : ¬ (Valid a input ∧ Valid s st)) :
    TickExecutes p input st none ((checks a s).work + 1) ((checks a s).arena + 1) := by
  have hc := (checks a s).executes (input,st)
  have hn : (checks a s).execute (input,st) = false := by
    cases he : (checks a s).execute (input,st)
    · rfl
    · exact False.elim (h ((checks_correct a s input st).mp he))
  rw [hn] at hc
  exact .reject hc

/-- The conservative arena retains validator allocations until transition end.
Every allocation prefix, plus the state between ticks, fits the static bound. -/
theorem checked_uniform (p : Source a b s) (input : Progress.Stream (Bits a)) (n k : Nat) :
    Indefinite.Program.retained (state p.program.machine input n) +
      (((checks a s).allocations ++ p.program.body.allocations ++ [1]).take k).sum ≤
        cells s.storage + p.tickArena := by
  have h : (((checks a s).allocations ++ p.program.body.allocations ++ [1]).take k).sum ≤
      ((checks a s).allocations ++ p.program.body.allocations ++ [1]).sum :=
    by
      have hsplit := congrArg List.sum (List.take_append_drop k
        ((checks a s).allocations ++ p.program.body.allocations ++ [1]))
      rw [List.sum_append] at hsplit
      omega
  simpa [Indefinite.Program.retained, tickArena, List.sum_append, Circuit.allocations_sum, Nat.add_assoc]
    using Nat.add_le_add_left h (cells s.storage)

/-- Work and all temporary arena allocations refer to the actual lowered body. -/
theorem finite_step (p : Source a b s) (input : Bits a) (state : Bits s) :
    Circuit.Executes p.program.body (input,state)
      (p.program.body.execute (input,state)) p.program.body.work p.program.body.arena :=
  p.program.body.executes _

theorem uniform (p : Source a b s) (input : Progress.Stream (Bits a)) (n k : Nat) :
    Indefinite.Program.retained (state p.program.machine input n) +
      (p.program.body.allocations.take k).sum ≤ cells s.storage + p.program.body.arena :=
  p.program.uniform input n k

/-- Conditional progress uses finite input, scheduler and sink waits. It asserts
no deadline or physical allocation bound for a host implementation. -/
theorem productive (p : Source a b s) (env : Indefinite.Program.Environment)
    (input : Progress.Stream (Bits a)) (deadline : Nat) :
    ∃ n, deadline < p.program.starts env (n+1) ∧
      Indefinite.Program.Round p.program (env.inputWait n) (env.schedulerWait n) (env.sinkWait n)
        (p.program.starts env n) (input n) (state p.program.machine input n)
        (output p.program.machine input n) (state p.program.machine input (n+1))
        (p.program.starts env (n+1)) := p.program.productive env input deadline

/-- Source observations and valid retained state hold at every accepted prefix. -/
theorem stream_correct (p : Source a b s) (input : Progress.Stream (Value a)) :
    (∀ n, state p.program.machine (fun k => encode (input k)) n =
      encode (state p.meaning input n)) ∧
    ∀ n, output p.program.machine (fun k => encode (input k)) n =
      encode (output p.meaning input n) := by
  apply transport p.meaning p.program.machine
    (fun x bits => bits = encode x) (fun st bits => bits = encode st)
    (fun y bits => bits = encode y) p.initial_correct
  · intro x bits st stored hx hs
    subst bits; subst stored
    rw [p.step_correct]
    exact ⟨rfl,rfl⟩
  · intro n; rfl

/-- Validator execution and the branch dispatch take finite modeled work before
body evaluation. External scheduler waiting remains a separate summand. -/
def checkedEnvironment (_p : Source a b s) (env : Indefinite.Program.Environment) :
    Indefinite.Program.Environment where
  inputWait := env.inputWait
  schedulerWait n := env.schedulerWait n + (checks a s).work + 1
  sinkWait := env.sinkWait

theorem checked_duration (p : Source a b s) (env : Indefinite.Program.Environment) (n : Nat) :
    p.program.duration (p.checkedEnvironment env) n =
      env.inputWait n + env.schedulerWait n + p.tickWork + env.sinkWait n + 1 := by
  simp only [Indefinite.Program.duration, checkedEnvironment, tickWork]
  omega

/-- Encoded source streams pass admission at every prefix, so validation cannot
introduce a rejected round. Work is the actual validator plus lowered transition. -/
theorem checked_ticks (p : Source a b s) (input : Progress.Stream (Value a)) (n : Nat) :
    TickExecutes p (encode (input n)) (state p.program.machine (fun k => encode (input k)) n)
      (p.tick (encode (input n)) (state p.program.machine (fun k => encode (input k)) n))
      p.tickWork p.tickArena := by
  apply p.accepted_tick
  · exact valid_encode a _
  · rw [(p.stream_correct input).1 n]
    exact valid_encode s _

/-- Existing backpressured service scheduling with finite validation included.
Together with `checked_ticks`, this supplies conditional indefinite service. -/
theorem checked_productive (p : Source a b s) (env : Indefinite.Program.Environment)
    (input : Progress.Stream (Value a)) (deadline : Nat) :
    ∃ n, deadline < p.program.starts (p.checkedEnvironment env) (n+1) ∧
      Indefinite.Program.Round p.program (env.inputWait n)
        (env.schedulerWait n + (checks a s).work + 1) (env.sinkWait n)
        (p.program.starts (p.checkedEnvironment env) n) (encode (input n))
        (state p.program.machine (fun k => encode (input k)) n)
        (output p.program.machine (fun k => encode (input k)) n)
        (state p.program.machine (fun k => encode (input k)) (n+1))
        (p.program.starts (p.checkedEnvironment env) (n+1)) :=
  p.program.productive (p.checkedEnvironment env) (fun k => encode (input k)) deadline

end Source
end FRPSpec.FiniteSum
