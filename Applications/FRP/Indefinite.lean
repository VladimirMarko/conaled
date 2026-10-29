import Applications.Circuits.Execution
import Applications.FRP.FiniteDelay

/-! Finite Boolean circuits with initialized state form a sufficient class of
indefinitely serviceable synchronous programs in the circuit arena model.
No request IDs, logical clocks or histories occur in executable state. -/
namespace FRPSpec.Indefinite
open FirstOrderCompiler Applications.Circuits Progress Progress.Feedback

/-- State is an explicit one-tick delay. The body has no instantaneous loop. -/
structure Program (a b s : Ty) where
  body : Circuit (.prod a s) (.prod b s)
  initial : Val Bool s

namespace Program
variable {a b c d s t : Ty}

def machine (p : Program a b s) : Initialized (Val Bool a) (Val Bool b) (Val Bool s) :=
  ⟨p.body.execute,p.initial⟩

def meaning (p : Program a b s) : Initialized (Val Bool a) (Val Bool b) (Val Bool s) :=
  ⟨p.body.digital.value,p.initial⟩

theorem correct (p : Program a b s) : p.machine = p.meaning := by
  have h : p.body.execute = p.body.digital.value := funext (Circuit.execute_correct p.body)
  simp only [machine, meaning, h]

/-- Values have no variable-sized payload. This observation counts retained
Boolean cells; arena frames and temporary values are accounted separately. -/
def retained (_ : Val Bool s) : Nat := cells s

/-- Every admitted input stream and every prefix share a single static bound.
The bound also includes every internal allocation point of the next step. -/
theorem uniform (p : Program a b s) :
    ∀ (input : Stream (Val Bool a)) (n k : Nat),
      retained (state p.machine input n) + (p.body.allocations.take k).sum ≤
        cells s + p.body.arena := by
  intro input n k
  exact Nat.add_le_add_left (p.body.arena_prefix k) _

/-- A finite operational derivation produces the next output at every prefix.
This is independent of whether an external input/scheduler/sink cooperates. -/
theorem next (p : Program a b s) (input : Stream (Val Bool a)) (n : Nat) :
    Circuit.Executes p.body (input n,state p.machine input n)
      (output p.machine input n,state p.machine input (n+1)) p.body.work p.body.arena :=
  p.body.executes _

/-- A fixed-size body permits every finite number of steps and one more, with
semantic correctness, constant per-step work and a uniform internal-space bound. -/
theorem service (p : Program a b s) (input : Stream (Val Bool a)) :
    (∀ n, output p.machine input n = output p.meaning input n) ∧
    (∀ n, Circuit.Executes p.body (input n,state p.machine input n)
      (output p.machine input n,state p.machine input (n+1)) p.body.work p.body.arena) ∧
    ∀ n k, retained (state p.machine input n) + (p.body.allocations.take k).sum ≤
      cells s + p.body.arena :=
  ⟨by rw [correct]; exact fun _ => rfl,p.next input,p.uniform input⟩

/-- Finite readiness/service/acceptance delays are the environmental premises.
No completion time or output stream is supplied by this record. Absence of input,
unfair scheduling or a blocked sink cannot supply the corresponding finite wait. -/
structure Environment where
  inputWait : Nat → Nat
  schedulerWait : Nat → Nat
  sinkWait : Nat → Nat

/-- One input admission and one output acceptance delimit an evaluation. Waits
are not charged as active work. `+ 1` records the final acceptance transition. -/
def duration (p : Program a b s) (env : Environment) (n : Nat) : Nat :=
  env.inputWait n + env.schedulerWait n + p.body.work + env.sinkWait n + 1

def starts (p : Program a b s) (env : Environment) : Nat → Nat
  | 0 => 0
  | n+1 => starts p env n + duration p env n

/-- A service round waits for input, waits for scheduling, performs a finite
circuit evaluation, and waits for sink acceptance. The next round cannot start
until the output has been accepted. Logical times are never executable state. -/
inductive Round (p : Program a b s) (inputWait schedulerWait sinkWait : Nat) :
    Nat → Val Bool a → Val Bool s → Val Bool b → Val Bool s → Nat → Prop where
  | service {x st y st' start} (evaluation : Circuit.Executes p.body (x,st) (y,st') w arena) :
      Round p inputWait schedulerWait sinkWait start x st y st'
        (start + (inputWait + schedulerWait + w + sinkWait + 1))

/-- The operational run is constructed from finite environmental delays and
local evaluation, rather than assumed as an infinite completion schedule. -/
theorem scheduled_run (p : Program a b s) (env : Environment)
    (input : Stream (Val Bool a)) (n : Nat) :
    Round p (env.inputWait n) (env.schedulerWait n) (env.sinkWait n)
      (p.starts env n) (input n) (state p.machine input n)
      (output p.machine input n) (state p.machine input (n+1)) (p.starts env (n+1)) :=
  .service (p.next input n)

/-- Infinitely many accepted outputs follow when each environmental wait is
finite. The constructed run is backpressured, so there is no queue of outputs. -/
theorem productive (p : Program a b s) (env : Environment)
    (input : Stream (Val Bool a)) (deadline : Nat) :
    ∃ n, deadline < p.starts env (n+1) ∧
      Round p (env.inputWait n) (env.schedulerWait n) (env.sinkWait n)
        (p.starts env n) (input n) (state p.machine input n)
        (output p.machine input n) (state p.machine input (n+1)) (p.starts env (n+1)) := by
  have lower : ∀ n, n ≤ p.starts env n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => simp only [starts, duration]; omega
  exact ⟨deadline,lt_of_lt_of_le (Nat.lt_succ_self deadline) (lower _),p.scheduled_run env input deadline⟩

def pure (f : Circuit a b) : Program a b .unit :=
  ⟨.pair (.compose f .first) .terminate,()⟩

def delay (seed : Val Bool a) : Program a a a := ⟨.pair .second .first,seed⟩

/-- Serial evaluation retains one fixed-size intermediate. It never enqueues. -/
def seq (p : Program a b s) (q : Program b c t) : Program a c (.prod s t) where
  initial := (p.initial,q.initial)
  body := .compose
    (.pair (.compose .first .first) (.pair .second (.compose .second .first)))
    (.compose
      (.pair (.compose q.body (.pair (.compose .first .first) .second))
        (.compose .second .first))
      (.pair (.compose p.body (.pair .first (.compose .first .second)))
        (.compose .second .second)))

/-- Both branches are evaluated synchronously in a fixed order. -/
def par (p : Program a b s) (q : Program c d t) : Program (.prod a c) (.prod b d) (.prod s t) where
  initial := (p.initial,q.initial)
  body := .compose
    (.pair (.pair (.compose .first .first) (.compose .first .second))
      (.pair (.compose .second .first) (.compose .second .second)))
    (.pair (.compose p.body (.pair (.compose .first .first) (.compose .first .second)))
      (.compose q.body (.pair (.compose .second .first) (.compose .second .second))))

theorem pure_machine (f : Circuit a b) :
    (pure f).machine = Progress.Feedback.pure f.execute := rfl

theorem seq_machine (p : Program a b s) (q : Program b c t) :
    (p.seq q).machine = Progress.Feedback.seq p.machine q.machine := rfl

theorem par_machine (p : Program a b s) (q : Program c d t) :
    (p.par q).machine = Progress.Feedback.par p.machine q.machine := rfl

/-- Wiring overhead is fixed by the constructors, independent of stream length. -/
theorem seq_work (p : Program a b s) (q : Program b c t) :
    (p.seq q).body.work = p.body.work + q.body.work + 31 := by
  simp only [seq, Circuit.work]
  omega

theorem par_work (p : Program a b s) (q : Program c d t) :
    (p.par q).body.work = p.body.work + q.body.work + 33 := by
  simp only [par, Circuit.work]
  omega

/-- The original compiler can supply any finite circuit body. The wrapper only
rearranges its context; it does not interpret source syntax at every tick. -/
def compiled (p : ReactiveCompiler.Compiled Circuit.target a b s) : Program a b s where
  initial := p.seed.execute ()
  body := .compose p.body (.pair (.pair .terminate .second) .first)

theorem compiled_machine (p : ReactiveCompiler.Compiled Circuit.target a b s) :
    (compiled p).machine = ReactiveCompiler.realize Circuit.target Circuit.execute p := rfl

theorem compiled_source (seed : Term Gate [] s) (body : Term Gate [a,s] (.prod b s)) :
    (compiled (ReactiveCompiler.compile Circuit.target seed body)).machine =
      ReactiveCompiler.source Gate.meaning seed body := by
  rw [compiled_machine]
  have realization (p : ReactiveCompiler.Compiled Circuit.target a b s) :
      ReactiveCompiler.realize Circuit.target Circuit.execute p =
        ReactiveCompiler.realize Circuit.target Circuit.sound.denote p := by
    have hb : Circuit.execute p.body = Circuit.sound.denote p.body :=
      funext (fun x => Circuit.execute_correct p.body x)
    have hs : Circuit.execute p.seed = Circuit.sound.denote p.seed :=
      funext (fun x => Circuit.execute_correct p.seed x)
    simp only [ReactiveCompiler.realize, hb, hs]
  rw [realization]
  exact ReactiveCompiler.realize_compile Circuit.target Circuit.sound seed body

/-- A different backend supplies local observations, initialization and transition
simulation. The existing stream theorem then reuses every client observation. -/
theorem transport (p : Program a b s) {A B S : Type}
    (backend : Initialized A B S) (I : Val Bool a → A → Prop)
    (R : Val Bool s → S → Prop) (O : Val Bool b → B → Prop)
    (initial : R p.initial backend.initial)
    (step : ∀ x y u v, I x y → R u v →
      O (p.machine.step (x,u)).1 (backend.step (y,v)).1 ∧
      R (p.machine.step (x,u)).2 (backend.step (y,v)).2)
    (input : Stream (Val Bool a)) (other : Stream A) (inputs : ∀ n, I (input n) (other n)) :
    (∀ n, R (state p.machine input n) (state backend other n)) ∧
      ∀ n, O (output p.machine input n) (output backend other n) :=
  Progress.Feedback.transport p.machine backend I R O initial step input other inputs

/-- Transfer a uniform retained-state bound after local backend simulation.
The backend still owes its own finite transition-work and temporary-space proof. -/
theorem transport_bound (p : Program a b s) {S : Type}
    (backend : Initialized (Val Bool a) (Val Bool b) S)
    (R : Val Bool s → S → Prop) (initial : R p.initial backend.initial)
    (step : ∀ x u v, R u v →
      (p.machine.step (x,u)).1 = (backend.step (x,v)).1 ∧
      R (p.machine.step (x,u)).2 (backend.step (x,v)).2)
    (cost : S → Nat) (reweight : Nat → Nat) (mono : Monotone reweight)
    (compare : ∀ u v, R u v → cost v ≤ reweight (retained u))
    (input : Stream (Val Bool a)) :
    ∀ n, cost (state backend input n) ≤ reweight (cells s) := by
  have related := (p.transport backend Eq R Eq initial
    (by intro x y u v h; subst y; exact step x u v) input input (fun _ => rfl)).1
  let source : Set (Val Bool s) := {u | ∃ n, u = state p.machine input n}
  let target : Set S := {v | ∃ n, v = state backend input n}
  have cover : Interaction.Refines R source target := by
    rintro v ⟨n,rfl⟩
    exact ⟨_,⟨n,rfl⟩,related n⟩
  have bounded := cover.bound retained cost reweight mono compare (cells s)
    (fun _ _ => Nat.le_refl _)
  intro n
  exact bounded _ ⟨n,rfl⟩

end Program

/-- The nonempty witness uses the already compiled #231 delay semantics. -/
def delay : Program .base .base .base := Program.delay false

theorem delay_compiled : delay.machine = FiniteDelay.machine := FiniteDelay.correct.symm

def twice := delay.seq delay

theorem twice_output (input : Stream Bool) :
    output twice.machine input = output FiniteDelay.machine (output FiniteDelay.machine input) := by
  rw [twice, Program.seq_machine, delay_compiled]
  exact seq_output _ _ _

end FRPSpec.Indefinite
