import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Interval
import Mathlib.Order.Monotone.Basic

set_option autoImplicit false
set_option warningAsError true

/-!
# Native simulation by print-and-move transitions

Each target action writes a symbol and moves exactly one square. The adapter
preserves the native alphabet, supplied start and complete physical tape at
normal control boundaries. A native move costs one target action; a native
write costs two, with its rightward excursion and return included. A final
decision action reaches an accepting or rejecting control and moves the tape
right. For a stopped native endpoint with a Boolean output, a native bound `B`
therefore yields a deciding bound `2 * B + 1`.

The trace API observes every actual target prefix, including write excursions
and the final decision. It bounds the input-inclusive visited interval by
`max N 1 + U` for target time `U`. This interval observation does not assert
bounded support for an arbitrary initial tape.
-/

namespace Resources.TuringSimulation.PrintMove

open Function Turing

/-- One complete conventional transition, executed as print followed by move. -/
structure Action (Γ Q : Type*) where
  next : Q
  letter : Γ
  direction : Dir

/-- Optional extension of a conventional transition table to terminal states.
The adapter below proves totality on precisely its nonterminal controls. -/
abbrev Machine (Γ Q : Type*) := Q → Γ → Option (Action Γ Q)

abbrev Cfg (Γ Q : Type*) [Inhabited Γ] := TM0.Cfg Γ Q

/-- The real combined action, on the exact native physical tape type. -/
def step {Γ Q : Type*} [Inhabited Γ] (M : Machine Γ Q) (c : Cfg Γ Q) :
    Option (Cfg Γ Q) :=
  (M c.q c.Tape.head).map (fun a => ⟨a.next, (c.Tape.write a.letter).move a.direction⟩)

/-- Literal initialization with the supplied control, without an ambient
control-default assumption or a whole-word input encoder. -/
def init {Γ Q : Type*} [Inhabited Γ] (start : Q) (input : List Γ) : Cfg Γ Q :=
  ⟨start, Tape.mk₁ input⟩

/-- Finite normal and return copies of native control, plus two terminals. -/
inductive Control (Q : Type*)
  | normal : Q → Control Q
  | returning : Q → Control Q
  | accept : Control Q
  | reject : Control Q
  deriving DecidableEq, Fintype

def controlEquiv {Q : Type*} : Control Q ≃ (Q ⊕ Q) ⊕ Bool where
  toFun
    | .normal q => .inl (.inl q)
    | .returning q => .inl (.inr q)
    | .accept => .inr true
    | .reject => .inr false
  invFun
    | .inl (.inl q) => .normal q
    | .inl (.inr q) => .returning q
    | .inr true => .accept
    | .inr false => .reject
  left_inv := by intro q; cases q <;> rfl
  right_inv := by
    intro x
    rcases x with x | b
    · rcases x with q | q <;> rfl
    · cases b <;> rfl

theorem card_control {Q : Type*} [Fintype Q] :
    Fintype.card (Control Q) = 2 * Fintype.card Q + 2 := by
  rw [Fintype.card_congr controlEquiv, Fintype.card_sum, Fintype.card_sum,
    Fintype.card_bool]
  omega

theorem normal_ne_accept {Q : Type*} (q : Q) : Control.normal q ≠ .accept := by
  intro h
  cases h

theorem normal_ne_reject {Q : Type*} (q : Q) : Control.normal q ≠ .reject := by
  intro h
  cases h

theorem accept_ne_reject {Q : Type*} : (Control.accept : Control Q) ≠ .reject := by
  intro h
  cases h

def Nonterminal {Q : Type*} (q : Control Q) : Prop := q ≠ .accept ∧ q ≠ .reject

section Adapter

variable {Γ Q : Type*} [Inhabited Q] [DecidableEq Γ]

/-- Inspect the actual native instruction. None is a real final decision
action, rather than an uncharged observation or a missing active transition. -/
def normalAction (M : TM0.Machine Γ Q) (trueLetter : Γ) (q : Q) (a : Γ) :
    Action Γ (Control Q) :=
  match M q a with
  | some (q', .move d) => ⟨.normal q', a, d⟩
  | some (q', .write b) => ⟨.returning q', b, .right⟩
  | none => ⟨if a = trueLetter then .accept else .reject, a, .right⟩

/-- The actual combined transition table. A return prints the right neighbour
unchanged before moving left; terminals have no transition. -/
def adapter (M : TM0.Machine Γ Q) (trueLetter : Γ) : Machine Γ (Control Q)
  | .normal q, a => some (normalAction M trueLetter q a)
  | .returning q, a => some ⟨.normal q, a, .left⟩
  | .accept, _ => none
  | .reject, _ => none

/-- The total transition on the published nonterminal domain. Impossible
terminal cases are eliminated by their proof, without a runtime fallback. -/
def delta (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (q : {q : Control Q // Nonterminal q}) (a : Γ) : Action Γ (Control Q) :=
  match q with
  | ⟨.normal q, _⟩ => normalAction M trueLetter q a
  | ⟨.returning q, _⟩ => ⟨.normal q, a, .left⟩
  | ⟨.accept, h⟩ => False.elim (h.1 rfl)
  | ⟨.reject, h⟩ => False.elim (h.2 rfl)

theorem adapter_eq_none_iff (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (q : Control Q) (a : Γ) :
    adapter M trueLetter q a = none ↔ q = .accept ∨ q = .reject := by
  cases q <;> simp [adapter]

theorem adapter_delta (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (q : {q : Control Q // Nonterminal q}) (a : Γ) :
    adapter M trueLetter q.val a = some (delta M trueLetter q a) := by
  rcases q with ⟨q, h⟩
  cases q with
  | normal q => rfl
  | returning q => rfl
  | accept => exact False.elim (h.1 rfl)
  | reject => exact False.elim (h.2 rfl)

end Adapter

section Boundaries

variable {Γ Q : Type*} [Inhabited Γ]

/-- Preserve the full source configuration at a normal simulation boundary. -/
def normalCfg (c : TM0.Cfg Γ Q) : Cfg Γ (Control Q) := ⟨.normal c.q, c.Tape⟩

theorem normalCfg_tape (c : TM0.Cfg Γ Q) : (normalCfg c).Tape = c.Tape := rfl

/-- The supplied start and the literal native input tape are unchanged. -/
theorem normalCfg_init (start : Q) (input : List Γ) :
    normalCfg (⟨start, Tape.mk₁ input⟩ : TM0.Cfg Γ Q) =
      init (.normal start) input := rfl

theorem normalCfg_native_init [Inhabited Q] (input : List Γ) :
    normalCfg (TM0.init input : TM0.Cfg Γ Q) = init (.normal (default : Q)) input := rfl

end Boundaries

section TapeSemantics

variable {Γ Q : Type*} [Inhabited Γ] [Inhabited Q] [DecidableEq Γ]

theorem step_delta (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (q : {q : Control Q // Nonterminal q}) (T : Tape Γ) :
    step (adapter M trueLetter) ⟨q.val, T⟩ =
      some ⟨(delta M trueLetter q T.head).next,
        (T.write (delta M trueLetter q T.head).letter).move
          (delta M trueLetter q T.head).direction⟩ := by
  simp only [step, adapter_delta, Option.map_some]

/-- One real combined action simulates a native move, preserving the complete
successor tape and the exact next normal control. -/
theorem move_step (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (q q' : Q) (T : Tape Γ) (d : Dir) (h : M q T.head = some (q', .move d)) :
    step (adapter M trueLetter) (normalCfg ⟨q, T⟩) =
      some (normalCfg ⟨q', T.move d⟩) := by
  simp only [step, normalCfg, adapter, normalAction, h, Option.map_some, Tape.write_self]

/-- The first half of an actual stationary-write simulation. -/
theorem write_first_step (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (q q' : Q) (T : Tape Γ) (a : Γ) (h : M q T.head = some (q', .write a)) :
    step (adapter M trueLetter) (normalCfg ⟨q, T⟩) =
      some ⟨.returning q', (T.write a).move .right⟩ := by
  simp only [step, normalCfg, adapter, normalAction, h, Option.map_some]

/-- A return preserves the currently scanned neighbour and moves left. -/
theorem return_step (M : TM0.Machine Γ Q) (trueLetter : Γ) (q : Q) (T : Tape Γ) :
    step (adapter M trueLetter) ⟨.returning q, T⟩ =
      some (normalCfg ⟨q, T.move .left⟩) := by
  change some (⟨.normal q, (T.write T.head).move .left⟩ : Cfg Γ (Control Q)) =
    some ⟨.normal q, T.move .left⟩
  rw [Tape.write_self]

/-- The second half restores exactly the written tape, including both tails. -/
theorem write_second_step (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (q' : Q) (T : Tape Γ) (a : Γ) :
    step (adapter M trueLetter) ⟨.returning q', (T.write a).move .right⟩ =
      some (normalCfg ⟨q', T.write a⟩) := by
  rw [return_step, Tape.move_right_left]

theorem accept_step (M : TM0.Machine Γ Q) (trueLetter : Γ) (T : Tape Γ) :
    step (adapter M trueLetter) ⟨.accept, T⟩ = none := rfl

theorem reject_step (M : TM0.Machine Γ Q) (trueLetter : Γ) (T : Tape Γ) :
    step (adapter M trueLetter) ⟨.reject, T⟩ = none := rfl

theorem step_eq_none_iff_terminal (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (c : Cfg Γ (Control Q)) :
    step (adapter M trueLetter) c = none ↔ c.q = .accept ∨ c.q = .reject := by
  rcases c with ⟨q, T⟩
  cases q <;> simp [step, adapter]

end TapeSemantics

/-- A literal one-step native optional-iteration witness for any supplied step. -/
def oneStep {α : Type*} (f : α → Option α) (a : α) (b : Option α) (h : f a = b) :
    StateTransition.EvalsTo f a b where
  steps := 1
  evals_in_steps := by
    rw [Function.iterate_one]
    exact h

/-- The local count is justified by moveRun/writeRun; it will be summed
only over commands selected by the actual native finite run. -/
def commandCost {Γ Q : Type*} : Option (Q × TM0.Stmt Γ) → ℕ
  | some (_, .move _) => 1
  | some (_, .write _) => 2
  | none => 0

theorem commandCost_le_two {Γ Q : Type*} (a : Option (Q × TM0.Stmt Γ)) : commandCost a ≤ 2 := by
  cases a with
  | none => exact Nat.zero_le 2
  | some a =>
    rcases a with ⟨q, s⟩
    cases s with
    | move d => exact Nat.le_succ 1
    | write b => exact Nat.le_refl 2

section ExactSimulation

variable {Γ Q : Type*} [Inhabited Γ] [Inhabited Q] [DecidableEq Γ]

def moveRun (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (q q' : Q) (T : Tape Γ) (d : Dir) (h : M q T.head = some (q', .move d)) :
    StateTransition.EvalsTo (step (adapter M trueLetter)) (normalCfg ⟨q, T⟩)
      (some (normalCfg ⟨q', T.move d⟩)) :=
  oneStep _ _ _ (move_step M trueLetter q q' T d h)

theorem moveRun_steps (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (q q' : Q) (T : Tape Γ) (d : Dir) (h : M q T.head = some (q', .move d)) :
    (moveRun M trueLetter q q' T d h).steps = 1 := rfl

def writeRun (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (q q' : Q) (T : Tape Γ) (a : Γ) (h : M q T.head = some (q', .write a)) :
    StateTransition.EvalsTo (step (adapter M trueLetter)) (normalCfg ⟨q, T⟩)
      (some (normalCfg ⟨q', T.write a⟩)) :=
  StateTransition.EvalsTo.trans (step (adapter M trueLetter)) _
    ⟨.returning q', (T.write a).move .right⟩ _
    (oneStep _ _ _ (write_first_step M trueLetter q q' T a h))
    (oneStep _ _ _ (write_second_step M trueLetter q' T a))

theorem writeRun_steps (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (q q' : Q) (T : Tape Γ) (a : Γ) (h : M q T.head = some (q', .write a)) :
    (writeRun M trueLetter q q' T a h).steps = 2 := rfl

/-- A successful actual native step has a complete normal-boundary witness
with precisely the applicable one- or two-action count. -/
theorem native_step_exact (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (c finish : TM0.Cfg Γ Q) (hstep : TM0.step M c = some finish) :
    ∃ run : StateTransition.EvalsTo (step (adapter M trueLetter))
        (normalCfg c) (some (normalCfg finish)),
      run.steps = commandCost (M c.q c.Tape.head) := by
  rcases c with ⟨q, T⟩
  cases hcmd : M q T.head with
  | none =>
    have hs : TM0.step M ⟨q, T⟩ = none := by
      simp only [TM0.step, hcmd, Option.map_none]
    rw [hs] at hstep
    cases hstep
  | some a =>
    rcases a with ⟨q', s⟩
    cases s with
    | move d =>
      have hs : TM0.step M ⟨q, T⟩ = some ⟨q', T.move d⟩ := by
        simp only [TM0.step, hcmd, Option.map_some]
      have heq : (⟨q', T.move d⟩ : TM0.Cfg Γ Q) = finish :=
        Option.some.inj (hs.symm.trans hstep)
      subst finish
      exact ⟨moveRun M trueLetter q q' T d hcmd, rfl⟩
    | write a =>
      have hs : TM0.step M ⟨q, T⟩ = some ⟨q', T.write a⟩ := by
        simp only [TM0.step, hcmd, Option.map_some]
      have heq : (⟨q', T.write a⟩ : TM0.Cfg Γ Q) = finish :=
        Option.some.inj (hs.symm.trans hstep)
      subst finish
      exact ⟨writeRun M trueLetter q q' T a hcmd, rfl⟩

/-- Literal native optional prefixes, before any combined-action translation. -/
def nativePrefix (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q) (n : ℕ) :
    Option (TM0.Cfg Γ Q) := (_root_.flip Bind.bind (TM0.step M))^[n] (some start)

omit [DecidableEq Γ] in
theorem nativePrefix_succ (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q) (n : ℕ) :
    nativePrefix M start (n + 1) = Option.bind (nativePrefix M start n) (TM0.step M) :=
  Function.iterate_succ_apply' (_root_.flip Bind.bind (TM0.step M)) n (some start)

def observedNativeCommand (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q) (n : ℕ) :
    Option (Q × TM0.Stmt Γ) :=
  Option.bind (nativePrefix M start n) (fun c => M c.q c.Tape.head)

omit [DecidableEq Γ] in
theorem observedNativeCommand_of_live (M : TM0.Machine Γ Q)
    (start c : TM0.Cfg Γ Q) (n : ℕ) (h : nativePrefix M start n = some c) :
    observedNativeCommand M start n = M c.q c.Tape.head := by
  simp only [observedNativeCommand, h, Option.bind_some]

/-- Exact sum of emitted counts along the actual selected native commands.
The theorem below connects this sum to the actual combined iterate. -/
def simulationTime (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q) : ℕ → ℕ
  | 0 => 0
  | n + 1 => commandCost (observedNativeCommand M start n) + simulationTime M start n

omit [DecidableEq Γ] in
theorem simulationTime_le (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q) (n : ℕ) :
    simulationTime M start n ≤ 2 * n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have h := commandCost_le_two (observedNativeCommand M start n)
    rw [simulationTime]
    omega

/-- Lift an actual native finite run to the same complete configuration in
normal control. The exact count is proved, including the zero-step case. -/
theorem finite_run_exact (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (start finish : TM0.Cfg Γ Q) (n : ℕ)
    (hrun : nativePrefix M start n = some finish) :
    ∃ run : StateTransition.EvalsTo (step (adapter M trueLetter))
        (normalCfg start) (some (normalCfg finish)),
      run.steps = simulationTime M start n := by
  revert hrun
  induction n generalizing finish with
  | zero =>
    intro hrun
    have heq : start = finish := Option.some.inj hrun
    subst finish
    exact ⟨StateTransition.EvalsTo.refl _ _, rfl⟩
  | succ n ih =>
    intro hrun
    rw [nativePrefix_succ] at hrun
    cases hmid : nativePrefix M start n with
    | none =>
      rw [hmid] at hrun
      cases hrun
    | some mid =>
      rw [hmid] at hrun
      change TM0.step M mid = some finish at hrun
      obtain ⟨before, hbefore⟩ := ih mid hmid
      obtain ⟨after, hafter⟩ := native_step_exact M trueLetter mid finish hrun
      let combined := StateTransition.EvalsTo.trans (step (adapter M trueLetter))
        (normalCfg start) (normalCfg mid) (some (normalCfg finish)) before after
      refine ⟨combined, ?_⟩
      change after.steps + before.steps = simulationTime M start (n + 1)
      rw [simulationTime, observedNativeCommand_of_live M start mid n hmid,
        hbefore, hafter]

/-- Consume the supplied actual bounded native witness; no timing relation or
desired target witness is assumed. The returned run retains the full endpoint. -/
theorem lift_bounded_run (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (start finish : TM0.Cfg Γ Q) (B : ℕ)
    (source : StateTransition.EvalsToInTime (TM0.step M) start (some finish) B) :
    ∃ target : StateTransition.EvalsToInTime (step (adapter M trueLetter))
        (normalCfg start) (some (normalCfg finish)) (2 * B),
      target.steps = simulationTime M start source.steps ∧ target.steps ≤ 2 * source.steps := by
  obtain ⟨run, hrun⟩ := finite_run_exact M trueLetter start finish source.steps source.evals_in_steps
  have hcount : run.steps ≤ 2 * source.steps := by
    rw [hrun]
    exact simulationTime_le M start source.steps
  refine ⟨{ toEvalsTo := run, steps_le_m := ?_ }, hrun, hcount⟩
  exact le_trans hcount (Nat.mul_le_mul_left 2 source.steps_le_m)

end ExactSimulation

def terminalControl {Q : Type*} : Bool → Control Q
  | false => .reject
  | true => .accept

/-- Full tape after the charged final decision: the original head symbol was
printed unchanged, then the physical head moved right. -/
def decidedCfg {Γ Q : Type*} [Inhabited Γ] (answer : Bool) (T : Tape Γ) :
    Cfg Γ (Control Q) := ⟨terminalControl answer, T.move .right⟩

section Decision

variable {Γ Q : Type*} [Inhabited Γ] [Inhabited Q] [DecidableEq Γ]

omit [DecidableEq Γ] in
theorem native_command_none_of_stopped (M : TM0.Machine Γ Q)
    (finish : TM0.Cfg Γ Q) (stopped : TM0.step M finish = none) :
    M finish.q finish.Tape.head = none := by
  rcases finish with ⟨q, T⟩
  cases hcmd : M q T.head with
  | none => rfl
  | some a => simp only [TM0.step, hcmd, Option.map_some, Option.some_ne_none] at stopped

/-- Proved Boolean output is consumed here, after simulation. No blank or
other arbitrary stopped letter is silently declared a valid Boolean answer. -/
theorem decision_step (M : TM0.Machine Γ Q) (bit : Bool ↪ Γ)
    (finish : TM0.Cfg Γ Q) (answer : Bool)
    (stopped : TM0.step M finish = none) (output : finish.Tape.head = bit answer) :
    step (adapter M (bit true)) (normalCfg finish) = some (decidedCfg answer finish.Tape) := by
  have hcmd := native_command_none_of_stopped M finish stopped
  rcases finish with ⟨q, T⟩
  change M q T.head = none at hcmd
  change T.head = bit answer at output
  simp only [step, normalCfg, adapter, normalAction, hcmd, Option.map_some, Tape.write_self]
  cases answer with
  | false =>
    have hne : bit false ≠ bit true := by
      intro h
      have impossible : false = true := bit.injective h
      cases impossible
    change some (⟨if T.head = bit true then .accept else .reject, T.move .right⟩ :
      Cfg Γ (Control Q)) = some ⟨.reject, T.move .right⟩
    rw [output, ite_eq_right hne]
  | true =>
    change some (⟨if T.head = bit true then .accept else .reject, T.move .right⟩ :
      Cfg Γ (Control Q)) = some ⟨.accept, T.move .right⟩
    rw [output, ite_eq_left rfl]

def decisionRun (M : TM0.Machine Γ Q) (bit : Bool ↪ Γ)
    (finish : TM0.Cfg Γ Q) (answer : Bool)
    (stopped : TM0.step M finish = none) (output : finish.Tape.head = bit answer) :
    StateTransition.EvalsTo (step (adapter M (bit true))) (normalCfg finish)
      (some (decidedCfg answer finish.Tape)) :=
  oneStep _ _ _ (decision_step M bit finish answer stopped output)

theorem decisionRun_steps (M : TM0.Machine Γ Q) (bit : Bool ↪ Γ)
    (finish : TM0.Cfg Γ Q) (answer : Bool)
    (stopped : TM0.step M finish = none) (output : finish.Tape.head = bit answer) :
    (decisionRun M bit finish answer stopped output).steps = 1 := rfl

theorem decidedCfg_stopped (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (answer : Bool) (T : Tape Γ) : step (adapter M trueLetter) (decidedCfg answer T) = none := by
  cases answer <;> rfl

/-- Actual paid simulation and decision. The endpoint is the correct terminal
control with the complete moved source tape. At native count0 this count is1. -/
theorem decide_of_native_run (M : TM0.Machine Γ Q) (bit : Bool ↪ Γ)
    (start finish : TM0.Cfg Γ Q) (answer : Bool) (B : ℕ)
    (source : StateTransition.EvalsToInTime (TM0.step M) start (some finish) B)
    (stopped : TM0.step M finish = none) (output : finish.Tape.head = bit answer) :
    ∃ target : StateTransition.EvalsToInTime (step (adapter M (bit true)))
        (normalCfg start) (some (decidedCfg answer finish.Tape)) (2 * B + 1),
      target.steps = simulationTime M start source.steps + 1 ∧
      target.steps ≤ 2 * source.steps + 1 ∧
      step (adapter M (bit true)) (decidedCfg answer finish.Tape) = none := by
  obtain ⟨before, hbefore, hbound⟩ := lift_bounded_run M (bit true) start finish B source
  let after := decisionRun M bit finish answer stopped output
  let run := StateTransition.EvalsTo.trans (step (adapter M (bit true)))
    (normalCfg start) (normalCfg finish) (some (decidedCfg answer finish.Tape))
    before.toEvalsTo after
  have hsteps : run.steps = simulationTime M start source.steps + 1 := by
    change 1 + before.steps = simulationTime M start source.steps + 1
    rw [hbefore, Nat.add_comm]
  have hcount : run.steps ≤ 2 * source.steps + 1 := by
    change 1 + before.steps ≤ 2 * source.steps + 1
    omega
  refine ⟨{ toEvalsTo := run, steps_le_m := ?_ }, hsteps, hcount,
    decidedCfg_stopped M (bit true) answer finish.Tape⟩
  exact le_trans hcount (Nat.add_le_add_right (Nat.mul_le_mul_left 2 source.steps_le_m) 1)

/-- The optional-step observation after a terminal conventional cfg is
separate from the published accepting/rejecting computation. -/
def terminalOuterNone (M : TM0.Machine Γ Q) (trueLetter : Γ) (answer : Bool) (T : Tape Γ) :
    StateTransition.EvalsTo (step (adapter M trueLetter)) (decidedCfg answer T) none :=
  oneStep _ _ _ (decidedCfg_stopped M trueLetter answer T)

theorem terminalOuterNone_steps (M : TM0.Machine Γ Q) (trueLetter : Γ)
    (answer : Bool) (T : Tape Γ) : (terminalOuterNone M trueLetter answer T).steps = 1 := rfl

end Decision

end Resources.TuringSimulation.PrintMove

namespace Resources.TuringSimulation.PrintMove.Trace

open Function Turing

def directionOffset : Dir → ℤ
  | .left => -1
  | .right => 1

def actionOffset {Γ Q : Type*} : Option (Action Γ Q) → ℤ
  | none => 0
  | some a => directionOffset a.direction

theorem actionOffset_bounds {Γ Q : Type*} (a : Option (Action Γ Q)) :
    -1 ≤ actionOffset a ∧ actionOffset a ≤ 1 := by
  cases a with
  | none =>
    change (-1 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ 1
    decide
  | some a =>
    rcases a with ⟨q, b, d⟩
    cases d with
    | left =>
      change (-1 : ℤ) ≤ -1 ∧ (-1 : ℤ) ≤ 1
      decide
    | right =>
      change (-1 : ℤ) ≤ 1 ∧ (1 : ℤ) ≤ 1
      decide

section Trace

variable {Γ Q : Type*} [Inhabited Γ]

def cfgAt (M : Machine Γ Q) (start : Cfg Γ Q) (n : ℕ) : Option (Cfg Γ Q) :=
  (_root_.flip Bind.bind (step M))^[n] (some start)

theorem cfgAt_succ (M : Machine Γ Q) (start : Cfg Γ Q) (n : ℕ) :
    cfgAt M start (n + 1) = Option.bind (cfgAt M start n) (step M) :=
  Function.iterate_succ_apply' (_root_.flip Bind.bind (step M)) n (some start)

def actionAt (M : Machine Γ Q) (start : Cfg Γ Q) (n : ℕ) : Option (Action Γ Q) :=
  Option.bind (cfgAt M start n) (fun c => M c.q c.Tape.head)

/-- Displacement of the actual combined action at every real prefix. -/
def headPosition (M : Machine Γ Q) (start : Cfg Γ Q) (origin : ℤ) : ℕ → ℤ
  | 0 => origin
  | n + 1 => headPosition M start origin n + actionOffset (actionAt M start n)

theorem headPosition_succ (M : Machine Γ Q) (start : Cfg Γ Q) (origin : ℤ) (n : ℕ) :
    headPosition M start origin (n + 1) =
      headPosition M start origin n + actionOffset (actionAt M start n) := rfl

theorem headPosition_step_bounds (M : Machine Γ Q) (start : Cfg Γ Q)
    (origin : ℤ) (n : ℕ) :
    headPosition M start origin n - 1 ≤ headPosition M start origin (n + 1) ∧
      headPosition M start origin (n + 1) ≤ headPosition M start origin n + 1 := by
  have h := actionOffset_bounds (actionAt M start n)
  rw [headPosition_succ]
  omega

/-- Only live native optional prefixes supply visits; terminal outer none is
not treated as an additional physical head location. -/
def visitedCells (M : Machine Γ Q) (start : Cfg Γ Q) (origin : ℤ) (U : ℕ) : Finset ℤ :=
  ((Finset.range (U + 1)).filter (fun i => (cfgAt M start i).isSome = true)).image
    (headPosition M start origin)

theorem mem_visitedCells (M : Machine Γ Q) (start : Cfg Γ Q)
    (origin : ℤ) (U : ℕ) (x : ℤ) :
    x ∈ visitedCells M start origin U ↔
      ∃ i, i ≤ U ∧ (cfgAt M start i).isSome = true ∧ headPosition M start origin i = x := by
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, hpos⟩
    rcases Finset.mem_filter.mp hi with ⟨hrange, hlive⟩
    exact ⟨i, Nat.le_of_lt_succ (Finset.mem_range.mp hrange), hlive, hpos⟩
  · rintro ⟨i, hi, hlive, hpos⟩
    exact Finset.mem_image.mpr ⟨i,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi), hlive⟩, hpos⟩

theorem visitedCells_card_le (M : Machine Γ Q) (start : Cfg Γ Q) (origin : ℤ) (U : ℕ) :
    (visitedCells M start origin U).card ≤ U + 1 := by
  calc
    _ ≤ ((Finset.range (U + 1)).filter (fun i => (cfgAt M start i).isSome = true)).card :=
      Finset.card_image_le
    _ ≤ (Finset.range (U + 1)).card := Finset.card_filter_le _ _
    _ = U + 1 := Finset.card_range _

def inputCells (origin : ℤ) (N : ℕ) : Finset ℤ :=
  (Finset.range N).image (fun i : ℕ => origin + (i : ℤ))

def leftEdge (M : Machine Γ Q) (start : Cfg Γ Q) (origin : ℤ) : ℕ → ℤ
  | 0 => origin
  | n + 1 => min (leftEdge M start origin n) (headPosition M start origin (n + 1))

def rightEdge (M : Machine Γ Q) (start : Cfg Γ Q) (origin : ℤ) (N : ℕ) : ℕ → ℤ
  | 0 => origin + ((N - 1 : ℕ) : ℤ)
  | n + 1 => max (rightEdge M start origin N n) (headPosition M start origin (n + 1))

def visitedInterval (M : Machine Γ Q) (start : Cfg Γ Q) (origin : ℤ) (N U : ℕ) : Finset ℤ :=
  Finset.Icc (leftEdge M start origin U) (rightEdge M start origin N U)

theorem headPosition_between_edges (M : Machine Γ Q) (start : Cfg Γ Q)
    (origin : ℤ) (N n : ℕ) :
    leftEdge M start origin n ≤ headPosition M start origin n ∧
      headPosition M start origin n ≤ rightEdge M start origin N n := by
  cases n with
  | zero =>
    change origin ≤ origin ∧ origin ≤ origin + ((N - 1 : ℕ) : ℤ)
    omega
  | succ n => exact ⟨min_le_right _ _, le_max_right _ _⟩

theorem leftEdge_antitone (M : Machine Γ Q) (start : Cfg Γ Q) (origin : ℤ) :
    Antitone (leftEdge M start origin) :=
  antitone_nat_of_succ_le (fun _ => min_le_left _ _)

theorem rightEdge_monotone (M : Machine Γ Q) (start : Cfg Γ Q) (origin : ℤ) (N : ℕ) :
    Monotone (rightEdge M start origin N) :=
  monotone_nat_of_le_succ (fun _ => le_max_left _ _)

theorem visitedCells_subset_interval (M : Machine Γ Q) (start : Cfg Γ Q)
    (origin : ℤ) (N U : ℕ) :
    visitedCells M start origin U ⊆ visitedInterval M start origin N U := by
  intro x hx
  rcases (mem_visitedCells M start origin U x).mp hx with ⟨i, hi, _, hpos⟩
  rw [← hpos]
  have h := headPosition_between_edges M start origin N i
  exact Finset.mem_Icc.mpr
    ⟨le_trans (leftEdge_antitone M start origin hi) h.1,
      le_trans h.2 (rightEdge_monotone M start origin N hi)⟩

theorem inputCells_subset_interval (M : Machine Γ Q) (start : Cfg Γ Q)
    (origin : ℤ) (N U : ℕ) : inputCells origin N ⊆ visitedInterval M start origin N U := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, hi, hpos⟩
  have hilt := Finset.mem_range.mp hi
  have hl := leftEdge_antitone M start origin (Nat.zero_le U)
  have hr := rightEdge_monotone M start origin N (Nat.zero_le U)
  change leftEdge M start origin U ≤ origin at hl
  change origin + ((N - 1 : ℕ) : ℤ) ≤ rightEdge M start origin N U at hr
  apply Finset.mem_Icc.mpr
  omega

theorem interval_width_le (M : Machine Γ Q) (start : Cfg Γ Q)
    (origin : ℤ) (N U : ℕ) :
    rightEdge M start origin N U + 1 - leftEdge M start origin U ≤
      ((max N 1 + U : ℕ) : ℤ) := by
  induction U with
  | zero =>
    change origin + ((N - 1 : ℕ) : ℤ) + 1 - origin ≤ ((max N 1 + 0 : ℕ) : ℤ)
    omega
  | succ U ih =>
    have hold := headPosition_between_edges M start origin N U
    have hmove := headPosition_step_bounds M start origin U
    change max (rightEdge M start origin N U) (headPosition M start origin (U + 1)) +
      1 - min (leftEdge M start origin U) (headPosition M start origin (U + 1)) ≤ _
    omega

theorem visitedInterval_card_le (M : Machine Γ Q) (start : Cfg Γ Q)
    (origin : ℤ) (N U : ℕ) : (visitedInterval M start origin N U).card ≤ max N 1 + U := by
  rw [visitedInterval, Int.card_Icc]
  exact Int.toNat_le.mpr (interval_width_le M start origin N U)

theorem actionAt_eq_none_of_next_none (M : Machine Γ Q) (start : Cfg Γ Q)
    (n : ℕ) (hnext : cfgAt M start (n + 1) = none) : actionAt M start n = none := by
  cases hprev : cfgAt M start n with
  | none => simp only [actionAt, hprev, Option.bind_none]
  | some c =>
    unfold actionAt
    rw [hprev]
    change M c.q c.Tape.head = none
    cases hcmd : M c.q c.Tape.head with
    | none => rfl
    | some a =>
      rw [cfgAt_succ, hprev] at hnext
      change step M c = none at hnext
      simp only [step, hcmd, Option.map_some, Option.some_ne_none] at hnext

theorem terminal_prefix_adds_no_cells (M : Machine Γ Q) (start : Cfg Γ Q)
    (origin : ℤ) (N n : ℕ) (hnext : cfgAt M start (n + 1) = none) :
    visitedCells M start origin (n + 1) = visitedCells M start origin n ∧
      visitedInterval M start origin N (n + 1) = visitedInterval M start origin N n := by
  constructor
  · apply Finset.Subset.antisymm
    · intro x hx
      rcases (mem_visitedCells M start origin (n + 1) x).mp hx with ⟨i, hi, hlive, hpos⟩
      have hne : i ≠ n + 1 := by
        intro heq
        subst i
        rw [hnext] at hlive
        cases hlive
      exact (mem_visitedCells M start origin n x).mpr ⟨i, by omega, hlive, hpos⟩
    · intro x hx
      rcases (mem_visitedCells M start origin n x).mp hx with ⟨i, hi, hlive, hpos⟩
      exact (mem_visitedCells M start origin (n + 1) x).mpr
        ⟨i, Nat.le_trans hi (Nat.le_succ n), hlive, hpos⟩
  · have hp : headPosition M start origin (n + 1) = headPosition M start origin n := by
      rw [headPosition_succ, actionAt_eq_none_of_next_none M start n hnext]
      simp only [actionOffset, add_zero]
    have hb := headPosition_between_edges M start origin N n
    change Finset.Icc
      (min (leftEdge M start origin n) (headPosition M start origin (n + 1)))
      (max (rightEdge M start origin N n) (headPosition M start origin (n + 1))) =
        Finset.Icc (leftEdge M start origin n) (rightEdge M start origin N n)
    rw [hp, min_eq_left hb.1, max_eq_left hb.2]

/-- Every actual prefix of the supplied combined witness is observed. The
transient return state and the final rightward decision are not skipped. -/
theorem interval_le_of_run (M : Machine Γ Q) (start : Cfg Γ Q)
    (endpoint : Option (Cfg Γ Q)) (B : ℕ)
    (run : StateTransition.EvalsToInTime (step M) start endpoint B) (origin : ℤ) (N : ℕ) :
    cfgAt M start run.steps = endpoint ∧
      ∀ i ≤ run.steps, (visitedInterval M start origin N i).card ≤ max N 1 + B := by
  refine ⟨run.evals_in_steps, ?_⟩
  intro i hi
  exact le_trans (visitedInterval_card_le M start origin N i)
    (Nat.add_le_add_left (le_trans hi run.steps_le_m) _)

/-- Actual combined printing/movement respects global cell coordinates. This
also identifies exactly the one global cell that a combined write may alter. -/
theorem printMove_nth_at_other_global_coordinate (T : Tape Γ) (a : Γ)
    (d : Dir) (x p : ℤ) (hne : x ≠ p) :
    ((T.write a).move d).nth (x - (p + directionOffset d)) = T.nth (x - p) := by
  have hframe : ((T.write a).move d).nth (x - (p + directionOffset d)) =
      (T.write a).nth (x - p) := by
    cases d with
    | left =>
      rw [directionOffset, Tape.move_left_nth]
      congr 1
      omega
    | right =>
      rw [directionOffset, Tape.move_right_nth]
      congr 1
      omega
  rw [hframe, Tape.write_nth, ite_eq_right (sub_ne_zero.mpr hne)]

end Trace

section PaidRun

variable {Γ Q : Type*} [Inhabited Γ] [Inhabited Q] [DecidableEq Γ]

/-- The actual paid decision witness also supplies a conservative physical
visited interval bound. N is declared input length; arbitrary starting support
is not silently asserted to fit that declaration. -/
theorem paid_run_interval (M : TM0.Machine Γ Q) (bit : Bool ↪ Γ)
    (start finish : TM0.Cfg Γ Q) (answer : Bool) (B N : ℕ) (origin : ℤ)
    (source : StateTransition.EvalsToInTime (TM0.step M) start (some finish) B)
    (stopped : TM0.step M finish = none) (output : finish.Tape.head = bit answer) :
    ∃ target : StateTransition.EvalsToInTime (step (adapter M (bit true)))
        (normalCfg start) (some (decidedCfg answer finish.Tape)) (2 * B + 1),
      target.steps = simulationTime M start source.steps + 1 ∧
      ∀ i ≤ target.steps,
        (visitedInterval (adapter M (bit true)) (normalCfg start) origin N i).card ≤
          max N 1 + (2 * B + 1) := by
  obtain ⟨target, hcount, _hbound, _halt⟩ :=
    decide_of_native_run M bit start finish answer B source stopped output
  exact ⟨target, hcount, (interval_le_of_run (adapter M (bit true)) (normalCfg start)
    (some (decidedCfg answer finish.Tape)) (2 * B + 1) target origin N).2⟩

end PaidRun

end Resources.TuringSimulation.PrintMove.Trace
