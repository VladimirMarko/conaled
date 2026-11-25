import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Exact reflection of native primitive tape machines

Reflect the complete physical tape and native move directions while preserving supplied defaults, live and outer-none endpoints, and literal iteration counts.
-/

set_option autoImplicit false
set_option warningAsError true


namespace Resources.TuringSimulation.TapeReflection

open Function Turing

def direction : Dir → Dir
  | .left => .right
  | .right => .left

theorem direction_involutive (d : Dir) : direction (direction d) = d := by
  cases d <;> rfl

def tape {Γ : Type*} [Inhabited Γ] (T : Tape Γ) : Tape Γ :=
  ⟨T.head, T.right, T.left⟩

theorem tape_involutive {Γ : Type*} [Inhabited Γ] (T : Tape Γ) :
    tape (tape T) = T := by
  cases T
  rfl

theorem tape_head {Γ : Type*} [Inhabited Γ] (T : Tape Γ) :
    (tape T).head = T.head := rfl

theorem tape_write {Γ : Type*} [Inhabited Γ] (T : Tape Γ) (a : Γ) :
    tape (T.write a) = (tape T).write a := rfl

theorem tape_move {Γ : Type*} [Inhabited Γ] (T : Tape Γ) (d : Dir) :
    tape (T.move d) = (tape T).move (direction d) := by
  cases T
  cases d <;> rfl

def statement {Γ : Type*} : TM0.Stmt Γ → TM0.Stmt Γ
  | .move d => .move (direction d)
  | .write a => .write a

theorem statement_involutive {Γ : Type*} (s : TM0.Stmt Γ) :
    statement (statement s) = s := by
  cases s with
  | move d => cases d <;> rfl
  | write _ => rfl

def configuration {Γ Q : Type*} [Inhabited Γ] (c : TM0.Cfg Γ Q) : TM0.Cfg Γ Q :=
  ⟨c.q, tape c.Tape⟩

theorem configuration_involutive {Γ Q : Type*} [Inhabited Γ]
    (c : TM0.Cfg Γ Q) : configuration (configuration c) = c := by
  cases c with
  | mk q T =>
    change TM0.Cfg.mk q (tape (tape T)) = TM0.Cfg.mk q T
    rw [tape_involutive]

def machine {Γ Q : Type*} [Inhabited Q] (M : TM0.Machine Γ Q) :
    TM0.Machine Γ Q :=
  fun q a => (M q a).map (fun result => (result.1, statement result.2))

/-- A reflected native step retains the same control and complete reflected
tape. This statement includes the halt transition returning outer none. -/
theorem step {Γ Q : Type*} [Inhabited Γ] [Inhabited Q]
    (M : TM0.Machine Γ Q) (c : TM0.Cfg Γ Q) :
    TM0.step (machine M) (configuration c) =
      (TM0.step M c).map configuration := by
  cases c with
  | mk q T =>
    cases T with
    | mk a L R =>
      cases h : M q a with
      | none =>
        simp only [TM0.step, machine, configuration, tape, h, Option.map_none]
      | some result =>
        rcases result with ⟨q', act⟩
        cases act with
        | write b =>
          simp only [TM0.step, machine, configuration, tape, h,
            Option.map_some, statement, Tape.write]
        | move d =>
          cases d <;>
            simp only [TM0.step, machine, configuration, tape, h,
              Option.map_some, statement, direction, Tape.move]

theorem bind_step {Γ Q : Type*} [Inhabited Γ] [Inhabited Q]
    (M : TM0.Machine Γ Q) (x : Option (TM0.Cfg Γ Q)) :
    (flip Bind.bind (TM0.step M) x).map configuration =
      flip Bind.bind (TM0.step (machine M)) (x.map configuration) := by
  cases x with
  | none => rfl
  | some c => exact (step M c).symm

/-- Exact optional iteration, for every input option and every count. This
does not assume the count is positive or that an endpoint is live. -/
theorem iterate_option {Γ Q : Type*} [Inhabited Γ] [Inhabited Q]
    (M : TM0.Machine Γ Q) (n : ℕ) (x : Option (TM0.Cfg Γ Q)) :
    ((flip Bind.bind (TM0.step M))^[n] x).map configuration =
      (flip Bind.bind (TM0.step (machine M)))^[n] (x.map configuration) := by
  induction n generalizing x with
  | zero => rfl
  | succ n IH =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact (IH (flip Bind.bind (TM0.step M) x)).trans
      (congrArg ((flip Bind.bind (TM0.step (machine M)))^[n]) (bind_step M x))

/-- Reflection uses the existing native witness and preserves its count,
bound, control and full optional endpoint. -/
def evalsToInTime {Γ Q : Type*} [Inhabited Γ] [Inhabited Q]
    (M : TM0.Machine Γ Q) (a : TM0.Cfg Γ Q)
    (b : Option (TM0.Cfg Γ Q)) (B : ℕ)
    (h : StateTransition.EvalsToInTime (TM0.step M) a b B) :
    StateTransition.EvalsToInTime (TM0.step (machine M))
      (configuration a) (b.map configuration) B where
  toEvalsTo := {
    steps := h.steps
    evals_in_steps := by
      have eq := iterate_option M h.steps (some a)
      rw [h.evals_in_steps] at eq
      exact eq.symm }
  steps_le_m := h.steps_le_m

theorem evalsToInTime_steps {Γ Q : Type*} [Inhabited Γ] [Inhabited Q]
    (M : TM0.Machine Γ Q) (a : TM0.Cfg Γ Q)
    (b : Option (TM0.Cfg Γ Q)) (B : ℕ)
    (h : StateTransition.EvalsToInTime (TM0.step M) a b B) :
    (evalsToInTime M a b B h).steps = h.steps := rfl

/-- The source default is literally unchanged; this is not a native-input
claim for a right-facing nonempty list. The input prelude supplies that separate
connection to the reflected encoded tape. -/
theorem configuration_default {Γ Q : Type*} [Inhabited Γ] [Inhabited Q]
    (T : Tape Γ) :
    (configuration (⟨default, T⟩ : TM0.Cfg Γ Q)).q = (default : Q) := rfl

end Resources.TuringSimulation.TapeReflection
