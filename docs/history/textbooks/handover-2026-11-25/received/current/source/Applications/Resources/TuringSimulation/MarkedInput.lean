import Applications.Resources.TuringSimulation.TapeReflection
import Applications.Resources.TuringSimulation.SingletonOutput
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Paid ordinary input and output for the reflected native simulator

A fixed injective nonblank letter map starts the actual prelude. Full native runs retain their counts through reflection, then pay one output write and a separate next transition to outer none.
-/

set_option autoImplicit false
set_option warningAsError true


namespace Resources.TuringSimulation.MarkedInput

open Function Turing
open Turing.TM2to1
open Resources.TuringSimulation

variable {K : Type*} {Γ : K → Type*} [DecidableEq K]

/-- A designated input letter; it is never the working blank. -/
def symbol (k : K) (a : Γ k) : Γ' K Γ :=
  (false, Function.update (fun _ => none) k (some a))

theorem symbol_selected (k : K) (a : Γ k) : (symbol k a).2 k = some a := by
  exact Function.update_self k (some a) (fun j : K => (none : Option (Γ j)))

theorem symbol_injective (k : K) : Function.Injective (symbol (Γ := Γ) k) := by
  intro a b h
  have observed := congrArg (fun c : Γ' K Γ => c.2 k) h
  rw [symbol_selected, symbol_selected] at observed
  exact Option.some.inj observed

theorem symbol_ne_blank (k : K) (a : Γ k) : symbol k a ≠ (default : Γ' K Γ) := by
  intro h
  have observed := congrArg (fun c : Γ' K Γ => c.2 k) h
  rw [symbol_selected] at observed
  change some a = none at observed
  cases observed

def input (k : K) (raw : List (Γ k)) : List (Γ' K Γ) := raw.map (symbol k)

theorem input_length (k : K) (raw : List (Γ k)) : (input k raw).length = raw.length := by
  simp only [input, List.length_map]

/-- A pointed alphabet embedding exposes the distinction between none and a
present false symbol, independently of any whole-word encoding. -/
def inputAlphabet (k : K) : PointedMap (Option (Γ k)) (Γ' K Γ) :=
  ⟨fun a => match a with | none => default | some a => symbol k a, rfl⟩

def readInput (k : K) : PointedMap (Γ' K Γ) (Option (Γ k)) :=
  ⟨fun a => a.2 k, rfl⟩

theorem read_inputAlphabet (k : K) (a : Option (Γ k)) :
    readInput k (inputAlphabet k a) = a := by
  cases a with
  | none => rfl
  | some a => exact symbol_selected k a

/-- The ordinary output observation retains present false as some false.
Mapping directly to Bool with false as blank would lose this distinction. -/
theorem output_readback (k : K) (a : Γ k) :
    (ListBlank.mk [symbol k a]).map (readInput k) = ListBlank.mk [some a] := by
  rw [ListBlank.map_mk]
  change ListBlank.mk [(symbol k a).2 k] = ListBlank.mk [some a]
  rw [symbol_selected]

inductive Control (Q : Type*)
  | start
  | scan
  | mark
  | run (q : Q)
  | done
  deriving Fintype

instance {Q : Type*} : Inhabited (Control Q) := ⟨.start⟩

variable {Q : Type*} [Inhabited Q]

/-- An actual native primitive machine. The source default is inherited from
the supplied Q instance; the wrapper's native default is start. The emit
function is fixed with the machine and is executed by one native write.
Control and alphabet finiteness are independent of the input word. -/
def machine (k : K) (M : TM0.Machine (Γ' K Γ) Q) (emit : Γ' K Γ → Γ' K Γ) :
    TM0.Machine (Γ' K Γ) (Control Q)
  | .start, a =>
      match a.2 k with
      | none => some (.run default, .write (true, a.2))
      | some _ => some (.scan, .move .right)
  | .scan, a =>
      match a.2 k with
      | none => some (.mark, .move .left)
      | some _ => some (.scan, .move .right)
  | .mark, a => some (.run default, .write (true, a.2))
  | .run q, a =>
      match M q a with
      | none => some (.done, .write (emit a))
      | some (q', act) => some (.run q', TapeReflection.statement act)
  | .done, _ => none

/-- The physical left list is nearest first. This helper describes actual
native tapes during the scan, not a separate evaluator. -/
def scanTape (k : K) (left right : List (Γ k)) : Tape (Γ' K Γ) :=
  Tape.mk' (ListBlank.mk (input k left)) (ListBlank.mk (input k right))

def preludeSteps {α : Type*} : List α → ℕ
  | [] => 1
  | a :: raw => (a :: raw).length + 2

variable (k : K) (M : TM0.Machine (Γ' K Γ) Q) (emit : Γ' K Γ → Γ' K Γ)

theorem scan_symbol_step (a : Γ k) (left right : List (Γ k)) :
    TM0.step (machine k M emit) ⟨.scan, scanTape k left (a :: right)⟩ =
      some ⟨.scan, scanTape k (a :: left) right⟩ := by
  have instruction : machine k M emit .scan (symbol k a) =
      some (.scan, .move .right) := by
    change ((match Function.update (fun j : K => (none : Option (Γ j))) k (some a) k with
      | none => some (Control.mark, TM0.Stmt.move Dir.left)
      | some _ => some (Control.scan, TM0.Stmt.move Dir.right)) :
        Option (Control Q × TM0.Stmt (Γ' K Γ))) = _
    rw [Function.update_self]
  have moved : (scanTape k left (a :: right)).move Dir.right =
      scanTape k (a :: left) right := by
    simp only [scanTape, input, List.map_cons, Tape.move_right_mk',
      ListBlank.head_mk, List.headI_cons, ListBlank.cons_mk,
      ListBlank.tail_mk, List.tail_cons]
  simp only [TM0.step, scanTape, input, List.map_cons, Tape.mk'_head,
    ListBlank.head_mk, List.headI_cons]
  rw [instruction]
  change some (⟨Control.scan, (scanTape k left (a :: right)).move Dir.right⟩ :
    TM0.Cfg (Γ' K Γ) (Control Q)) = _
  rw [moved]
  rfl

theorem start_symbol_step (a : Γ k) (right : List (Γ k)) :
    TM0.step (machine k M emit) (TM0.init (input k (a :: right))) =
      some ⟨.scan, scanTape k [a] right⟩ := by
  have instruction : machine k M emit .start (symbol k a) =
      some (.scan, .move .right) := by
    change ((match Function.update (fun j : K => (none : Option (Γ j))) k (some a) k with
      | none => some (Control.run default,
          TM0.Stmt.write (true, Function.update
            (fun j : K => (none : Option (Γ j))) k (some a)))
      | some _ => some (Control.scan, TM0.Stmt.move Dir.right)) :
        Option (Control Q × TM0.Stmt (Γ' K Γ))) = _
    rw [Function.update_self]
  have transported := congrArg
    (fun action : Option (Control Q × TM0.Stmt (Γ' K Γ)) =>
      TM0.step (fun _ _ => action)
        (⟨Control.start, scanTape k [] (a :: right)⟩ : TM0.Cfg (Γ' K Γ) (Control Q)))
    instruction
  have start_default : (default : Control Q) = Control.start := rfl
  simpa only [TM0.init, TM0.step, scanTape, input, List.map_cons, List.map_nil,
    Tape.mk₁, Tape.mk₂, Tape.mk'_head, ListBlank.head_mk, List.headI_cons,
    Option.map_some, Tape.move_right_mk', ListBlank.cons_mk,
    ListBlank.tail_mk, List.tail_cons, start_default] using transported

theorem scan_empty_step (left : List (Γ k)) :
    TM0.step (machine k M emit) ⟨.scan, scanTape k left []⟩ =
      some ⟨.mark, (scanTape k left []).move .left⟩ := rfl

omit [DecidableEq K] in
theorem mark_step (T : Tape (Γ' K Γ)) :
    TM0.step (machine k M emit) ⟨.mark, T⟩ =
      some ⟨.run default, T.write (true, T.head.2)⟩ := rfl

omit [Inhabited Q] in
theorem blank_cons_empty {A : Type*} [Inhabited A] :
    (∅ : ListBlank A).cons default = ∅ :=
  ListBlank.cons_head_tail (∅ : ListBlank A)

omit [Inhabited Q] in
theorem marked_boundary_tape (a : Γ k) (left : List (Γ k)) :
    ((scanTape k (a :: left) []).move .left).write
        (true, ((scanTape k (a :: left) []).move .left).head.2) =
      TapeReflection.tape (Tape.mk₁ (trInit k (a :: left).reverse)) := by
  have endpoint := congrArg
    (fun raw : List (Γ k) =>
      TapeReflection.tape (Tape.mk₁ (Γ := Γ' K Γ)
        ((true, (input (Γ := Γ) k raw).headI.2) :: (input (Γ := Γ) k raw).tail)))
    (List.reverse_reverse (a :: left))
  have blankTail := congrArg
    (fun right : ListBlank (Γ' K Γ) =>
      Tape.mk (Γ := Γ' K Γ)
        (true, Function.update (fun j : K => (none : Option (Γ j))) k (some a))
        (ListBlank.mk (input (Γ := Γ) k left)) right)
    (blank_cons_empty (A := Γ' K Γ))
  exact blankTail.trans endpoint.symm

/-- The scan consumes the literal unread suffix. Its complete endpoint tape
contains the reverse order on the physical left because actual right moves
have pushed each encountered symbol onto Tape.left. -/
theorem scan_exact (right : List (Γ k)) (left : List (Γ k)) (nonempty : left ≠ []) :
    (flip Bind.bind (TM0.step (machine k M emit)))^[right.length + 2]
      (some ⟨.scan, scanTape k left right⟩) =
      some ⟨.run default,
        TapeReflection.tape (Tape.mk₁ (trInit k (left.reverse ++ right)))⟩ := by
  induction right generalizing left with
  | nil =>
    cases left with
    | nil => exact False.elim (nonempty rfl)
    | cons a left =>
      simp only [List.length_nil, List.append_nil, Nat.zero_add]
      rw [Function.iterate_succ_apply]
      change (flip Bind.bind (TM0.step (machine k M emit)))^[1]
        (TM0.step (machine k M emit) ⟨.scan, scanTape k (a :: left) []⟩) = _
      rw [scan_empty_step]
      change TM0.step (machine k M emit)
        ⟨.mark, (scanTape k (a :: left) []).move .left⟩ = _
      exact (mark_step k M emit ((scanTape k (a :: left) []).move .left)).trans
        (congrArg (fun T : Tape (Γ' K Γ) =>
          some (TM0.Cfg.mk (Control.run (default : Q)) T))
          (marked_boundary_tape k a left))
  | cons a right IH =>
    have count : (a :: right).length + 2 = (right.length + 2) + 1 := by
      change right.length + 1 + 2 = right.length + 2 + 1
      exact Nat.add_right_comm _ _ _
    rw [count, Function.iterate_succ_apply]
    change (flip Bind.bind (TM0.step (machine k M emit)))^[right.length + 2]
      (TM0.step (machine k M emit) ⟨.scan, scanTape k left (a :: right)⟩) = _
    rw [scan_symbol_step]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
      IH (a :: left) (by simp only [ne_eq, List.cons_ne_nil, not_false_eq_true])

/-- Actual ordinary native initialization reaches the same supplied source
default on the complete reflected encoded tape. Empty input costs one write;
positive length N costs N right moves, one left move and one marker write. -/
theorem prelude_exact (raw : List (Γ k)) :
    (flip Bind.bind (TM0.step (machine k M emit)))^[preludeSteps raw]
      (some (TM0.init (input k raw))) =
      some ⟨.run default, TapeReflection.tape (Tape.mk₁ (trInit k raw))⟩ := by
  cases raw with
  | nil => rfl
  | cons a raw =>
    have count : preludeSteps (a :: raw) = (raw.length + 2) + 1 := by
      change raw.length + 1 + 2 = raw.length + 2 + 1
      exact Nat.add_right_comm _ _ _
    rw [count, Function.iterate_succ_apply]
    change (flip Bind.bind (TM0.step (machine k M emit)))^[raw.length + 2]
      (TM0.step (machine k M emit) (TM0.init (input k (a :: raw)))) = _
    rw [start_symbol_step]
    simpa only [List.reverse_singleton, List.singleton_append] using
      scan_exact k M emit raw [a] (by simp only [ne_eq, List.cons_ne_nil, not_false_eq_true])

def preludeRun (raw : List (Γ k)) :
    StateTransition.EvalsTo (TM0.step (machine k M emit))
      (TM0.init (input k raw))
      (some ⟨.run default, TapeReflection.tape (Tape.mk₁ (trInit k raw))⟩) where
  steps := preludeSteps raw
  evals_in_steps := prelude_exact k M emit raw

theorem preludeRun_steps (raw : List (Γ k)) :
    (preludeRun k M emit raw).steps = preludeSteps raw := rfl

omit [DecidableEq K] in
/-- Once the whole tape is singleton, a native write changes that complete
tape to the ordinary output singleton. The source halt condition comes from
the actual related live source halt, not from a presumed answer. -/
theorem emit_singleton_step (q : Q) (a : Γ' K Γ) (stopped : M q a = none) :
    TM0.step (machine k M emit) ⟨.run q, Tape.mk₁ [a]⟩ =
      some ⟨.done, Tape.mk₁ [emit a]⟩ := by
  simp only [TM0.step, machine, Tape.mk₁, Tape.mk₂, Tape.mk'_head,
    ListBlank.head_mk, List.headI_cons, stopped, Option.map_some]
  rfl

omit [DecidableEq K] in
theorem done_step (T : Tape (Γ' K Γ)) :
    TM0.step (machine k M emit) ⟨.done, T⟩ = none := rfl

end Resources.TuringSimulation.MarkedInput

namespace Resources.TuringSimulation.MarkedInput

open Function Turing
open Turing.TM2to1

variable {K : Type*} {Γ : K → Type*} [DecidableEq K]
variable {Q : Type*} [Inhabited Q]

/-- The run phase retains the complete source configuration with its entire
tape reflected and its actual source control wrapped. -/
def runConfiguration (c : TM0.Cfg (Γ' K Γ) Q) : TM0.Cfg (Γ' K Γ) (Control Q) :=
  ⟨.run c.q, TapeReflection.tape c.Tape⟩

variable (k : K) (M : TM0.Machine (Γ' K Γ) Q) (emit : Γ' K Γ → Γ' K Γ)

omit [DecidableEq K] in
/-- Every live native source transition is one live native wrapper transition.
The full successor tape, not only the head observation, is preserved. -/
theorem run_step (a b : TM0.Cfg (Γ' K Γ) Q) (live : TM0.step M a = some b) :
    TM0.step (machine k M emit) (runConfiguration a) = some (runConfiguration b) := by
  rcases a with ⟨q, T⟩
  cases transition : M q T.head with
  | none =>
    simp only [TM0.step, transition, Option.map_none] at live
    cases live
  | some result =>
    rcases result with ⟨q', act⟩
    simp only [TM0.step, transition, Option.map_some] at live
    have endpoint := Option.some.inj live
    subst b
    cases act with
    | write x =>
      simp only [TM0.step, machine, runConfiguration, TapeReflection.tape_head,
        transition, Option.map_some, TapeReflection.statement, TapeReflection.tape_write]
    | move d =>
      simp only [TM0.step, machine, runConfiguration, TapeReflection.tape_head,
        transition, Option.map_some, TapeReflection.statement, TapeReflection.tape_move]

private theorem iterate_none {A : Type*} (f : A → Option A) (n : ℕ) :
    (flip Bind.bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n IH =>
    rw [Function.iterate_succ_apply', IH]
    rfl

omit [DecidableEq K] in
/-- The actual optional source iteration ending live contains no outer-none
prefix. Therefore the wrapper has the same literal iteration count. -/
theorem run_iterate (n : ℕ) (a b : TM0.Cfg (Γ' K Γ) Q)
    (live : (flip Bind.bind (TM0.step M))^[n] (some a) = some b) :
    (flip Bind.bind (TM0.step (machine k M emit)))^[n] (some (runConfiguration a)) =
      some (runConfiguration b) := by
  induction n generalizing a with
  | zero =>
    change some a = some b at live
    change some (runConfiguration a) = some (runConfiguration b)
    exact congrArg (fun c => some (runConfiguration c)) (Option.some.inj live)
  | succ n IH =>
    rw [Function.iterate_succ_apply] at live ⊢
    change (flip Bind.bind (TM0.step M))^[n] (TM0.step M a) = some b at live
    change (flip Bind.bind (TM0.step (machine k M emit)))^[n]
      (TM0.step (machine k M emit) (runConfiguration a)) = some (runConfiguration b)
    cases first : TM0.step M a with
    | none =>
      rw [first, iterate_none] at live
      cases live
    | some next =>
      rw [first] at live
      rw [run_step k M emit a next first]
      exact IH next live

/-- Actual source witness transported with the same stored count, for a live
endpoint. This makes no promise about lifting the original terminal none. -/
def liveRun (a b : TM0.Cfg (Γ' K Γ) Q)
    (before : StateTransition.EvalsTo (TM0.step M) a (some b)) :
    StateTransition.EvalsTo (TM0.step (machine k M emit))
      (runConfiguration a) (some (runConfiguration b)) where
  steps := before.steps
  evals_in_steps := run_iterate k M emit before.steps a b before.evals_in_steps

omit [DecidableEq K] in
theorem liveRun_steps (a b : TM0.Cfg (Γ' K Γ) Q)
    (before : StateTransition.EvalsTo (TM0.step M) a (some b)) :
    (liveRun k M emit a b before).steps = before.steps := rfl

/-- Prelude, same-count live simulation and one actual output write. The
premise is an actual native encoded-input run with a complete singleton tape. -/
def normalizedRun (raw : List (Γ k)) (q : Q) (a : Γ' K Γ)
    (before : StateTransition.EvalsTo (TM0.step M)
      (TM0.init (trInit k raw)) (some ⟨q, Tape.mk₁ [a]⟩))
    (stopped : M q a = none) :
    StateTransition.EvalsTo (TM0.step (machine k M emit))
      (TM0.init (input k raw)) (some ⟨.done, Tape.mk₁ [emit a]⟩) := by
  let beginning := preludeRun k M emit raw
  let mainRun := liveRun k M emit (TM0.init (trInit k raw))
    ⟨q, Tape.mk₁ [a]⟩ before
  let toSourceHalt := StateTransition.EvalsTo.trans
    (TM0.step (machine k M emit)) (TM0.init (input k raw))
    (runConfiguration (TM0.init (trInit k raw)))
    (some (runConfiguration ⟨q, Tape.mk₁ [a]⟩)) beginning mainRun
  let output : StateTransition.EvalsTo (TM0.step (machine k M emit))
      (runConfiguration ⟨q, Tape.mk₁ [a]⟩) (some ⟨.done, Tape.mk₁ [emit a]⟩) :=
    { steps := 1
      evals_in_steps := by
        change TM0.step (machine k M emit)
          ⟨.run q, TapeReflection.tape (Tape.mk₁ [a])⟩ = _
        rw [SingletonOutput.reflection_singleton]
        exact emit_singleton_step k M emit q a stopped }
  exact StateTransition.EvalsTo.trans (TM0.step (machine k M emit))
    (TM0.init (input k raw)) (runConfiguration ⟨q, Tape.mk₁ [a]⟩)
    (some ⟨.done, Tape.mk₁ [emit a]⟩) toSourceHalt output

theorem normalizedRun_steps (raw : List (Γ k)) (q : Q) (a : Γ' K Γ)
    (before : StateTransition.EvalsTo (TM0.step M)
      (TM0.init (trInit k raw)) (some ⟨q, Tape.mk₁ [a]⟩))
    (stopped : M q a = none) :
    (normalizedRun k M emit raw q a before stopped).steps =
      1 + (before.steps + preludeSteps raw) := rfl

/-- Quantitative composition preserves the source bound and charges the
literal prelude and emitter costs. It reaches a live done configuration. -/
def normalizedRunInTime (raw : List (Γ k)) (q : Q) (a : Γ' K Γ) (B : ℕ)
    (before : StateTransition.EvalsToInTime (TM0.step M)
      (TM0.init (trInit k raw)) (some ⟨q, Tape.mk₁ [a]⟩) B)
    (stopped : M q a = none) :
    StateTransition.EvalsToInTime (TM0.step (machine k M emit))
      (TM0.init (input k raw)) (some ⟨.done, Tape.mk₁ [emit a]⟩)
      (preludeSteps raw + B + 1) where
  toEvalsTo := normalizedRun k M emit raw q a before.toEvalsTo stopped
  steps_le_m := by
    change 1 + (before.steps + preludeSteps raw) ≤ preludeSteps raw + B + 1
    have bounded := Nat.add_le_add_left
      (Nat.add_le_add_right before.steps_le_m (preludeSteps raw)) 1
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using bounded

/-- The live normalized output pays one further transition to outer none.
The complete output is retained by normalizedRunInTime, not by the none value. -/
def normalizedOuterNone (raw : List (Γ k)) (q : Q) (a : Γ' K Γ) (B : ℕ)
    (before : StateTransition.EvalsToInTime (TM0.step M)
      (TM0.init (trInit k raw)) (some ⟨q, Tape.mk₁ [a]⟩) B)
    (stopped : M q a = none) :
    StateTransition.EvalsToInTime (TM0.step (machine k M emit))
      (TM0.init (input k raw)) none (preludeSteps raw + B + 2) := by
  let live := normalizedRunInTime k M emit raw q a B before stopped
  let terminal : StateTransition.EvalsToInTime (TM0.step (machine k M emit))
      (⟨.done, Tape.mk₁ [emit a]⟩ : TM0.Cfg (Γ' K Γ) (Control Q)) none 1 :=
    { steps := 1
      evals_in_steps := rfl
      steps_le_m := Nat.le_refl 1 }
  have after := StateTransition.EvalsToInTime.trans
    (TM0.step (machine k M emit)) (preludeSteps raw + B + 1) 1
    (TM0.init (input k raw)) ⟨.done, Tape.mk₁ [emit a]⟩ none live terminal
  simpa only [Nat.add_comm 1 (preludeSteps raw + B + 1)] using after

private theorem live_iteration_reaches {A : Type*} (f : A → Option A)
    (n : ℕ) (a b : A) (live : (flip Bind.bind f)^[n] (some a) = some b) :
    StateTransition.Reaches f a b := by
  induction n generalizing a with
  | zero =>
    change some a = some b at live
    have same := Option.some.inj live
    subst b
    exact Relation.ReflTransGen.refl
  | succ n IH =>
    rw [Function.iterate_succ_apply] at live
    change (flip Bind.bind f)^[n] (f a) = some b at live
    cases first : f a with
    | none =>
      rw [first, iterate_none] at live
      cases live
    | some next =>
      rw [first] at live
      exact Relation.ReflTransGen.head first (IH next live)

/-- Native TM0 evaluation actually returns the ordinary output singleton.
This follows from the composed live iteration and actual done transition. -/
theorem normalized_eval (raw : List (Γ k)) (q : Q) (a : Γ' K Γ)
    (before : StateTransition.EvalsTo (TM0.step M)
      (TM0.init (trInit k raw)) (some ⟨q, Tape.mk₁ [a]⟩))
    (stopped : M q a = none) :
    TM0.eval (machine k M emit) (input k raw) =
      Part.some (ListBlank.mk [emit a]) := by
  let run := normalizedRun k M emit raw q a before stopped
  apply Part.eq_some_iff.mpr
  apply (Part.mem_map_iff _).mpr
  refine ⟨⟨.done, Tape.mk₁ [emit a]⟩, ?_, rfl⟩
  apply StateTransition.mem_eval.mpr
  exact ⟨live_iteration_reaches (TM0.step (machine k M emit)) run.steps
    (TM0.init (input k raw)) ⟨.done, Tape.mk₁ [emit a]⟩ run.evals_in_steps,
    done_step k M emit _⟩

end Resources.TuringSimulation.MarkedInput
