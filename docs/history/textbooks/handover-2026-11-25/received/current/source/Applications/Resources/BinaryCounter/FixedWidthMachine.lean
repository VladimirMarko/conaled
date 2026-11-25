import Applications.Resources.BinaryCounter.FixedWidth
import Mathlib.Computability.TuringMachine.Computable

/-!
# An open finite-stack fixed-width predecessor

The actual TM2 blocks borrow low zero bits into a Unit stack, replace the first
true by false, and restore the borrowed prefix. At zero they actually restore
the original word. Every exit is a live caller label. Arbitrary protected stacks
and finite caller state remain unchanged through the first handoff; arbitrary
caller execution after that handoff has no such preservation promise.

The mathematical specification, remaining rank and lengths below are proof-side
objects. None is executed by a statement callback. Instantiating the explicit
finite index, alphabet, label and register families gives finite machine control.
The complete verifier and its computational-model/NP correspondence remain open.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.BinaryCounter.FixedWidthMachine

inductive Result
  | positive | zero
  deriving DecidableEq

instance : Fintype Result where
  elems := {.positive, .zero}
  complete result := by cases result <;> decide

/-- Independent literal-word predecessor meaning, including restored zero failure. -/
inductive PredSpec : Bits → Result → Bits → Prop
  | positive (zeros : Nat) (tail : Bits) :
      PredSpec (List.replicate zeros false ++ true :: tail) .positive
        (List.replicate zeros true ++ false :: tail)
  | zero (width : Nat) :
      PredSpec (List.replicate width false) .zero (List.replicate width false)

/-- A proof-side endpoint specification; never used in a machine callback. -/
def predSpec : Bits → Result × Bits
  | [] => (.zero, [])
  | true :: tail => (.positive, false :: tail)
  | false :: tail =>
      match predSpec tail with
      | (.positive, ys) => (.positive, true :: ys)
      | (.zero, ys) => (.zero, false :: ys)

theorem predSpec_first_true (zeros : Nat) (tail : Bits) :
    predSpec (List.replicate zeros false ++ true :: tail) =
      (.positive, List.replicate zeros true ++ false :: tail) := by
  induction zeros with
  | zero => rfl
  | succ zeros ih =>
      simp only [List.replicate_succ, List.cons_append, predSpec, ih]

theorem predSpec_replicate_false (width : Nat) :
    predSpec (List.replicate width false) = (.zero, List.replicate width false) := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [List.replicate_succ, predSpec, ih]

theorem bitWord_cases (fuel : Bits) :
    (∃ width, fuel = List.replicate width false) ∨
      ∃ zeros tail, fuel = List.replicate zeros false ++ true :: tail := by
  induction fuel with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons bit tail ih =>
      cases bit with
      | true => exact Or.inr ⟨0, tail, rfl⟩
      | false =>
          rcases ih with ⟨width, rfl⟩ | ⟨zeros, higher, rfl⟩
          · exact Or.inl ⟨width + 1, rfl⟩
          · exact Or.inr ⟨zeros + 1, higher, rfl⟩

theorem predSpec_spec (fuel : Bits) :
    PredSpec fuel (predSpec fuel).1 (predSpec fuel).2 := by
  rcases bitWord_cases fuel with ⟨width, rfl⟩ | ⟨zeros, tail, rfl⟩
  · rw [predSpec_replicate_false]
    exact .zero width
  · rw [predSpec_first_true]
    exact .positive zeros tail

theorem predSpec_iff (fuel : Bits) (result : Result) (final : Bits) :
    predSpec fuel = (result, final) ↔ PredSpec fuel result final := by
  constructor
  · intro equal
    simpa only [equal] using predSpec_spec fuel
  · intro spec
    cases spec with
    | positive zeros tail => exact predSpec_first_true zeros tail
    | zero width => exact predSpec_replicate_false width

theorem predSpec_source (fuel : Bits) :
    predSpec fuel =
      match (decFixedRun fuel).1 with
      | none => (.zero, fuel)
      | some ys => (.positive, ys) := by
  induction fuel with
  | nil => rfl
  | cons bit tail ih =>
      cases bit with
      | true => rfl
      | false =>
          cases returned : (decFixedRun tail).1 with
          | none =>
              simp only [predSpec, ih, returned, decFixedRun_false, bind]
          | some ys =>
              simp only [predSpec, ih, returned, decFixedRun_false, bind]

theorem predSpec_of_some {fuel ys : Bits} (returned : (decFixedRun fuel).1 = some ys) :
    predSpec fuel = (.positive, ys) := by rw [predSpec_source, returned]

theorem predSpec_of_none {fuel : Bits} (returned : (decFixedRun fuel).1 = none) :
    predSpec fuel = (.zero, fuel) := by rw [predSpec_source, returned]

theorem predSpec_positive_iff (fuel ys : Bits) :
    predSpec fuel = (.positive, ys) ↔ (decFixedRun fuel).1 = some ys := by
  rw [predSpec_source]
  cases returned : (decFixedRun fuel).1 <;> simp

theorem predSpec_zero_iff (fuel : Bits) :
    predSpec fuel = (.zero, fuel) ↔ (decFixedRun fuel).1 = none := by
  rw [predSpec_source]
  cases returned : (decFixedRun fuel).1 <;> simp

theorem predSpec_width (fuel : Bits) : (predSpec fuel).2.length = fuel.length := by
  rw [predSpec_source]
  cases returned : (decFixedRun fuel).1 with
  | none => rfl
  | some ys => exact decFixedRun_some_length returned

theorem predSpec_positive_value {fuel ys : Bits}
    (result : predSpec fuel = (.positive, ys)) : value fuel = value ys + 1 :=
  decFixedRun_some_value ((predSpec_positive_iff fuel ys).mp result)

/-- Exact actual handoff count, classified mathematically rather than at runtime. -/
def runSteps : Bits → Nat
  | [] => 2
  | true :: _ => 2
  | false :: raw => runSteps raw + 2

theorem runSteps_pos (fuel : Bits) : 0 < runSteps fuel := by
  cases fuel with
  | nil => decide
  | cons bit tail => cases bit <;> simp [runSteps]

theorem runSteps_first_true (zeros : Nat) (tail : Bits) :
    runSteps (List.replicate zeros false ++ true :: tail) = 2 * zeros + 2 := by
  induction zeros with
  | zero => rfl
  | succ zeros ih =>
      simp only [List.replicate_succ, List.cons_append, runSteps, ih]
      omega

theorem runSteps_replicate_false (width : Nat) :
    runSteps (List.replicate width false) = 2 * width + 2 := by
  induction width with
  | zero => rfl
  | succ width ih =>
      simp only [List.replicate_succ, runSteps, ih]
      omega

theorem runSteps_le (fuel : Bits) : runSteps fuel ≤ 2 * fuel.length + 2 := by
  induction fuel with
  | nil => rfl
  | cons bit tail ih => cases bit <;> simp only [runSteps, List.length_cons] <;> omega

theorem runSteps_le_source_cost (fuel : Bits) : runSteps fuel ≤ (decFixedRun fuel).2 := by
  rcases bitWord_cases fuel with ⟨width, rfl⟩ | ⟨zeros, tail, rfl⟩
  · rw [runSteps_replicate_false, decFixedRun_replicate_false]
  · rw [runSteps_first_true, decFixedRun_first_true]
    omega

inductive LocalStack
  | fuel | borrowed
  deriving DecidableEq

instance : Fintype LocalStack where
  elems := {.fuel, .borrowed}
  complete stack := by cases stack <;> decide

inductive Phase
  | borrow | restoreTrue | restoreFalse
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.borrow, .restoreTrue, .restoreFalse}
  complete phase := by cases phase <;> decide

abbrev StackId (K : Type) := LocalStack ⊕ K
abbrev External (Λ : Type) := Result ⊕ Λ
abbrev Label (Λ : Type) := Phase ⊕ External Λ
abbrev Registers (R : Type) := Option Bool × R

variable {K Λ R : Type} {Γ : K → Type}

abbrev alphabet (Γ : K → Type) : StackId K → Type
  | .inl .fuel => Bool
  | .inl .borrowed => Unit
  | .inr k => Γ k

instance alphabetFintype [∀ k, Fintype (Γ k)] (k : StackId K) :
    Fintype (alphabet Γ k) := by
  cases k with
  | inl slot => cases slot <;> exact inferInstance
  | inr k => exact inferInstance

abbrev Statement (Γ : K → Type) (Λ R : Type) :=
  Turing.TM2.Stmt (alphabet Γ) (Label Λ) (Registers R)
abbrev Cfg (Γ : K → Type) (Λ R : Type) :=
  Turing.TM2.Cfg (alphabet Γ) (Label Λ) (Registers R)

def phaseLabel (phase : Phase) : Label Λ := .inl phase
def resultLabel (result : Result) : Label Λ := .inr (.inl result)
def callerLabel (label : Λ) : Label Λ := .inr (.inr label)

def reset (regs : Registers R) : Registers R := (none, regs.2)
def storeBit (regs : Registers R) (bit : Option Bool) : Registers R := (bit, regs.2)
def storeBorrowed (regs : Registers R) (token : Option Unit) : Registers R :=
  (token.map (fun _ => false), regs.2)

def jump (label : Label Λ) : Statement Γ Λ R :=
  .load reset (.goto (fun _ => label))

/-- Only finite observations, constant pushes, finite resets and actual gotos. -/
def block : Phase → Statement Γ Λ R
  | .borrow =>
      .pop (.inl .fuel) storeBit (.branch (fun regs => regs.1.isSome)
        (.branch (fun regs => regs.1.getD false)
          (.push (.inl .fuel) (fun _ => false) (jump (phaseLabel .restoreTrue)))
          (.push (.inl .borrowed) (fun _ => ()) (jump (phaseLabel .borrow))))
        (jump (phaseLabel .restoreFalse)))
  | .restoreTrue =>
      .pop (.inl .borrowed) storeBorrowed (.branch (fun regs => regs.1.isSome)
        (.push (.inl .fuel) (fun _ => true) (jump (phaseLabel .restoreTrue)))
        (jump (resultLabel .positive)))
  | .restoreFalse =>
      .pop (.inl .borrowed) storeBorrowed (.branch (fun regs => regs.1.isSome)
        (.push (.inl .fuel) (fun _ => false) (jump (phaseLabel .restoreFalse)))
        (jump (resultLabel .zero)))

def program (caller : External Λ → Statement Γ Λ R) : Label Λ → Statement Γ Λ R
  | .inl phase => block phase
  | .inr label => caller label

theorem program_eq_of_agrees (ambient : Label Λ → Statement Γ Λ R)
    (owned : ∀ phase, ambient (phaseLabel phase) = block phase) :
    ambient = program (fun external => ambient (.inr external)) := by
  funext label
  cases label with
  | inl phase => exact owned phase
  | inr external => rfl

def cfg (label : Option (Label Λ)) (regs : Registers R) (fuel : Bits)
    (borrowed : List Unit) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R where
  l := label
  var := regs
  stk
    | .inl .fuel => fuel
    | .inl .borrowed => borrowed
    | .inr k => ctx k

theorem cfg_ext {left right : Cfg Γ Λ R}
    (label : left.l = right.l) (regs : left.var = right.var)
    (fuel : left.stk (.inl .fuel) = right.stk (.inl .fuel))
    (borrowed : left.stk (.inl .borrowed) = right.stk (.inl .borrowed))
    (ctx : ∀ k, left.stk (.inr k) = right.stk (.inr k)) : left = right := by
  have stackEq : left.stk = right.stk := by
    funext k
    cases k with
    | inl slot => cases slot with
      | fuel => exact fuel
      | borrowed => exact borrowed
    | inr k => exact ctx k
  cases left
  cases right
  cases label
  cases regs
  cases stackEq
  rfl

theorem cfg_eta (c : Cfg Γ Λ R) :
    cfg c.l c.var (c.stk (.inl .fuel)) (c.stk (.inl .borrowed))
      (fun k => c.stk (.inr k)) = c := by
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

variable [DecidableEq K]

def step (caller : External Λ → Statement Γ Λ R) : Cfg Γ Λ R → Option (Cfg Γ Λ R) :=
  Turing.TM2.step (program caller)

def next (caller : External Λ → Statement Γ Λ R) (c : Option (Cfg Γ Λ R)) :
    Option (Cfg Γ Λ R) := c.bind (step caller)

@[simp] theorem next_none (caller : External Λ → Statement Γ Λ R) : next caller none = none := rfl
@[simp] theorem next_some (caller : External Λ → Statement Γ Λ R) (c : Cfg Γ Λ R) :
    next caller (some c) = step caller c := rfl

variable (caller : External Λ → Statement Γ Λ R)

theorem borrow_step_nil (regs : Registers R) (borrowed : List Unit)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .borrow)) regs [] borrowed ctx) =
      some (cfg (some (phaseLabel .restoreFalse)) (reset regs) [] borrowed ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem borrow_step_false (raw : Bits) (regs : Registers R) (borrowed : List Unit)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .borrow)) regs (false :: raw) borrowed ctx) =
      some (cfg (some (phaseLabel .borrow)) (reset regs) raw (() :: borrowed) ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem borrow_step_true (tail : Bits) (regs : Registers R) (borrowed : List Unit)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .borrow)) regs (true :: tail) borrowed ctx) =
      some (cfg (some (phaseLabel .restoreTrue)) (reset regs) (false :: tail) borrowed ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem restoreTrue_step_nil (raw : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .restoreTrue)) regs raw [] ctx) =
      some (cfg (some (resultLabel .positive)) (reset regs) raw [] ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem restoreTrue_step_cons (raw : Bits) (regs : Registers R) (borrowed : List Unit)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .restoreTrue)) regs raw (() :: borrowed) ctx) =
      some (cfg (some (phaseLabel .restoreTrue)) (reset regs) (true :: raw) borrowed ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem restoreFalse_step_nil (raw : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .restoreFalse)) regs raw [] ctx) =
      some (cfg (some (resultLabel .zero)) (reset regs) raw [] ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem restoreFalse_step_cons (raw : Bits) (regs : Registers R) (borrowed : List Unit)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .restoreFalse)) regs raw (() :: borrowed) ctx) =
      some (cfg (some (phaseLabel .restoreFalse)) (reset regs) (false :: raw) borrowed ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem iterate_step (n : Nat) (c d : Cfg Γ Λ R) (transition : step caller c = some d) :
    (next caller)^[n + 1] (some c) = (next caller)^[n] (some d) := by
  rw [Function.iterate_succ_apply, next_some, transition]

private theorem replicate_append_cons (n : Nat) (bit : Bool) (raw : Bits) :
    List.replicate n bit ++ bit :: raw = List.replicate (n + 1) bit ++ raw := by
  rw [List.replicate_add]
  simp only [List.replicate_one, List.append_assoc, List.singleton_append]

theorem restoreTrue_iterate (raw : Bits) (borrowed : List Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[borrowed.length + 1]
        (some (cfg (some (phaseLabel .restoreTrue)) regs raw borrowed ctx)) =
      some (cfg (some (resultLabel .positive)) (reset regs)
        (List.replicate borrowed.length true ++ raw) [] ctx) := by
  induction borrowed generalizing raw regs with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, next_some,
        restoreTrue_step_nil, List.replicate_zero, List.nil_append]
  | cons token borrowed ih =>
      cases token
      rw [show (() :: borrowed).length + 1 = (borrowed.length + 1) + 1 by rfl,
        iterate_step caller _ _ _ (restoreTrue_step_cons caller raw regs borrowed ctx), ih]
      simp only [reset, List.length_cons, replicate_append_cons]

theorem restoreFalse_iterate (raw : Bits) (borrowed : List Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[borrowed.length + 1]
        (some (cfg (some (phaseLabel .restoreFalse)) regs raw borrowed ctx)) =
      some (cfg (some (resultLabel .zero)) (reset regs)
        (List.replicate borrowed.length false ++ raw) [] ctx) := by
  induction borrowed generalizing raw regs with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, next_some,
        restoreFalse_step_nil, List.replicate_zero, List.nil_append]
  | cons token borrowed ih =>
      cases token
      rw [show (() :: borrowed).length + 1 = (borrowed.length + 1) + 1 by rfl,
        iterate_step caller _ _ _ (restoreFalse_step_cons caller raw regs borrowed ctx), ih]
      simp only [reset, List.length_cons, replicate_append_cons]

theorem borrow_first_true_iterate (zeros : Nat) (tail : Bits) (borrowed : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * zeros + borrowed.length + 2]
        (some (cfg (some (phaseLabel .borrow)) regs
          (List.replicate zeros false ++ true :: tail) borrowed ctx)) =
      some (cfg (some (resultLabel .positive)) (reset regs)
        (List.replicate (borrowed.length + zeros) true ++ false :: tail) [] ctx) := by
  induction zeros generalizing borrowed regs with
  | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, List.replicate_zero, List.nil_append]
      rw [show borrowed.length + 2 = (borrowed.length + 1) + 1 by rfl,
        iterate_step caller _ _ _ (borrow_step_true caller tail regs borrowed ctx),
        restoreTrue_iterate]
      rfl
  | succ zeros ih =>
      rw [show 2 * (zeros + 1) + borrowed.length + 2 =
        (2 * zeros + (() :: borrowed).length + 2) + 1 by simp only [List.length_cons]; omega]
      simp only [List.replicate_succ, List.cons_append]
      rw [iterate_step caller _ _ _ (borrow_step_false caller _ regs borrowed ctx), ih]
      have count : borrowed.length + 1 + zeros = borrowed.length + (zeros + 1) := by omega
      simp only [reset, List.length_cons, count]

theorem borrow_zero_iterate (width : Nat) (borrowed : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * width + borrowed.length + 2]
        (some (cfg (some (phaseLabel .borrow)) regs
          (List.replicate width false) borrowed ctx)) =
      some (cfg (some (resultLabel .zero)) (reset regs)
        (List.replicate (borrowed.length + width) false) [] ctx) := by
  induction width generalizing borrowed regs with
  | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, List.replicate_zero]
      rw [show borrowed.length + 2 = (borrowed.length + 1) + 1 by rfl,
        iterate_step caller _ _ _ (borrow_step_nil caller regs borrowed ctx),
        restoreFalse_iterate]
      simp only [List.append_nil, reset]
  | succ width ih =>
      rw [show 2 * (width + 1) + borrowed.length + 2 =
        (2 * width + (() :: borrowed).length + 2) + 1 by simp only [List.length_cons]; omega]
      simp only [List.replicate_succ]
      rw [iterate_step caller _ _ _ (borrow_step_false caller _ regs borrowed ctx), ih]
      have count : borrowed.length + 1 + width = borrowed.length + (width + 1) := by omega
      simp only [reset, List.length_cons, count]

/-- Existing borrowed tokens represent low zeros already removed from the logical input. -/
theorem borrow_iterate (raw : Bits) (borrowed : List Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[runSteps raw + borrowed.length]
        (some (cfg (some (phaseLabel .borrow)) regs raw borrowed ctx)) =
      some (cfg
        (some (resultLabel (predSpec (List.replicate borrowed.length false ++ raw)).1))
        (reset regs) (predSpec (List.replicate borrowed.length false ++ raw)).2 [] ctx) := by
  rcases bitWord_cases raw with ⟨width, rfl⟩ | ⟨zeros, tail, rfl⟩
  · rw [← List.replicate_add, predSpec_replicate_false, runSteps_replicate_false]
    rw [show 2 * width + 2 + borrowed.length = 2 * width + borrowed.length + 2 by omega]
    exact borrow_zero_iterate caller width borrowed regs ctx
  · rw [← List.append_assoc, ← List.replicate_add, predSpec_first_true, runSteps_first_true]
    rw [show 2 * zeros + 2 + borrowed.length = 2 * zeros + borrowed.length + 2 by omega]
    exact borrow_first_true_iterate caller zeros tail borrowed regs ctx

theorem borrow_run (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[runSteps raw]
        (some (cfg (some (phaseLabel .borrow)) regs raw [] ctx)) =
      some (cfg (some (resultLabel (predSpec raw).1)) (reset regs) (predSpec raw).2 [] ctx) := by
  simpa only [List.length_nil, Nat.add_zero, List.replicate_zero, List.nil_append] using
    borrow_iterate caller raw [] regs ctx

theorem borrow_run_first_true (zeros : Nat) (tail : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * zeros + 2]
        (some (cfg (some (phaseLabel .borrow)) regs
          (List.replicate zeros false ++ true :: tail) [] ctx)) =
      some (cfg (some (resultLabel .positive)) (reset regs)
        (List.replicate zeros true ++ false :: tail) [] ctx) := by
  simpa only [List.length_nil, Nat.add_zero, Nat.zero_add] using
    borrow_first_true_iterate caller zeros tail [] regs ctx

theorem borrow_run_replicate_false (width : Nat) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * width + 2]
        (some (cfg (some (phaseLabel .borrow)) regs (List.replicate width false) [] ctx)) =
      some (cfg (some (resultLabel .zero)) (reset regs) (List.replicate width false) [] ctx) := by
  simpa only [List.length_nil, Nat.add_zero, Nat.zero_add] using
    borrow_zero_iterate caller width [] regs ctx

theorem borrow_run_of_some (raw ys : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (returned : (decFixedRun raw).1 = some ys) :
    (next caller)^[runSteps raw]
        (some (cfg (some (phaseLabel .borrow)) regs raw [] ctx)) =
      some (cfg (some (resultLabel .positive)) (reset regs) ys [] ctx) := by
  rw [borrow_run, predSpec_of_some returned]

theorem borrow_run_of_none (raw : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (returned : (decFixedRun raw).1 = none) :
    (next caller)^[runSteps raw]
        (some (cfg (some (phaseLabel .borrow)) regs raw [] ctx)) =
      some (cfg (some (resultLabel .zero)) (reset regs) raw [] ctx) := by
  rw [borrow_run, predSpec_of_none returned]

/-- Actual timed evidence to a live caller configuration, with no caller statement executed. -/
def borrowInTime (raw : Bits) (borrowed : List Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .borrow)) regs raw borrowed ctx)
      (some (cfg
        (some (resultLabel (predSpec (List.replicate borrowed.length false ++ raw)).1))
        (reset regs) (predSpec (List.replicate borrowed.length false ++ raw)).2 [] ctx))
      (runSteps raw + borrowed.length) where
  steps := runSteps raw + borrowed.length
  evals_in_steps := borrow_iterate caller raw borrowed regs ctx
  steps_le_m := Nat.le_refl _

def borrowInLinearTime (raw : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .borrow)) regs raw [] ctx)
      (some (cfg (some (resultLabel (predSpec raw).1)) (reset regs) (predSpec raw).2 [] ctx))
      (2 * raw.length + 2) where
  steps := runSteps raw
  evals_in_steps := borrow_run caller raw regs ctx
  steps_le_m := runSteps_le raw

/-- Owned labels are disjoint from every live caller continuation. -/
def Owned : Option (Label Λ) → Prop
  | some (.inl _) => True
  | _ => False

def phaseSteps : Phase → Bits → List Unit → Nat
  | .borrow, raw, borrowed => runSteps raw + borrowed.length
  | .restoreTrue, _, borrowed => borrowed.length + 1
  | .restoreFalse, _, borrowed => borrowed.length + 1

/-- A proof-only rank. External code may do anything after rank reaches zero. -/
def remainingSteps (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl phase) => phaseSteps phase (c.stk (.inl .fuel)) (c.stk (.inl .borrowed))
  | _ => 0

omit [DecidableEq K] in
theorem remainingSteps_pos_iff (c : Cfg Γ Λ R) : 0 < remainingSteps c ↔ Owned c.l := by
  cases labelEq : c.l with
  | none => simp [remainingSteps, Owned, labelEq]
  | some label => cases label with
    | inr external => simp [remainingSteps, Owned, labelEq]
    | inl phase =>
        cases phase with
        | borrow =>
            simp only [remainingSteps, labelEq, phaseSteps, Owned, iff_true]
            have positive := runSteps_pos (c.stk (.inl .fuel))
            omega
        | restoreTrue => simp [remainingSteps, Owned, labelEq, phaseSteps]
        | restoreFalse => simp [remainingSteps, Owned, labelEq, phaseSteps]

omit [DecidableEq K] in
theorem owned_cases (c : Cfg Γ Λ R) (owned : Owned c.l) :
    ∃ phase regs raw borrowed ctx,
      c = cfg (some (phaseLabel phase)) regs raw borrowed ctx := by
  cases labelEq : c.l with
  | none => simp [Owned, labelEq] at owned
  | some label => cases label with
    | inr external => simp [Owned, labelEq] at owned
    | inl phase =>
        refine ⟨phase, c.var, c.stk (.inl .fuel), c.stk (.inl .borrowed),
          (fun k => c.stk (.inr k)), ?_⟩
        simpa only [labelEq, phaseLabel] using (cfg_eta c).symm

/-- One actual owned transition has exact rank decrease and preserves represented cells. -/
theorem phase_step_data (phase : Phase) (raw : Bits) (borrowed : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∃ reached,
      step caller (cfg (some (phaseLabel phase)) regs raw borrowed ctx) = some reached ∧
      phaseSteps phase raw borrowed = remainingSteps reached + 1 ∧
      reached.var = reset regs ∧
      (reached.stk (.inl .fuel)).length + (reached.stk (.inl .borrowed)).length =
        raw.length + borrowed.length ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  cases phase with
  | borrow =>
      cases raw with
      | nil =>
          refine ⟨_, borrow_step_nil caller regs borrowed ctx, ?_, rfl, rfl, fun _ => rfl⟩
          simp only [phaseSteps, runSteps, remainingSteps, cfg, phaseLabel]
          omega
      | cons bit raw => cases bit with
        | false =>
            refine ⟨_, borrow_step_false caller raw regs borrowed ctx, ?_, rfl, ?_, fun _ => rfl⟩
            · simp only [phaseSteps, runSteps, remainingSteps, cfg, phaseLabel, List.length_cons]
              omega
            · simp only [cfg, List.length_cons]
              omega
        | true =>
            refine ⟨_, borrow_step_true caller raw regs borrowed ctx, ?_, rfl, rfl, fun _ => rfl⟩
            simp only [phaseSteps, runSteps, remainingSteps, cfg, phaseLabel]
            omega
  | restoreTrue =>
      cases borrowed with
      | nil =>
          refine ⟨_, restoreTrue_step_nil caller raw regs ctx, ?_, rfl, rfl, fun _ => rfl⟩
          rfl
      | cons token borrowed =>
          cases token
          refine ⟨_, restoreTrue_step_cons caller raw regs borrowed ctx, ?_, rfl, ?_, fun _ => rfl⟩
          · rfl
          · simp only [cfg, List.length_cons]
            omega
  | restoreFalse =>
      cases borrowed with
      | nil =>
          refine ⟨_, restoreFalse_step_nil caller raw regs ctx, ?_, rfl, rfl, fun _ => rfl⟩
          rfl
      | cons token borrowed =>
          cases token
          refine ⟨_, restoreFalse_step_cons caller raw regs borrowed ctx, ?_, rfl, ?_, fun _ => rfl⟩
          · rfl
          · simp only [cfg, List.length_cons]
            omega

def LocalStep (before after : Cfg Γ Λ R) : Prop :=
  Owned before.l ∧ step caller before = some after

theorem local_step_data {before after : Cfg Γ Λ R} (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 ∧
    after.var.1 = none ∧ after.var.2 = before.var.2 ∧
    (after.stk (.inl .fuel)).length + (after.stk (.inl .borrowed)).length =
      (before.stk (.inl .fuel)).length + (before.stk (.inl .borrowed)).length ∧
    ∀ k, after.stk (.inr k) = before.stk (.inr k) := by
  obtain ⟨phase, regs, raw, borrowed, ctx, rfl⟩ := owned_cases before transition.1
  obtain ⟨reached, executed, rank, registers, cells, frame⟩ :=
    phase_step_data caller phase raw borrowed regs ctx
  have equal : reached = after := Option.some.inj (executed.symm.trans transition.2)
  subst after
  exact ⟨rank, by rw [registers]; rfl, by rw [registers]; rfl, cells, frame⟩

theorem local_step_remaining {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 :=
  (local_step_data caller transition).1

theorem local_progress (before : Cfg Γ Λ R) (positive : 0 < remainingSteps before) :
    ∃ after, step caller before = some after ∧ remainingSteps before = remainingSteps after + 1 := by
  obtain ⟨phase, regs, raw, borrowed, ctx, rfl⟩ :=
    owned_cases before ((remainingSteps_pos_iff before).mp positive)
  obtain ⟨after, executed, rank, _⟩ := phase_step_data caller phase raw borrowed regs ctx
  exact ⟨after, executed, rank⟩

/-- The same owned body is executed for arbitrary choices of external caller code. -/
theorem step_caller_independent (other : External Λ → Statement Γ Λ R)
    (c : Cfg Γ Λ R) (owned : Owned c.l) : step caller c = step other c := by
  obtain ⟨phase, regs, raw, borrowed, ctx, rfl⟩ := owned_cases c owned
  rfl

/-- Actual prefix execution from a decreasing rank; the premise is proved from local blocks. -/
theorem ranked_prefix {σ : Type} (transition : σ → Option σ) (rank : σ → Nat)
    (progress : ∀ c, 0 < rank c → ∃ d, transition c = some d ∧ rank c = rank d + 1)
    (n : Nat) (start : σ) (bound : n ≤ rank start) :
    ∃ reached, (fun c : Option σ => c.bind transition)^[n] (some start) = some reached ∧
      rank reached = rank start - n ∧
      Relation.ReflTransGen (fun c d => 0 < rank c ∧ transition c = some d) start reached := by
  induction n generalizing start with
  | zero => exact ⟨start, rfl, by omega, .refl⟩
  | succ n ih =>
      have positive : 0 < rank start := by omega
      obtain ⟨middle, first, decreased⟩ := progress start positive
      obtain ⟨reached, tailRun, remaining, path⟩ := ih middle (by omega)
      refine ⟨reached, ?_, by omega, ?_⟩
      · rw [Function.iterate_succ_apply]
        simpa only [Option.bind_some, first] using tailRun
      · exact (Relation.ReflTransGen.single ⟨positive, first⟩).trans path

theorem ranked_prefix_eq {σ : Type} (first second : σ → Option σ) (rank : σ → Nat)
    (progress : ∀ c, 0 < rank c → ∃ d, first c = some d ∧ rank c = rank d + 1)
    (agree : ∀ c, 0 < rank c → first c = second c)
    (n : Nat) (start : σ) (bound : n ≤ rank start) :
    (fun c : Option σ => c.bind first)^[n] (some start) =
      (fun c : Option σ => c.bind second)^[n] (some start) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
      have positive : 0 < rank start := by omega
      obtain ⟨middle, executed, decreased⟩ := progress start positive
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [Option.bind_some, ← agree start positive, executed]
      exact ih middle (by omega)

theorem prefix_local_register (n : Nat) (start reached : Cfg Γ Λ R)
    (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached)
    (positive : 0 < n) : reached.var.1 = none := by
  induction n generalizing start reached with
  | zero => omega
  | succ n ih =>
      have rankPositive : 0 < remainingSteps start := by omega
      obtain ⟨middle, first, decreased⟩ := local_progress caller start rankPositive
      have owned := (remainingSteps_pos_iff start).mp rankPositive
      have canonical := (local_step_data caller ⟨owned, first⟩).2.1
      rw [Function.iterate_succ_apply, next_some, first] at executed
      by_cases empty : n = 0
      · subst n
        have equal : middle = reached := Option.some.inj executed
        simpa only [equal] using canonical
      · exact ih middle reached (by omega) executed (by omega)

theorem phase_prefix (phase : Phase) (raw : Bits) (borrowed : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat)
    (bound : n ≤ phaseSteps phase raw borrowed) :
    ∃ reached,
      (next caller)^[n] (some (cfg (some (phaseLabel phase)) regs raw borrowed ctx)) = some reached ∧
      remainingSteps reached = phaseSteps phase raw borrowed - n ∧
      Relation.ReflTransGen (LocalStep caller)
        (cfg (some (phaseLabel phase)) regs raw borrowed ctx) reached ∧
      (n < phaseSteps phase raw borrowed ↔ Owned reached.l) ∧
      (0 < n → reached.var.1 = none) := by
  obtain ⟨reached, executed, rank, path⟩ := ranked_prefix (step caller) remainingSteps
    (local_progress caller) n (cfg (some (phaseLabel phase)) regs raw borrowed ctx) bound
  change remainingSteps reached = phaseSteps phase raw borrowed - n at rank
  refine ⟨reached, executed, rank, ?_, ?_, ?_⟩
  · exact Relation.ReflTransGen.mono
      (fun before _ h => ⟨(remainingSteps_pos_iff before).mp h.1, h.2⟩) _ _ path
  · rw [← remainingSteps_pos_iff, rank]
    omega
  · exact prefix_local_register caller n
      (cfg (some (phaseLabel phase)) regs raw borrowed ctx) reached bound executed

theorem phase_prefix_caller_independent (other : External Λ → Statement Γ Λ R)
    (phase : Phase) (raw : Bits) (borrowed : List Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ phaseSteps phase raw borrowed) :
    (next caller)^[n] (some (cfg (some (phaseLabel phase)) regs raw borrowed ctx)) =
      (next other)^[n] (some (cfg (some (phaseLabel phase)) regs raw borrowed ctx)) := by
  exact ranked_prefix_eq (step caller) (step other) remainingSteps (local_progress caller)
    (fun c positive => step_caller_independent caller other c ((remainingSteps_pos_iff c).mp positive))
    n _ bound

variable [Fintype K]

/-- Every occupied actual stack cell, including arbitrary caller workspace. -/
def stackCells (c : Cfg Γ Λ R) : Nat :=
  (c.stk (.inl .fuel)).length + (c.stk (.inl .borrowed)).length +
    ∑ k, (c.stk (.inr k)).length

theorem local_step_preserves {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    after.var.2 = before.var.2 ∧
      (∀ k, after.stk (.inr k) = before.stk (.inr k)) ∧ stackCells after = stackCells before := by
  obtain ⟨_, _, registers, cells, frame⟩ := local_step_data caller transition
  refine ⟨registers, frame, ?_⟩
  simp only [stackCells, cells, frame]

/-- Caller bodies are deliberately excluded from this local reach relation. -/
theorem local_reaches_preserves {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2 = start.var.2 ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧ stackCells reached = stackCells start := by
  induction path with
  | refl => exact ⟨rfl, fun _ => rfl, rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨registers, frame, cells⟩ := local_step_preserves caller transition
      exact ⟨registers.trans ih.1, fun k => (frame k).trans (ih.2.1 k), cells.trans ih.2.2⟩

/-- The changing actual fuel and Unit stack still represent one independent original word. -/
def FuelRepresents (original : Bits) (c : Cfg Γ Λ R) : Prop :=
  match c.l with
  | some (.inl .borrow) =>
      original = List.replicate (c.stk (.inl .borrowed)).length false ++ c.stk (.inl .fuel)
  | some (.inl .restoreTrue) =>
      ∃ rebuilt tail,
        c.stk (.inl .fuel) = List.replicate rebuilt true ++ false :: tail ∧
        original = List.replicate ((c.stk (.inl .borrowed)).length + rebuilt) false ++ true :: tail
  | some (.inl .restoreFalse) =>
      ∃ rebuilt,
        c.stk (.inl .fuel) = List.replicate rebuilt false ∧
        original = List.replicate ((c.stk (.inl .borrowed)).length + rebuilt) false
  | some (.inr (.inl result)) =>
      c.stk (.inl .borrowed) = [] ∧ PredSpec original result (c.stk (.inl .fuel))
  | _ => False

omit [Fintype K] in
theorem fuelRepresents_step {original : Bits} {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) (represented : FuelRepresents original before) :
    FuelRepresents original after := by
  rcases transition with ⟨owned, executed⟩
  obtain ⟨phase, regs, raw, borrowed, ctx, rfl⟩ := owned_cases before owned
  cases phase with
  | borrow =>
      change original = List.replicate borrowed.length false ++ raw at represented
      cases raw with
      | nil =>
          rw [borrow_step_nil] at executed
          cases Option.some.inj executed
          change ∃ rebuilt, [] = List.replicate rebuilt false ∧
            original = List.replicate (borrowed.length + rebuilt) false
          exact ⟨0, rfl, by simpa only [Nat.add_zero, List.append_nil] using represented⟩
      | cons bit raw => cases bit with
        | false =>
            rw [borrow_step_false] at executed
            cases Option.some.inj executed
            change original = List.replicate (() :: borrowed).length false ++ raw
            simpa only [List.length_cons, replicate_append_cons] using represented
        | true =>
            rw [borrow_step_true] at executed
            cases Option.some.inj executed
            change ∃ rebuilt tail, false :: raw = List.replicate rebuilt true ++ false :: tail ∧
              original = List.replicate (borrowed.length + rebuilt) false ++ true :: tail
            exact ⟨0, raw, rfl, by simpa only [Nat.add_zero] using represented⟩
  | restoreTrue =>
      change ∃ rebuilt tail, raw = List.replicate rebuilt true ++ false :: tail ∧
        original = List.replicate (borrowed.length + rebuilt) false ++ true :: tail at represented
      obtain ⟨rebuilt, tail, rawEq, originalEq⟩ := represented
      cases borrowed with
      | nil =>
          rw [restoreTrue_step_nil] at executed
          cases Option.some.inj executed
          change [] = [] ∧ PredSpec original .positive raw
          refine ⟨rfl, ?_⟩
          rw [rawEq, originalEq]
          simpa only [List.length_nil, Nat.zero_add] using PredSpec.positive rebuilt tail
      | cons token borrowed =>
          cases token
          rw [restoreTrue_step_cons] at executed
          cases Option.some.inj executed
          change ∃ count higher,
            true :: raw = List.replicate count true ++ false :: higher ∧
            original = List.replicate (borrowed.length + count) false ++ true :: higher
          refine ⟨rebuilt + 1, tail, ?_, ?_⟩
          · rw [rawEq]
            rfl
          · rw [originalEq]
            congr 2
            simp only [List.length_cons]
            omega
  | restoreFalse =>
      change ∃ rebuilt, raw = List.replicate rebuilt false ∧
        original = List.replicate (borrowed.length + rebuilt) false at represented
      obtain ⟨rebuilt, rawEq, originalEq⟩ := represented
      cases borrowed with
      | nil =>
          rw [restoreFalse_step_nil] at executed
          cases Option.some.inj executed
          change [] = [] ∧ PredSpec original .zero raw
          refine ⟨rfl, ?_⟩
          rw [rawEq, originalEq]
          simpa only [List.length_nil, Nat.zero_add] using PredSpec.zero rebuilt
      | cons token borrowed =>
          cases token
          rw [restoreFalse_step_cons] at executed
          cases Option.some.inj executed
          change ∃ count, false :: raw = List.replicate count false ∧
            original = List.replicate (borrowed.length + count) false
          refine ⟨rebuilt + 1, ?_, ?_⟩
          · rw [rawEq]
            rfl
          · rw [originalEq]
            congr 1
            simp only [List.length_cons]
            omega

omit [Fintype K] in
theorem fuelRepresents_reaches {original : Bits} {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached)
    (represented : FuelRepresents original start) : FuelRepresents original reached := by
  induction path with
  | refl => exact represented
  | @tail before after _ transition ih => exact fuelRepresents_step caller transition ih

omit [Fintype K] in
theorem borrow_prefix_represents (raw : Bits) (borrowed : List Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ runSteps raw + borrowed.length)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel .borrow)) regs raw borrowed ctx)) = some reached) :
    FuelRepresents (List.replicate borrowed.length false ++ raw) reached := by
  obtain ⟨actual, run, _, path, _, _⟩ := phase_prefix caller .borrow raw borrowed regs ctx n bound
  have equal : actual = reached := Option.some.inj (run.symm.trans executed)
  subst reached
  exact fuelRepresents_reaches caller path rfl

end Resources.BinaryCounter.FixedWidthMachine
