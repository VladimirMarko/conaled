import Applications.Resources.BinaryCounter.FixedWidthMachine
import Applications.Resources.RotationCertificate.Streaming

/-!
# Actual decoded-certificate fuel dispatch

One actual peek chooses the equality caller at EOF. A nonempty decoded word
enters the unchanged open fixed-width predecessor, then hands its actual returned
bits to the move-parser caller or its restored zero word to the rejection caller.
The complete certificate and all other caller stacks are preserved through that
handoff. The outer binary verifier still decodes the complete certificate first.
This component does not execute the remaining equality/parser/rotation phases.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.FuelDispatchMachine
open Resources.BinaryCounter

inductive DispatchLabel
  | inspectCertificate | atEnd
  deriving DecidableEq

instance : Fintype DispatchLabel where
  elems := {.inspectCertificate, .atEnd}
  complete label := by cases label <;> decide

inductive Exit
  | atEnd | positive | zero
  deriving DecidableEq

instance : Fintype Exit where
  elems := {.atEnd, .positive, .zero}
  complete exit := by cases exit <;> decide

abbrev Protected (K : Type) := Unit ⊕ K
abbrev ExtraLabel (Λ : Type) := DispatchLabel ⊕ Λ
abbrev Label (Λ : Type) := FixedWidthMachine.Label (ExtraLabel Λ)
abbrev Registers (R : Type) := FixedWidthMachine.Registers R

variable {K Λ R : Type} {Γ : K → Type}

abbrev protectedAlphabet (Γ : K → Type) : Protected K → Type
  | .inl _ => Tag
  | .inr k => Γ k

instance protectedAlphabetFintype [∀ k, Fintype (Γ k)] (k : Protected K) :
    Fintype (protectedAlphabet Γ k) := by
  cases k <;> exact inferInstance

abbrev Statement (Γ : K → Type) (Λ R : Type) :=
  FixedWidthMachine.Statement (protectedAlphabet Γ) (ExtraLabel Λ) R
abbrev Cfg (Γ : K → Type) (Λ R : Type) :=
  FixedWidthMachine.Cfg (protectedAlphabet Γ) (ExtraLabel Λ) R

def inspectLabel : Label Λ := FixedWidthMachine.callerLabel (.inl .inspectCertificate)
def atEndLabel : Label Λ := FixedWidthMachine.callerLabel (.inl .atEnd)
def positiveLabel : Label Λ := FixedWidthMachine.resultLabel .positive
def zeroLabel : Label Λ := FixedWidthMachine.resultLabel .zero
def callerLabel (label : Λ) : Label Λ := FixedWidthMachine.callerLabel (.inr label)

def exitLabel : Exit → Label Λ
  | .atEnd => atEndLabel
  | .positive => positiveLabel
  | .zero => zeroLabel

def exitOfResult : FixedWidthMachine.Result → Exit
  | .positive => .positive
  | .zero => .zero

theorem exitLabel_result (result : FixedWidthMachine.Result) :
    exitLabel (Λ := Λ) (exitOfResult result) = FixedWidthMachine.resultLabel result := by
  cases result <;> rfl

def storePresence (regs : Registers R) (tag : Option Tag) : Registers R :=
  (tag.map (fun _ => false), regs.2)

/-- A finite callback sees only the actual head's presence; it does not parse it. -/
def inspectBlock : Statement Γ Λ R :=
  .peek (.inr (.inl ())) storePresence (.branch (fun regs => regs.1.isSome)
    (FixedWidthMachine.jump (FixedWidthMachine.phaseLabel .borrow))
    (FixedWidthMachine.jump atEndLabel))

def callerHandler (caller : (Exit ⊕ Λ) → Statement Γ Λ R) :
    FixedWidthMachine.External (ExtraLabel Λ) → Statement Γ Λ R
  | .inl .positive => caller (.inl .positive)
  | .inl .zero => caller (.inl .zero)
  | .inr (.inl .inspectCertificate) => inspectBlock
  | .inr (.inl .atEnd) => caller (.inl .atEnd)
  | .inr (.inr label) => caller (.inr label)

/-- The predecessor is reused definitionally, with inspection as one caller label. -/
abbrev program (caller : (Exit ⊕ Λ) → Statement Γ Λ R) : Label Λ → Statement Γ Λ R :=
  FixedWidthMachine.program (callerHandler caller)

theorem program_eq_of_agrees (ambient : Label Λ → Statement Γ Λ R)
    (phases : ∀ phase, ambient (FixedWidthMachine.phaseLabel phase) = FixedWidthMachine.block phase)
    (inspect : ambient inspectLabel = inspectBlock) :
    ambient = program (fun label => match label with
      | .inl exit => ambient (exitLabel exit)
      | .inr label => ambient (callerLabel label)) := by
  funext label
  cases label with
  | inl phase => exact phases phase
  | inr external => cases external with
    | inl result => cases result <;> rfl
    | inr extra => cases extra with
      | inl label => cases label with
        | inspectCertificate => exact inspect
        | atEnd => rfl
      | inr label => rfl

def stores (cert : Word) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (protectedAlphabet Γ k)
  | .inl _ => cert
  | .inr k => ctx k

abbrev cfg (label : Option (Label Λ)) (regs : Registers R) (fuel : Bits)
    (borrowed : List Unit) (cert : Word) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  FixedWidthMachine.cfg label regs fuel borrowed (stores cert ctx)

variable [DecidableEq K]

abbrev step (caller : (Exit ⊕ Λ) → Statement Γ Λ R) : Cfg Γ Λ R → Option (Cfg Γ Λ R) :=
  FixedWidthMachine.step (callerHandler caller)

abbrev next (caller : (Exit ⊕ Λ) → Statement Γ Λ R) : Option (Cfg Γ Λ R) → Option (Cfg Γ Λ R) :=
  FixedWidthMachine.next (callerHandler caller)

variable (caller : (Exit ⊕ Λ) → Statement Γ Λ R)

theorem dispatch_step_nil (fuel : Bits) (borrowed : List Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some inspectLabel) regs fuel borrowed [] ctx) =
      some (cfg (some atEndLabel) (FixedWidthMachine.reset regs) fuel borrowed [] ctx) := by
  apply congrArg some
  apply FixedWidthMachine.cfg_ext <;> first | rfl | exact fun _ => rfl

theorem dispatch_step_cons (fuel : Bits) (borrowed : List Unit) (tag : Tag) (raw : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some inspectLabel) regs fuel borrowed (tag :: raw) ctx) =
      some (cfg (some (FixedWidthMachine.phaseLabel .borrow)) (FixedWidthMachine.reset regs)
        fuel borrowed (tag :: raw) ctx) := by
  apply congrArg some
  apply FixedWidthMachine.cfg_ext <;> first | rfl | exact fun _ => rfl

/-- Independent branch specification at the decoded-word boundary. -/
def dispatchSpec (fuel : Bits) : Word → Exit × Bits
  | [] => (.atEnd, fuel)
  | _ :: _ => (exitOfResult (FixedWidthMachine.predSpec fuel).1, (FixedWidthMachine.predSpec fuel).2)

/-- Proof-side transition count, absent from the finite statement body. -/
def dispatchSteps (fuel : Bits) : Word → Nat
  | [] => 1
  | _ :: _ => FixedWidthMachine.runSteps fuel + 1

theorem dispatch_run_nil (fuel : Bits) (borrowed : List Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[1] (some (cfg (some inspectLabel) regs fuel borrowed [] ctx)) =
      some (cfg (some atEndLabel) (FixedWidthMachine.reset regs) fuel borrowed [] ctx) := by
  exact dispatch_step_nil caller fuel borrowed regs ctx

/-- Existing borrowed tokens retain the same represented-prefix meaning as the core. -/
theorem dispatch_run_cons (fuel : Bits) (borrowed : List Unit) (tag : Tag) (raw : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[FixedWidthMachine.runSteps fuel + borrowed.length + 1]
        (some (cfg (some inspectLabel) regs fuel borrowed (tag :: raw) ctx)) =
      some (cfg
        (some (FixedWidthMachine.resultLabel
          (FixedWidthMachine.predSpec (List.replicate borrowed.length false ++ fuel)).1))
        (FixedWidthMachine.reset regs)
        (FixedWidthMachine.predSpec (List.replicate borrowed.length false ++ fuel)).2
        [] (tag :: raw) ctx) := by
  rw [FixedWidthMachine.iterate_step (callerHandler caller) _ _ _
    (dispatch_step_cons caller fuel borrowed tag raw regs ctx), FixedWidthMachine.borrow_iterate]
  rfl

theorem dispatch_run (fuel : Bits) (cert : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[dispatchSteps fuel cert]
        (some (cfg (some inspectLabel) regs fuel [] cert ctx)) =
      some (cfg (some (exitLabel (dispatchSpec fuel cert).1)) (FixedWidthMachine.reset regs)
        (dispatchSpec fuel cert).2 [] cert ctx) := by
  cases cert with
  | nil => exact dispatch_run_nil caller fuel [] regs ctx
  | cons tag raw =>
      simpa only [List.length_nil, Nat.add_zero, List.replicate_zero, List.nil_append,
        dispatchSteps, dispatchSpec, exitLabel_result] using
        dispatch_run_cons caller fuel [] tag raw regs ctx

theorem dispatch_run_first_true (zeros : Nat) (tail : Bits) (tag : Tag) (raw : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * zeros + 3]
        (some (cfg (some inspectLabel) regs (List.replicate zeros false ++ true :: tail)
          [] (tag :: raw) ctx)) =
      some (cfg (some positiveLabel) (FixedWidthMachine.reset regs)
        (List.replicate zeros true ++ false :: tail) [] (tag :: raw) ctx) := by
  have run := dispatch_run caller (List.replicate zeros false ++ true :: tail) (tag :: raw) regs ctx
  simpa only [dispatchSteps, dispatchSpec, FixedWidthMachine.runSteps_first_true,
    FixedWidthMachine.predSpec_first_true, exitOfResult, exitLabel, Nat.add_assoc] using run

theorem dispatch_run_replicate_false (width : Nat) (tag : Tag) (raw : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * width + 3]
        (some (cfg (some inspectLabel) regs (List.replicate width false) [] (tag :: raw) ctx)) =
      some (cfg (some zeroLabel) (FixedWidthMachine.reset regs)
        (List.replicate width false) [] (tag :: raw) ctx) := by
  have run := dispatch_run caller (List.replicate width false) (tag :: raw) regs ctx
  simpa only [dispatchSteps, dispatchSpec, FixedWidthMachine.runSteps_replicate_false,
    FixedWidthMachine.predSpec_replicate_false, exitOfResult, exitLabel, Nat.add_assoc] using run

theorem dispatch_run_of_some (fuel ys : Bits) (tag : Tag) (raw : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (returned : (decFixedRun fuel).1 = some ys) :
    (next caller)^[FixedWidthMachine.runSteps fuel + 1]
        (some (cfg (some inspectLabel) regs fuel [] (tag :: raw) ctx)) =
      some (cfg (some positiveLabel) (FixedWidthMachine.reset regs) ys [] (tag :: raw) ctx) := by
  simpa only [dispatchSteps, dispatchSpec, FixedWidthMachine.predSpec_of_some returned,
    exitOfResult, exitLabel] using dispatch_run caller fuel (tag :: raw) regs ctx

theorem dispatch_run_of_none (fuel : Bits) (tag : Tag) (raw : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (returned : (decFixedRun fuel).1 = none) :
    (next caller)^[FixedWidthMachine.runSteps fuel + 1]
        (some (cfg (some inspectLabel) regs fuel [] (tag :: raw) ctx)) =
      some (cfg (some zeroLabel) (FixedWidthMachine.reset regs) fuel [] (tag :: raw) ctx) := by
  simpa only [dispatchSteps, dispatchSpec, FixedWidthMachine.predSpec_of_none returned,
    exitOfResult, exitLabel] using dispatch_run caller fuel (tag :: raw) regs ctx

omit [DecidableEq K] in
theorem dispatchSteps_le (fuel : Bits) (cert : Word) :
    dispatchSteps fuel cert ≤ 2 * fuel.length + 3 := by
  have bound := FixedWidthMachine.runSteps_le fuel
  cases cert <;> simp only [dispatchSteps] <;> omega

omit [DecidableEq K] in
theorem dispatchSteps_le_source_cost (fuel : Bits) (tag : Tag) (raw : Word) :
    dispatchSteps fuel (tag :: raw) ≤ (decFixedRun fuel).2 + 1 := by
  exact Nat.add_le_add_right (FixedWidthMachine.runSteps_le_source_cost fuel) 1

def dispatchInTime (fuel : Bits) (cert : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some inspectLabel) regs fuel [] cert ctx)
      (some (cfg (some (exitLabel (dispatchSpec fuel cert).1)) (FixedWidthMachine.reset regs)
        (dispatchSpec fuel cert).2 [] cert ctx)) (dispatchSteps fuel cert) where
  steps := dispatchSteps fuel cert
  evals_in_steps := dispatch_run caller fuel cert regs ctx
  steps_le_m := Nat.le_refl _

def dispatchInLinearTime (fuel : Bits) (cert : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some inspectLabel) regs fuel [] cert ctx)
      (some (cfg (some (exitLabel (dispatchSpec fuel cert).1)) (FixedWidthMachine.reset regs)
        (dispatchSpec fuel cert).2 [] cert ctx)) (2 * fuel.length + 3) where
  steps := dispatchSteps fuel cert
  evals_in_steps := dispatch_run caller fuel cert regs ctx
  steps_le_m := dispatchSteps_le fuel cert

/-- The same returned fuel is bound into the existing source parser/executor continuation. -/
theorem checkStreamRun_of_fuel (fuel ys : Bits) (source target : BinaryTree Unit)
    (tag : Tag) (raw : Word) (returned : (decFixedRun fuel).1 = some ys) :
    let continued := bind (parseMoveRun (tag :: raw)) (fun parsed => match parsed with
      | none => (false, 1)
      | some (move, rest) => bind (applyMoveRun move source) (fun applied => match applied with
        | none => (false, 1)
        | some next => checkStreamRun ys next target rest))
    checkStreamRun fuel source target (tag :: raw) =
      (continued.1, 1 + (decFixedRun fuel).2 + continued.2) := by
  rw [checkStreamRun_cons]
  simp only [bind, returned, CallCount.tick]
  cases parsed : parseMoveRun (tag :: raw) with
  | mk result cost =>
      cases result with
      | none => simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      | some pair =>
          cases pair with
          | mk move rest =>
              simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              exact ⟨rfl, rfl⟩

theorem dispatch_zero_stream (fuel : Bits) (source target : BinaryTree Unit)
    (tag : Tag) (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (returned : (decFixedRun fuel).1 = none) :
    (next caller)^[FixedWidthMachine.runSteps fuel + 1]
        (some (cfg (some inspectLabel) regs fuel [] (tag :: raw) ctx)) =
      some (cfg (some zeroLabel) (FixedWidthMachine.reset regs) fuel [] (tag :: raw) ctx) ∧
    checkStreamRun fuel source target (tag :: raw) = (false, (decFixedRun fuel).2 + 2) :=
  ⟨dispatch_run_of_none caller fuel tag raw regs ctx returned,
    checkStreamRun_no_fuel fuel source target tag raw returned⟩

theorem dispatch_positive_stream (fuel ys : Bits) (source target : BinaryTree Unit)
    (tag : Tag) (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (returned : (decFixedRun fuel).1 = some ys) :
    let continued := bind (parseMoveRun (tag :: raw)) (fun parsed => match parsed with
      | none => (false, 1)
      | some (move, rest) => bind (applyMoveRun move source) (fun applied => match applied with
        | none => (false, 1)
        | some next => checkStreamRun ys next target rest))
    (next caller)^[FixedWidthMachine.runSteps fuel + 1]
        (some (cfg (some inspectLabel) regs fuel [] (tag :: raw) ctx)) =
      some (cfg (some positiveLabel) (FixedWidthMachine.reset regs) ys [] (tag :: raw) ctx) ∧
    checkStreamRun fuel source target (tag :: raw) =
      (continued.1, 1 + (decFixedRun fuel).2 + continued.2) :=
  ⟨dispatch_run_of_some caller fuel ys tag raw regs ctx returned,
    checkStreamRun_of_fuel fuel ys source target tag raw returned⟩

omit [DecidableEq K] in
theorem cfg_eta (c : Cfg Γ Λ R) :
    cfg c.l c.var (c.stk (.inl .fuel)) (c.stk (.inl .borrowed))
      (c.stk (.inr (.inl ()))) (fun k => c.stk (.inr (.inr k))) = c := by
  apply FixedWidthMachine.cfg_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · intro k
    cases k with
    | inl token => cases token; rfl
    | inr k => rfl

def Owned (label : Option (Label Λ)) : Prop :=
  FixedWidthMachine.Owned label ∨ label = some inspectLabel

def LocalStep (before after : Cfg Γ Λ R) : Prop := Owned before.l ∧ step caller before = some after

/-- Proof-only rank; no length or source evaluator is executed by inspection. -/
def remainingSteps (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inr (.inr (.inl .inspectCertificate))) =>
      match c.stk (.inr (.inl ())) with
      | [] => 1
      | _ :: _ => FixedWidthMachine.runSteps (c.stk (.inl .fuel)) +
          (c.stk (.inl .borrowed)).length + 1
  | _ => FixedWidthMachine.remainingSteps c

omit [DecidableEq K] in
theorem remainingSteps_core (c : Cfg Γ Λ R) (other : c.l ≠ some inspectLabel) :
    remainingSteps c = FixedWidthMachine.remainingSteps c := by
  cases labelEq : c.l with
  | none => simp only [remainingSteps, labelEq]
  | some label => cases label with
    | inl phase => simp only [remainingSteps, labelEq]
    | inr external => cases external with
      | inl result => simp only [remainingSteps, labelEq]
      | inr extra => cases extra with
        | inr label => simp only [remainingSteps, labelEq]
        | inl label => cases label with
          | atEnd => simp only [remainingSteps, labelEq]
          | inspectCertificate => exact False.elim (other labelEq)

omit [DecidableEq K] in
theorem remainingSteps_pos_iff (c : Cfg Γ Λ R) : 0 < remainingSteps c ↔ Owned c.l := by
  by_cases inspection : c.l = some inspectLabel
  · simp only [Owned, inspection, or_true, iff_true]
    cases certEq : c.stk (.inr (.inl ())) <;>
      simp [remainingSteps, inspection, inspectLabel, FixedWidthMachine.callerLabel, certEq]
  · rw [remainingSteps_core c inspection, FixedWidthMachine.remainingSteps_pos_iff]
    simp only [Owned, inspection, or_false]

omit [DecidableEq K] in
theorem core_owned_not_inspect {c : Cfg Γ Λ R} (owned : FixedWidthMachine.Owned c.l) :
    c.l ≠ some inspectLabel := by
  intro equal
  rw [equal] at owned
  exact owned

theorem core_step_not_inspect {before after : Cfg Γ Λ R}
    (transition : FixedWidthMachine.LocalStep (callerHandler caller) before after) :
    after.l ≠ some inspectLabel := by
  rcases transition with ⟨owned, executed⟩
  obtain ⟨phase, regs, fuel, borrowed, ctx, rfl⟩ := FixedWidthMachine.owned_cases before owned
  cases phase with
  | borrow =>
      cases fuel with
      | nil =>
          rw [FixedWidthMachine.borrow_step_nil] at executed
          cases Option.some.inj executed
          simp [FixedWidthMachine.cfg, FixedWidthMachine.phaseLabel, inspectLabel,
            FixedWidthMachine.callerLabel]
      | cons bit fuel => cases bit with
        | false =>
            rw [FixedWidthMachine.borrow_step_false] at executed
            cases Option.some.inj executed
            simp [FixedWidthMachine.cfg, FixedWidthMachine.phaseLabel, inspectLabel,
              FixedWidthMachine.callerLabel]
        | true =>
            rw [FixedWidthMachine.borrow_step_true] at executed
            cases Option.some.inj executed
            simp [FixedWidthMachine.cfg, FixedWidthMachine.phaseLabel, inspectLabel,
              FixedWidthMachine.callerLabel]
  | restoreTrue =>
      cases borrowed with
      | nil =>
          rw [FixedWidthMachine.restoreTrue_step_nil] at executed
          cases Option.some.inj executed
          simp [FixedWidthMachine.cfg, FixedWidthMachine.resultLabel, inspectLabel,
            FixedWidthMachine.callerLabel]
      | cons token borrowed =>
          cases token
          rw [FixedWidthMachine.restoreTrue_step_cons] at executed
          cases Option.some.inj executed
          simp [FixedWidthMachine.cfg, FixedWidthMachine.phaseLabel, inspectLabel,
            FixedWidthMachine.callerLabel]
  | restoreFalse =>
      cases borrowed with
      | nil =>
          rw [FixedWidthMachine.restoreFalse_step_nil] at executed
          cases Option.some.inj executed
          simp [FixedWidthMachine.cfg, FixedWidthMachine.resultLabel, inspectLabel,
            FixedWidthMachine.callerLabel]
      | cons token borrowed =>
          cases token
          rw [FixedWidthMachine.restoreFalse_step_cons] at executed
          cases Option.some.inj executed
          simp [FixedWidthMachine.cfg, FixedWidthMachine.phaseLabel, inspectLabel,
            FixedWidthMachine.callerLabel]

omit [DecidableEq K] in
theorem inspection_cases (c : Cfg Γ Λ R) (inspection : c.l = some inspectLabel) :
    ∃ regs fuel borrowed cert ctx, c = cfg (some inspectLabel) regs fuel borrowed cert ctx := by
  refine ⟨c.var, c.stk (.inl .fuel), c.stk (.inl .borrowed), c.stk (.inr (.inl ())),
    (fun k => c.stk (.inr (.inr k))), ?_⟩
  simpa only [inspection] using (cfg_eta c).symm

theorem local_step_remaining {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 := by
  rcases transition with ⟨owned, executed⟩
  rcases owned with core | inspection
  · rw [remainingSteps_core before (core_owned_not_inspect core),
      remainingSteps_core after (core_step_not_inspect caller ⟨core, executed⟩)]
    exact FixedWidthMachine.local_step_remaining (callerHandler caller) ⟨core, executed⟩
  · obtain ⟨regs, fuel, borrowed, cert, ctx, rfl⟩ := inspection_cases before inspection
    cases cert with
    | nil =>
        rw [dispatch_step_nil] at executed
        cases Option.some.inj executed
        rfl
    | cons tag raw =>
        rw [dispatch_step_cons] at executed
        cases Option.some.inj executed
        rfl

theorem local_step_register {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) : after.var.1 = none := by
  rcases transition with ⟨owned, executed⟩
  rcases owned with core | inspection
  · exact (FixedWidthMachine.local_step_data (callerHandler caller) ⟨core, executed⟩).2.1
  · obtain ⟨regs, fuel, borrowed, cert, ctx, rfl⟩ := inspection_cases before inspection
    cases cert with
    | nil =>
        rw [dispatch_step_nil] at executed
        cases Option.some.inj executed
        rfl
    | cons tag raw =>
        rw [dispatch_step_cons] at executed
        cases Option.some.inj executed
        rfl

theorem local_progress (before : Cfg Γ Λ R) (positive : 0 < remainingSteps before) :
    ∃ after, step caller before = some after ∧ remainingSteps before = remainingSteps after + 1 := by
  have owned := (remainingSteps_pos_iff before).mp positive
  cases labelEq : before.l with
  | none => simp [Owned, FixedWidthMachine.Owned, labelEq] at owned
  | some label =>
      have executed : step caller before =
          some (Turing.TM2.stepAux (program caller label) before.var before.stk) := by
        rcases before with ⟨control, regs, data⟩
        change control = some label at labelEq
        subst control
        rfl
      exact ⟨_, executed, local_step_remaining caller ⟨owned, executed⟩⟩

theorem step_caller_independent (other : (Exit ⊕ Λ) → Statement Γ Λ R)
    (c : Cfg Γ Λ R) (owned : Owned c.l) : step caller c = step other c := by
  rcases owned with core | inspection
  · exact FixedWidthMachine.step_caller_independent (callerHandler caller) (callerHandler other) c core
  · obtain ⟨regs, fuel, borrowed, cert, ctx, rfl⟩ := inspection_cases c inspection
    rfl

variable [Fintype K]

abbrev stackCells (c : Cfg Γ Λ R) : Nat := FixedWidthMachine.stackCells c

theorem local_step_preserves {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    after.var.2 = before.var.2 ∧
      after.stk (.inr (.inl ())) = before.stk (.inr (.inl ())) ∧
      (∀ k, after.stk (.inr (.inr k)) = before.stk (.inr (.inr k))) ∧
      stackCells after = stackCells before := by
  rcases transition with ⟨owned, executed⟩
  rcases owned with core | inspection
  · obtain ⟨registers, frame, cells⟩ :=
      FixedWidthMachine.local_step_preserves (callerHandler caller) ⟨core, executed⟩
    exact ⟨registers, frame (.inl ()), fun k => frame (.inr k), cells⟩
  · obtain ⟨regs, fuel, borrowed, cert, ctx, rfl⟩ := inspection_cases before inspection
    cases cert with
    | nil =>
        rw [dispatch_step_nil] at executed
        cases Option.some.inj executed
        exact ⟨rfl, rfl, fun _ => rfl, rfl⟩
    | cons tag raw =>
        rw [dispatch_step_cons] at executed
        cases Option.some.inj executed
        exact ⟨rfl, rfl, fun _ => rfl, rfl⟩

theorem local_reaches_preserves {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2 = start.var.2 ∧
      reached.stk (.inr (.inl ())) = start.stk (.inr (.inl ())) ∧
      (∀ k, reached.stk (.inr (.inr k)) = start.stk (.inr (.inr k))) ∧
      stackCells reached = stackCells start := by
  induction path with
  | refl => exact ⟨rfl, rfl, fun _ => rfl, rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨registers, cert, frame, cells⟩ := local_step_preserves caller transition
      exact ⟨registers.trans ih.1, cert.trans ih.2.1,
        fun k => (frame k).trans (ih.2.2.1 k), cells.trans ih.2.2.2⟩

omit [Fintype K] in
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
      have canonical := local_step_register caller ⟨owned, first⟩
      rw [Function.iterate_succ_apply] at executed
      change (next caller)^[n] (step caller start) = some reached at executed
      rw [first] at executed
      by_cases empty : n = 0
      · subst n
        have equal : middle = reached := Option.some.inj executed
        simpa only [equal] using canonical
      · exact ih middle reached (by omega) executed (by omega)

omit [DecidableEq K] [Fintype K] in
theorem remainingSteps_inspect (fuel : Bits) (cert : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (inspectLabel (Λ := Λ))) regs fuel [] cert ctx) =
      dispatchSteps fuel cert := by
  cases cert <;> rfl

omit [Fintype K] in
/-- Every actual prefix through the first handoff; later caller execution is excluded. -/
theorem dispatch_prefix (fuel : Bits) (cert : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ dispatchSteps fuel cert) :
    ∃ reached,
      (next caller)^[n] (some (cfg (some inspectLabel) regs fuel [] cert ctx)) = some reached ∧
      remainingSteps reached = dispatchSteps fuel cert - n ∧
      Relation.ReflTransGen (LocalStep caller) (cfg (some inspectLabel) regs fuel [] cert ctx) reached ∧
      (n < dispatchSteps fuel cert ↔ Owned reached.l) ∧
      (0 < n → reached.var.1 = none) := by
  have initialBound : n ≤ remainingSteps
      (cfg (some (inspectLabel (Λ := Λ))) regs fuel [] cert ctx) := by
    rwa [remainingSteps_inspect]
  obtain ⟨reached, executed, rank, path⟩ := FixedWidthMachine.ranked_prefix (step caller)
    remainingSteps (local_progress caller) n (cfg (some inspectLabel) regs fuel [] cert ctx) initialBound
  rw [remainingSteps_inspect] at rank
  refine ⟨reached, executed, rank, ?_, ?_, ?_⟩
  · exact Relation.ReflTransGen.mono
      (fun before _ h => ⟨(remainingSteps_pos_iff before).mp h.1, h.2⟩) _ _ path
  · rw [← remainingSteps_pos_iff, rank]
    omega
  · exact prefix_local_register caller n (cfg (some inspectLabel) regs fuel [] cert ctx)
      reached initialBound executed

omit [Fintype K] in
theorem dispatch_prefix_caller_independent (other : (Exit ⊕ Λ) → Statement Γ Λ R)
    (fuel : Bits) (cert : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ dispatchSteps fuel cert) :
    (next caller)^[n] (some (cfg (some inspectLabel) regs fuel [] cert ctx)) =
      (next other)^[n] (some (cfg (some inspectLabel) regs fuel [] cert ctx)) := by
  apply FixedWidthMachine.ranked_prefix_eq (step caller) (step other) remainingSteps
    (local_progress caller)
    (fun c positive => step_caller_independent caller other c ((remainingSteps_pos_iff c).mp positive))
  rwa [remainingSteps_inspect]

end Resources.RotationCertificate.FuelDispatchMachine
