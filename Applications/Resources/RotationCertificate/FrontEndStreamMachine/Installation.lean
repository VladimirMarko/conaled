import Applications.Resources.RotationCertificate.FrontEndStreamMachine.Package

/-!
# FrontEndStreamMachine: Installation
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.FrontEndStreamMachine

variable {K Λ R : Type} {Γ : K → Type}

section FurtherInstallation

variable {K' Λ' R' : Type} {Γ' : K' → Type}
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')

def installedCfg (c : Cfg Γ Λ R) : Turing.TM2.Cfg Γ' Λ' R' :=
  FrontEndMachine.Transport.cfg names symbols registers labels c

theorem installedCfg_injective :
    Function.Injective (installedCfg names symbols registers labels) :=
  FrontEndMachine.Transport.cfg_injective names symbols registers labels labels.injective

/-- The inverse recovers the entire dependent stack family and every caller
register/label component, including live halt-labelled configurations. -/
def installedCfgEquiv : Cfg Γ Λ R ≃ Turing.TM2.Cfg Γ' Λ' R' where
  toFun := installedCfg names symbols registers labels
  invFun c :=
    { l := c.l.map labels.symm
      var := registers.symm c.var
      stk := (FrontEndMachine.Transport.stackEquiv names symbols).symm c.stk }
  left_inv c := by
    rcases c with ⟨label, regs, data⟩
    cases label <;> simp [installedCfg, FrontEndMachine.Transport.cfg]
  right_inv c := by
    rcases c with ⟨label, regs, data⟩
    cases label <;> simp [installedCfg, FrontEndMachine.Transport.cfg]

@[simp] theorem installedCfgEquiv_apply (c : Cfg Γ Λ R) :
    installedCfgEquiv names symbols registers labels c =
      installedCfg names symbols registers labels c := rfl

theorem installedCfg_label (c : Cfg Γ Λ R) :
    (installedCfg names symbols registers labels c).l = c.l.map labels := rfl

theorem installedCfg_registers (c : Cfg Γ Λ R) :
    (installedCfg names symbols registers labels c).var = registers c.var := rfl

theorem installedCfg_stack (c : Cfg Γ Λ R) (k : StackId K) :
    (installedCfg names symbols registers labels c).stk (names k) =
      (c.stk k).map (symbols k) :=
  FrontEndMachine.Transport.stackEquiv_apply names symbols c.stk k

theorem installedCfg_registers_readback (c : Cfg Γ Λ R) :
    registers.symm (installedCfg names symbols registers labels c).var = c.var :=
  registers.symm_apply_apply c.var

theorem installedCfg_readback (c : Cfg Γ Λ R) :
    (installedCfgEquiv names symbols registers labels).symm
      (installedCfg names symbols registers labels c) = c :=
  (installedCfgEquiv names symbols registers labels).symm_apply_apply c

def installedOwned (label : Option Λ') : Prop := Owned (label.map labels.symm)

@[simp] theorem installedCfg_owned_iff (c : Cfg Γ Λ R) :
    installedOwned labels (installedCfg names symbols registers labels c).l ↔ Owned c.l := by
  cases label : c.l <;>
    simp [installedOwned, installedCfg, FrontEndMachine.Transport.cfg, label]

theorem installedCfg_stack_readback (c : Cfg Γ Λ R) (k : StackId K) :
    ((installedCfg names symbols registers labels c).stk (names k)).map
      (symbols k).symm = c.stk k := by
  rw [installedCfg_stack]
  simp

theorem installed_stack_cells [Fintype K] [Fintype K'] (c : Cfg Γ Λ R) :
    ∑ k, ((installedCfg names symbols registers labels c).stk k).length =
      ∑ k, (c.stk k).length :=
  FrontEndMachine.Transport.stackEquiv_total_length names symbols c.stk

variable [DecidableEq K] [DecidableEq K']
variable (caller : Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')

theorem installed_owned_step
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (owned : Owned start.l) :
    Turing.TM2.step ambient (installedCfg names symbols registers labels start) =
      (step caller start).map (installedCfg names symbols registers labels) :=
  FrontEndMachine.Transport.step_owned names symbols registers labels
    (program caller) ambient Owned installed start owned

/-- This transport uses the supplied actual owned prefix; later caller bodies
are unconstrained. Canonical rank-bounded specializations are proved separately. -/
theorem installed_prefix_of_owned
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (n : Nat) (start : Cfg Γ Λ R)
    (earlier : ∀ j, j < n → ∃ reached,
      (next caller)^[j] (some start) = some reached ∧ Owned reached.l) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) :=
  FrontEndMachine.Transport.iterate_owned names symbols registers labels
    (program caller) ambient Owned installed n start earlier

/-- A supplied actual owned run transports with the same activation count.
No condition is imposed on external caller bodies. -/
theorem installed_localRun
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    {n : Nat} {start finish : Cfg Γ Λ R} (run : LocalRun caller n start finish) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      some (installedCfg names symbols registers labels finish) := by
  rw [installed_prefix_of_owned names symbols registers labels caller ambient installed n start
    (fun j strict => LocalRun.owned_prefix caller run j strict)]
  rw [LocalRun.iterate caller run]
  rfl

theorem installed_localRun_owned_prefix
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    {n : Nat} {start finish : Cfg Γ Λ R} (run : LocalRun caller n start finish)
    (j : Nat) (strict : j < n) :
    ∃ reached, (FrontEndMachine.Transport.next ambient)^[j]
      (some (installedCfg names symbols registers labels start)) = some reached ∧
      installedOwned labels reached.l := by
  obtain ⟨reached, executed, owned⟩ := LocalRun.owned_prefix caller run j strict
  refine ⟨installedCfg names symbols registers labels reached, ?_, ?_⟩
  · rw [installed_prefix_of_owned names symbols registers labels caller ambient installed j start
      (fun k earlier => LocalRun.owned_prefix caller run k (Nat.lt_trans earlier strict))]
    rw [executed]
    rfl
  · exact (installedCfg_owned_iff names symbols registers labels reached).2 owned

/-- Arbitrary iterations, including arbitrary external caller behaviour, require
literal agreement on every label of the complete carrier. -/
theorem installed_iterate
    (installed : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (n : Nat) (start : Option (Cfg Γ Λ R)) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (start.map (installedCfg names symbols registers labels)) =
      ((next caller)^[n] start).map (installedCfg names symbols registers labels) :=
  FrontEndMachine.Transport.iterate names symbols registers labels
    (program caller) ambient installed n start

def installedTimed
    (installed : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (final : Option (Cfg Γ Λ R)) (bound : Nat)
    (run : StateTransition.EvalsToInTime (step caller) start final bound) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start)
      (final.map (installedCfg names symbols registers labels)) bound :=
  FrontEndMachine.Transport.timed names symbols registers labels
    (program caller) ambient installed start final bound run

@[simp] theorem installedTimed_steps
    (installed : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (final : Option (Cfg Γ Λ R)) (bound : Nat)
    (run : StateTransition.EvalsToInTime (step caller) start final bound) :
    (installedTimed names symbols registers labels caller ambient installed start final bound run).steps =
      run.steps := rfl

end FurtherInstallation

end Resources.RotationCertificate.FrontEndStreamMachine

namespace Resources.RotationCertificate.FrontEndStreamMachine

open Resources.BinaryCounter (Bits)

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R)

theorem init_first_halt (initial : R) (raw : Bits) :
    FirstHalt caller (Turing.initList (machine caller initial) raw) (runSteps raw)
      (Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw]) := by
  have startEq : (Turing.initList (machine caller initial) raw : Cfg Γ Λ R) =
      entry (initialRegisters initial) raw (fun _ => []) :=
    machine_initList_eq caller initial raw
  have finishEq :
      (Turing.haltList (machine caller initial) ([BitPairFraming.verifyFramed raw] : Bits) : Cfg Γ Λ R) =
      cfg none (fullReset (initialRegisters initial)) { fuel := [BitPairFraming.verifyFramed raw] }
        (fun _ => []) :=
    (machine_haltList_eq caller initial ([BitPairFraming.verifyFramed raw] : Bits)).trans
      (congrArg (fun fields : Registers R => cfg (Γ := Γ) (Λ := Λ) none fields
        { fuel := [BitPairFraming.verifyFramed raw] } (fun _ => []))
        (fullReset_initialRegisters initial).symm)
  exact (congrArg₂ (fun start finish : Cfg Γ Λ R =>
    FirstHalt caller start (runSteps raw) finish) startEq finishEq).mpr
      (run_verifyFramed caller (initialRegisters initial) raw (fun _ => []))

theorem init_first_halt_iff (initial : R) (raw : Bits) (n : Nat) (finish : Cfg Γ Λ R) :
    FirstHalt caller (Turing.initList (machine caller initial) raw) n finish ↔
      n = runSteps raw ∧
      finish = Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw] := by
  have startEq : (Turing.initList (machine caller initial) raw : Cfg Γ Λ R) =
      entry (initialRegisters initial) raw (fun _ => []) :=
    machine_initList_eq caller initial raw
  have finishEq :
      (Turing.haltList (machine caller initial) ([BitPairFraming.verifyFramed raw] : Bits) : Cfg Γ Λ R) =
      cfg none (fullReset (initialRegisters initial)) { fuel := [BitPairFraming.verifyFramed raw] }
        (fun _ => []) :=
    (machine_haltList_eq caller initial ([BitPairFraming.verifyFramed raw] : Bits)).trans
      (congrArg (fun fields : Registers R => cfg (Γ := Γ) (Λ := Λ) none fields
        { fuel := [BitPairFraming.verifyFramed raw] } (fun _ => []))
        (fullReset_initialRegisters initial).symm)
  exact (congrArg₂ (fun start result : Cfg Γ Λ R =>
    (FirstHalt caller start n finish ↔ n = runSteps raw ∧ finish = result)) startEq finishEq).mpr
      (run_first_halt_iff caller (initialRegisters initial) raw (fun _ => []) n finish)

theorem init_iterate (initial : R) (raw : Bits) :
    (fun c : Option (machine caller initial).Cfg => c.bind (machine caller initial).step)^[runSteps raw]
      (some (Turing.initList (machine caller initial) raw)) =
      some (Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw]) :=
  (init_first_halt caller initial raw).1

theorem init_outer_none (initial : R) (raw : Bits) :
    (fun c : Option (machine caller initial).Cfg => c.bind (machine caller initial).step)^[runSteps raw + 1]
      (some (Turing.initList (machine caller initial) raw)) = none := by
  rw [machine_initList_eq]
  exact run_outer_none caller (initialRegisters initial) raw (fun _ => [])

theorem init_after_halt (initial : R) (raw : Bits) (n : Nat) (strict : runSteps raw < n) :
    (fun c : Option (machine caller initial).Cfg => c.bind (machine caller initial).step)^[n]
      (some (Turing.initList (machine caller initial) raw)) = none := by
  rw [machine_initList_eq]
  exact run_after_halt caller (initialRegisters initial) raw (fun _ => []) n strict

theorem init_earlier_owned (initial : R) (raw : Bits) (n : Nat) (strict : n < runSteps raw) :
    ∃ reached,
      (fun c : Option (machine caller initial).Cfg => c.bind (machine caller initial).step)^[n]
        (some (Turing.initList (machine caller initial) raw)) = some reached ∧ Owned reached.l :=
  (init_first_halt caller initial raw).2.2 n strict

def initOutputsInTimeExact (initial : R) (raw : Bits) :
    Turing.TM2OutputsInTime (machine caller initial) raw
      (some [BitPairFraming.verifyFramed raw]) (runSteps raw) where
  steps := runSteps raw
  evals_in_steps := init_iterate caller initial raw
  steps_le_m := Nat.le_refl _

def initOutputsInTimePolynomial (initial : R) (raw : Bits) :
    Turing.TM2OutputsInTime (machine caller initial) raw
      (some [BitPairFraming.verifyFramed raw]) (raw.length * raw.length + 10 * raw.length + 36) where
  steps := runSteps raw
  evals_in_steps := init_iterate caller initial raw
  steps_le_m := runSteps_le raw

@[simp] theorem initOutputsInTimeExact_steps (initial : R) (raw : Bits) :
    (initOutputsInTimeExact caller initial raw).steps = runSteps raw := rfl

@[simp] theorem initOutputsInTimePolynomial_steps (initial : R) (raw : Bits) :
    (initOutputsInTimePolynomial caller initial raw).steps = runSteps raw := rfl

def initOutputs (initial : R) (raw : Bits) :
    Turing.TM2Outputs (machine caller initial) raw (some [BitPairFraming.verifyFramed raw]) :=
  (initOutputsInTimeExact caller initial raw).toTM2Outputs

def initNoneInTime (initial : R) (raw : Bits) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw) none (runSteps raw + 1) where
  steps := runSteps raw + 1
  evals_in_steps := init_outer_none caller initial raw
  steps_le_m := Nat.le_refl _

@[simp] theorem initNoneInTime_steps (initial : R) (raw : Bits) :
    (initNoneInTime caller initial raw).steps = runSteps raw + 1 := rfl

theorem init_peak (initial : R) (raw : Bits) :
    ExactPeak caller (Turing.initList (machine caller initial) raw)
      (runSteps raw) (max raw.length 1) := by
  have startEq : (Turing.initList (machine caller initial) raw : Cfg Γ Λ R) =
      entry (initialRegisters initial) raw (fun _ => []) :=
    machine_initList_eq caller initial raw
  have actual : ExactPeak caller (entry (initialRegisters initial) raw (fun _ => []))
      (runSteps raw) (max raw.length 1) := by
    simpa only [contextCells, List.length_nil, Finset.sum_const_zero, Nat.add_zero] using
      run_peak caller (initialRegisters initial) raw (fun _ => [])
  exact (congrArg (fun start : Cfg Γ Λ R =>
    ExactPeak caller start (runSteps raw) (max raw.length 1)) startEq).mpr actual

theorem init_prefix (initial : R) (raw : Bits) (n : Nat) (bound : n ≤ runSteps raw) :
    ∃ reached,
      (fun c : Option (machine caller initial).Cfg => c.bind (machine caller initial).step)^[n]
        (some (Turing.initList (machine caller initial) raw)) = some reached ∧
      remainingSteps reached = runSteps raw - n ∧
      Relation.ReflTransGen (LocalStep caller) (Turing.initList (machine caller initial) raw) reached ∧
      (n < runSteps raw ↔ Owned reached.l) ∧
      (n = 0 → reached = Turing.initList (machine caller initial) raw) ∧
      reached.var = registersAt (Turing.initList (machine caller initial) raw) n ∧
      user reached.var = initial ∧
      (∀ k, reached.stk (.inr (.inr k)) = []) ∧
      finalCfg reached = Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw] ∧
      stackCells reached ≤ max raw.length 1 ∧
      runSteps raw ≤ raw.length * raw.length + 10 * raw.length + 36 := by
  have startEq : (Turing.initList (machine caller initial) raw : Cfg Γ Λ R) =
      entry (initialRegisters initial) raw (fun _ => []) :=
    machine_initList_eq caller initial raw
  have finishEq : runResult (Λ := Λ) (initialRegisters initial) raw (fun _ => []) =
      (Turing.haltList (machine caller initial) ([BitPairFraming.verifyFramed raw] : Bits) : Cfg Γ Λ R) :=
    (runResult_eq (initialRegisters initial) raw (fun _ => [])).trans
      ((congrArg (fun fields : Registers R => cfg (Γ := Γ) (Λ := Λ) none fields
        { fuel := [BitPairFraming.verifyFramed raw] } (fun _ => []))
        (fullReset_initialRegisters initial)).trans
          (machine_haltList_eq caller initial ([BitPairFraming.verifyFramed raw] : Bits)).symm)
  obtain ⟨reached, executed, rank, path, ownership, zero, fields, retained, frame, final, cells, time⟩ :=
    run_owned_prefix caller (initialRegisters initial) raw (fun _ => []) n bound
  refine ⟨reached, ?_, rank, ?_, ownership, ?_, ?_, ?_, frame, final.trans finishEq, ?_, time⟩
  · exact (congrArg (fun start : Cfg Γ Λ R =>
      (next caller)^[n] (some start) = some reached) startEq).mpr executed
  · exact (congrArg (fun start : Cfg Γ Λ R =>
      Relation.ReflTransGen (LocalStep caller) start reached) startEq).mpr path
  · intro isZero
    exact (zero isZero).trans startEq.symm
  · exact fields.trans (congrArg (fun start : Cfg Γ Λ R => registersAt start n) startEq).symm
  · exact retained.trans (user_initialRegisters initial)
  · simpa only [contextCells, List.length_nil, Finset.sum_const_zero, Nat.add_zero] using cells

def machineCfgInTime (initial : R) (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (machine caller initial).step start
      (some (finalCfg start)) (remainingSteps start) := cfgInTime caller start

@[simp] theorem machineCfgInTime_steps (initial : R) (start : Cfg Γ Λ R) :
    (machineCfgInTime caller initial start).steps = remainingSteps start := rfl

def machinePhaseInTime (initial : R) (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (cfg (some (phaseLabel q)) regs D ctx) (some (phaseResult q regs D ctx)) (phaseSteps q D) :=
  phaseInTime caller q D regs ctx

@[simp] theorem machinePhaseInTime_steps (initial : R) (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (machinePhaseInTime caller initial q D regs ctx).steps = phaseSteps q D := rfl

end Resources.RotationCertificate.FrontEndStreamMachine

namespace Resources.RotationCertificate.FrontEndStreamMachine

variable {K Λ R : Type} {Γ : K → Type}
variable {K' Λ' R' : Type} {Γ' : K' → Type}
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable [DecidableEq K] [DecidableEq K']
variable (caller : Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
variable (installed : ∀ label, Owned (some label) →
  ambient (labels label) =
    FrontEndMachine.Transport.statement names symbols registers labels (program caller label))

include installed in
theorem installed_owned_prefix (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) :=
  installed_prefix_of_owned names symbols registers labels caller ambient installed n start
    (fun j strict => (cfg_localRun caller start).owned_prefix caller j (Nat.lt_of_lt_of_le strict bound))

include installed in
theorem installed_cfg_iterate (start : Cfg Γ Λ R) :
    (FrontEndMachine.Transport.next ambient)^[remainingSteps start]
      (some (installedCfg names symbols registers labels start)) =
      some (installedCfg names symbols registers labels (finalCfg start)) :=
  installed_localRun names symbols registers labels caller ambient installed (cfg_localRun caller start)

include installed in
theorem installed_halt_then_none (start : Cfg Γ Λ R) (halted : (finalCfg start).l = none) :
    (FrontEndMachine.Transport.next ambient)^[remainingSteps start + 1]
      (some (installedCfg names symbols registers labels start)) = none := by
  rw [Function.iterate_succ_apply', installed_cfg_iterate names symbols registers labels caller ambient installed]
  simp only [FrontEndMachine.Transport.next, Option.bind_some, Turing.TM2.step,
    installedCfg, FrontEndMachine.Transport.cfg, halted, Option.map_none]

include installed in
theorem installed_after_halt (start : Cfg Γ Λ R) (halted : (finalCfg start).l = none)
    (n : Nat) (strict : remainingSteps start < n) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = none := by
  have count : n = (n - (remainingSteps start + 1)) + (remainingSteps start + 1) := by omega
  rw [count, Function.iterate_add_apply,
    installed_halt_then_none names symbols registers labels caller ambient installed start halted]
  have noneIter (j : Nat) :
      (FrontEndMachine.Transport.next ambient)^[j] (none : Option (Turing.TM2.Cfg Γ' Λ' R')) = none := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih]; rfl
  exact noneIter _

include installed in
/-- An owned start never enters a caller body: its complete run reaches live
halt, then outer none. Agreement on the ninety-six owned bodies suffices at
every natural time, including times after that halt. -/
theorem installed_iterate_owned_start (start : Cfg Γ Λ R) (owned : Owned start.l) (n : Nat) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) := by
  by_cases early : n ≤ remainingSteps start
  · exact installed_owned_prefix names symbols registers labels caller ambient installed start n early
  · have halted := finalCfg_halted_of_owned start owned
    rw [installed_after_halt names symbols registers labels caller ambient installed start halted n (by omega),
      cfg_after_halt caller start halted n (by omega), Option.map_none]

include installed in
theorem installed_first_halt (start : Cfg Γ Λ R) (owned : Owned start.l) :
    (FrontEndMachine.Transport.next ambient)^[remainingSteps start]
      (some (installedCfg names symbols registers labels start)) =
      some (installedCfg names symbols registers labels (finalCfg start)) ∧
    (installedCfg names symbols registers labels (finalCfg start)).l = none ∧
    ∀ j, j < remainingSteps start → ∃ reached,
      (FrontEndMachine.Transport.next ambient)^[j]
        (some (installedCfg names symbols registers labels start)) = some reached ∧
      installedOwned labels reached.l := by
  refine ⟨installed_cfg_iterate names symbols registers labels caller ambient installed start, ?_, ?_⟩
  · rw [installedCfg_label, finalCfg_halted_of_owned start owned]
    rfl
  · exact installed_localRun_owned_prefix names symbols registers labels caller ambient installed
      (cfg_localRun caller start)

include installed in
theorem installed_first_halt_iff (start : Cfg Γ Λ R) (owned : Owned start.l)
    (n : Nat) (finish : Turing.TM2.Cfg Γ' Λ' R') :
    ((FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) = some finish ∧
      finish.l = none ∧
      ∀ j, j < n → ∃ reached,
        (FrontEndMachine.Transport.next ambient)^[j]
          (some (installedCfg names symbols registers labels start)) = some reached ∧
        installedOwned labels reached.l) ↔
      n = remainingSteps start ∧ finish = installedCfg names symbols registers labels (finalCfg start) := by
  constructor
  · rintro ⟨executed, halted, _⟩
    have bound : n ≤ remainingSteps start := by
      by_contra later
      have gone := installed_after_halt names symbols registers labels caller ambient installed start
        (finalCfg_halted_of_owned start owned) n (by omega)
      rw [gone] at executed
      cases executed
    have exactTime : n = remainingSteps start := by
      by_contra notLast
      obtain ⟨middle, before, middleOwned⟩ :=
        installed_localRun_owned_prefix names symbols registers labels caller ambient installed
          (cfg_localRun caller start) n (by omega)
      have same : middle = finish := Option.some.inj (before.symm.trans executed)
      subst middle
      simp only [installedOwned, halted, Option.map_none, Owned] at middleOwned
    subst n
    have endpoint := installed_cfg_iterate names symbols registers labels caller ambient installed start
    exact ⟨rfl, (Option.some.inj (endpoint.symm.trans executed)).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact installed_first_halt names symbols registers labels caller ambient installed start owned

include installed in
theorem installed_owned_prefix_frame (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      (FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) =
        some (installedCfg names symbols registers labels reached) ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ installedOwned labels (installedCfg names symbols registers labels reached).l) ∧
      (n = 0 → reached = start) ∧
      (installedCfg names symbols registers labels reached).var = registers (registersAt start n) ∧
      user reached.var = user start.var ∧
      (∀ k, (installedCfg names symbols registers labels reached).stk (names (.inr (.inr k))) =
        (start.stk (.inr (.inr k))).map (symbols (.inr (.inr k)))) ∧
      finalCfg reached = finalCfg start := by
  obtain ⟨reached, executed, rank, path, ownership, zero, reset, retained, frame, final⟩ :=
    owned_prefix_frame caller start n bound
  refine ⟨reached, executed, ?_, rank, path, ?_, zero, ?_, retained, ?_, final⟩
  · rw [installed_owned_prefix names symbols registers labels caller ambient installed start n bound, executed]
    rfl
  · simpa only [installedCfg_owned_iff] using ownership
  · rw [installedCfg_registers, reset]
  · intro k
    rw [installedCfg_stack, frame k]

include installed in
def installedOwnedInTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start)
      (some (installedCfg names symbols registers labels (finalCfg start))) (remainingSteps start) where
  steps := remainingSteps start
  evals_in_steps := installed_cfg_iterate names symbols registers labels caller ambient installed start
  steps_le_m := Nat.le_refl _

@[simp] theorem installedOwnedInTime_steps (start : Cfg Γ Λ R) :
    (installedOwnedInTime names symbols registers labels caller ambient installed start).steps =
      remainingSteps start := rfl

include installed in
def installedPhaseInTime (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels (cfg (some (phaseLabel q)) regs D ctx))
      (some (installedCfg names symbols registers labels (phaseResult q regs D ctx))) (phaseSteps q D) where
  steps := phaseSteps q D
  evals_in_steps := installed_localRun names symbols registers labels caller ambient installed
    (phase_localRun caller q D regs ctx)
  steps_le_m := Nat.le_refl _

@[simp] theorem installedPhaseInTime_steps (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (installedPhaseInTime names symbols registers labels caller ambient installed q D regs ctx).steps =
      phaseSteps q D := rfl

include installed in
def installedHaltNoneInTime (start : Cfg Γ Λ R) (halted : (finalCfg start).l = none) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start) none (remainingSteps start + 1) where
  steps := remainingSteps start + 1
  evals_in_steps := installed_halt_then_none names symbols registers labels caller ambient installed start halted
  steps_le_m := Nat.le_refl _

@[simp] theorem installedHaltNoneInTime_steps (start : Cfg Γ Λ R) (halted : (finalCfg start).l = none) :
    (installedHaltNoneInTime names symbols registers labels caller ambient installed start halted).steps =
      remainingSteps start + 1 := rfl

section PhysicalSpace
variable [Fintype K] [Fintype K']

include installed in
theorem installed_owned_prefix_space (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      (FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) =
        some (installedCfg names symbols registers labels reached) ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ installedOwned labels (installedCfg names symbols registers labels reached).l) ∧
      (n = 0 → reached = start) ∧
      (installedCfg names symbols registers labels reached).var = registers (registersAt start n) ∧
      user reached.var = user start.var ∧
      (∀ k, (installedCfg names symbols registers labels reached).stk (names (.inr (.inr k))) =
        (start.stk (.inr (.inr k))).map (symbols (.inr (.inr k)))) ∧
      finalCfg reached = finalCfg start ∧
      (∑ k, ((installedCfg names symbols registers labels reached).stk k).length) ≤ allowance start := by
  obtain ⟨reached, executed, ambientRun, rank, path, ownership, zero, reset, retained, frame, final⟩ :=
    installed_owned_prefix_frame names symbols registers labels caller ambient installed start n bound
  refine ⟨reached, executed, ambientRun, rank, path, ownership, zero, reset, retained, frame, final, ?_⟩
  rw [installed_stack_cells]
  exact prefix_stackCells_le_dirty caller start n bound reached executed

end PhysicalSpace

end Resources.RotationCertificate.FrontEndStreamMachine
