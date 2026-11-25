import Applications.Resources.RotationCertificate.StreamMachine.Package

/-!
# StreamMachine: InitialExecution
-/

set_option autoImplicit false
set_option warningAsError true


-- BEGIN PACKAGE EXECUTION PASSED3
namespace Resources.RotationCertificate.StreamMachine

variable {K Λ R : Type} {Γ : K → Type}

/-! ## The literal certificate-only initializer outcome

The four-step outcome is a live Boolean label. The input certificate remains
physical data, and the designated output/fuel word remains empty.
-/

theorem init_evaluate (raw : Word) :
    evaluate inspectPhase { certificate := raw } =
      ⟨raw.isEmpty, { certificate := raw }, 4⟩ := by
  cases raw with
  | nil =>
      rw [evaluate_inspect, evaluateInspect_nil _ rfl]
      rfl
  | cons tag raw =>
      rw [evaluate_inspect, evaluateInspect_nonempty _ (by simp)]
      rfl

theorem initClock_eq (raw : Word) : phaseSteps inspectPhase { certificate := raw } = 4 := by
  exact congrArg Evaluation.steps (init_evaluate raw)

theorem initResult_eq (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) inspectPhase regs { certificate := raw } ctx =
      cfg (some (resultLabel raw.isEmpty)) (resetAll regs) { certificate := raw } ctx := by
  simp only [phaseResult, init_evaluate, evaluationCfg]

variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem init_input_firstRun (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstRun caller (cfg (some (phaseLabel inspectPhase)) regs { certificate := raw } ctx)
      4 (cfg (some (resultLabel raw.isEmpty)) (resetAll regs) { certificate := raw } ctx) := by
  have actual := phase_firstRun caller inspectPhase { certificate := raw } regs ctx
  rw [initClock_eq, initResult_eq] at actual
  exact actual

section StreamPackageExecution

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

/-- The predicate uses the actual package step on the supplied installed cfg. -/
def machineFirstRun (initial : R) (start : Cfg Γ Λ R) (n : Nat) (finish : Cfg Γ Λ R) : Prop :=
  (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
      (some start) = some finish ∧
    ¬ Owned finish.l ∧
    ∀ j, j < n → ∃ reached,
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[j]
        (some start) = some reached ∧ Owned reached.l

def machineFirstResult (initial : R) (start : Cfg Γ Λ R) (b : Bool) : Prop :=
  ∃ n finish, machineFirstRun caller initial start n finish ∧
    finish.l = some (resultLabel b)

theorem machine_phase_run (initial : R) (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[phaseSteps q D]
      (some (cfg (some (phaseLabel q)) regs D ctx)) = some (phaseResult q regs D ctx) :=
  phase_iterate caller q D regs ctx

theorem machine_cfg_run (initial : R) (start : Cfg Γ Λ R) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[remainingSteps start]
      (some start) = some (finalCfg start) := cfg_iterate caller start

theorem machine_phase_first_return (initial : R) (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    machineFirstRun caller initial (cfg (some (phaseLabel q)) regs D ctx)
      (phaseSteps q D) (phaseResult q regs D ctx) := phase_firstRun caller q D regs ctx

theorem machine_cfg_first_return (initial : R) (start : Cfg Γ Λ R) :
    machineFirstRun caller initial start (remainingSteps start) (finalCfg start) :=
  cfg_firstRun caller start

theorem machineFirstRun_iff (initial : R) (start finish : Cfg Γ Λ R) (n : Nat) :
    machineFirstRun caller initial start n finish ↔
      n = remainingSteps start ∧ finish = finalCfg start := firstRun_iff caller start finish n

theorem machineFirstResult_iff (initial : R) (start : Cfg Γ Λ R) (b : Bool) :
    machineFirstResult caller initial start b ↔ (finalCfg start).l = some (resultLabel b) :=
  firstResult_iff_finalCfg caller start b

theorem machine_owned_prefix (initial : R) (start : Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ remainingSteps start) :
    ∃ reached,
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
        (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) := owned_prefix caller start n bound

def machinePhaseInTime (initial : R) (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (cfg (some (phaseLabel q)) regs D ctx) (some (phaseResult q regs D ctx)) (phaseSteps q D) where
  steps := phaseSteps q D
  evals_in_steps := machine_phase_run caller initial q D regs ctx
  steps_le_m := Nat.le_refl _

@[simp] theorem machinePhaseInTime_steps (initial : R) (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (machinePhaseInTime caller initial q D regs ctx).steps = phaseSteps q D := rfl

def machineCfgInTime (initial : R) (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (machine caller initial).step start
      (some (finalCfg start)) (remainingSteps start) where
  steps := remainingSteps start
  evals_in_steps := machine_cfg_run caller initial start
  steps_le_m := Nat.le_refl _

@[simp] theorem machineCfgInTime_steps (initial : R) (start : Cfg Γ Λ R) :
    (machineCfgInTime caller initial start).steps = remainingSteps start := rfl

theorem machineCfgInTime_nonowned (initial : R) (start : Cfg Γ Λ R)
    (nonowned : ¬ Owned start.l) :
    (machineCfgInTime caller initial start).steps = 0 ∧ finalCfg start = start :=
  ⟨nonowned_remaining start nonowned, nonowned_finalCfg start nonowned⟩

def machinePrefixInTime (initial : R) (start reached : Cfg Γ Λ R) (n : Nat)
    (executed : (next caller)^[n] (some start) = some reached) :
    StateTransition.EvalsToInTime (machine caller initial).step start (some reached) n where
  steps := n
  evals_in_steps := executed
  steps_le_m := Nat.le_refl _

@[simp] theorem machinePrefixInTime_steps (initial : R) (start reached : Cfg Γ Λ R) (n : Nat)
    (executed : (next caller)^[n] (some start) = some reached) :
    (machinePrefixInTime caller initial start reached n executed).steps = n := rfl

theorem machine_init_run (initial : R) (raw : Word) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[4]
      (some (Turing.initList (machine caller initial) raw)) =
      some (cfg (some (resultLabel raw.isEmpty)) (initialRegisters initial)
        { certificate := raw } (fun _ => [])) := by
  rw [initList_eq]
  exact (init_input_firstRun caller raw (initialRegisters initial) (fun _ => [])).1

theorem machine_init_first_return (initial : R) (raw : Word) :
    machineFirstRun caller initial (Turing.initList (machine caller initial) raw) 4
      (cfg (some (resultLabel raw.isEmpty)) (initialRegisters initial)
        { certificate := raw } (fun _ => [])) := by
  rw [initList_eq]
  exact init_input_firstRun caller raw (initialRegisters initial) (fun _ => [])

theorem machine_init_exact_rank (initial : R) (raw : Word) :
    remainingSteps (Turing.initList (machine caller initial) raw) = 4 := by
  rw [initList_eq, remainingSteps_phase_cfg, initClock_eq]

theorem machine_init_finalCfg (initial : R) (raw : Word) :
    finalCfg (Turing.initList (machine caller initial) raw) =
      cfg (some (resultLabel raw.isEmpty)) (initialRegisters initial)
        { certificate := raw } (fun _ => []) := by
  rw [initList_eq, finalCfg_phase_cfg, initResult_eq, resetAll_initialRegisters]

def machineInitInTimeExact (initial : R) (raw : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw)
      (some (cfg (some (resultLabel raw.isEmpty)) (initialRegisters initial)
        { certificate := raw } (fun _ => []))) 4 where
  steps := 4
  evals_in_steps := machine_init_run caller initial raw
  steps_le_m := Nat.le_refl _

@[simp] theorem machineInitInTimeExact_steps (initial : R) (raw : Word) :
    (machineInitInTimeExact caller initial raw).steps = 4 := rfl

theorem machine_init_true (initial : R) :
    machineFirstResult caller initial (Turing.initList (machine caller initial) ([] : Word)) true := by
  exact ⟨4, _, machine_init_first_return caller initial ([] : Word), rfl⟩

theorem machine_init_nonempty_false (initial : R) (tag : Tag) (raw : Word) :
    machineFirstResult caller initial (Turing.initList (machine caller initial) (tag :: raw)) false := by
  exact ⟨4, _, machine_init_first_return caller initial (tag :: raw), rfl⟩

theorem machine_init_endpoint_live (initial : R) (raw : Word) :
    (finalCfg (Turing.initList (machine caller initial) raw)).l = some (resultLabel raw.isEmpty) := by
  rw [machine_init_finalCfg]
  rfl

theorem machine_init_endpoint_not_halt (initial : R) (raw : Word) :
    (finalCfg (Turing.initList (machine caller initial) raw)).l ≠ none := by
  rw [machine_init_endpoint_live]
  exact Option.some_ne_none _

theorem machine_init_final_output_empty (initial : R) (raw : Word) :
    (finalCfg (Turing.initList (machine caller initial) raw)).stk (machine caller initial).k₁ = [] := by
  rw [machine_init_finalCfg]
  rfl

theorem machine_init_final_certificate (initial : R) (raw : Word) :
    (finalCfg (Turing.initList (machine caller initial) raw)).stk (.inl .certificate) = raw := by
  rw [machine_init_finalCfg]
  rfl

end StreamPackageExecution

end Resources.RotationCertificate.StreamMachine

-- END PACKAGE EXECUTION PASSED3

-- BEGIN INSTALLATION CANONICAL PASSED3
namespace Resources.RotationCertificate.StreamMachine

variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')

def installedOwned (label : Option Λ') : Prop := Owned (label.map labels.symm)

@[simp] theorem installedCfg_owned_iff (c : Cfg Γ Λ R) :
    installedOwned labels (installedCfg names symbols registers labels c).l ↔ Owned c.l := by
  cases label : c.l <;> simp [installedOwned, installedCfg, FrontEndMachine.Transport.cfg, label]

variable [DecidableEq K] [DecidableEq K']
variable (caller : External Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')

def installedFirstRun (start : Turing.TM2.Cfg Γ' Λ' R') (n : Nat)
    (finish : Turing.TM2.Cfg Γ' Λ' R') : Prop :=
  (FrontEndMachine.Transport.next ambient)^[n] (some start) = some finish ∧
    ¬ installedOwned labels finish.l ∧
    ∀ j, j < n → ∃ reached,
      (FrontEndMachine.Transport.next ambient)^[j] (some start) = some reached ∧
        installedOwned labels reached.l

/-- Only the 39 owned bodies, including all eight paid joins, are installed. -/
theorem installed_owned_prefix
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) := by
  apply installed_prefix_of_owned names symbols registers labels caller ambient installed n start
  intro j strict
  obtain ⟨reached, executed, _, _, ownership⟩ := owned_prefix caller start j (by omega)
  exact ⟨reached, executed, ownership.mp (by omega)⟩

theorem installed_owned_firstRun
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) :
    installedFirstRun labels ambient (installedCfg names symbols registers labels start)
      (remainingSteps start) (installedCfg names symbols registers labels (finalCfg start)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [installed_owned_prefix names symbols registers labels caller ambient installed start
      (remainingSteps start) (Nat.le_refl _), cfg_iterate caller start]
    rfl
  · rw [installedCfg_owned_iff]
    exact finalCfg_not_owned start
  · intro j strict
    obtain ⟨before, run, _, _, ownership⟩ := owned_prefix caller start j (by omega)
    refine ⟨installedCfg names symbols registers labels before, ?_, ?_⟩
    · rw [installed_owned_prefix names symbols registers labels caller ambient installed start j
        (by omega), run]
      rfl
    · rw [installedCfg_owned_iff]
      exact ownership.mp strict

/-- A later caller result cannot count as the first return. This converse uses
the actual strict-earlier ownership witnesses in the candidate run. -/
theorem installed_firstRun_iff
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (finish : Turing.TM2.Cfg Γ' Λ' R') :
    installedFirstRun labels ambient (installedCfg names symbols registers labels start) n finish ↔
      n = remainingSteps start ∧
        finish = installedCfg names symbols registers labels (finalCfg start) := by
  have canonical := installed_owned_firstRun names symbols registers labels caller ambient installed start
  constructor
  · rintro ⟨run, returned, earlier⟩
    have count : n = remainingSteps start := by
      rcases lt_trichotomy n (remainingSteps start) with less | equal | greater
      · obtain ⟨middle, prefixRun, owned⟩ := canonical.2.2 n less
        have same : finish = middle := Option.some.inj (run.symm.trans prefixRun)
        exact False.elim (returned (same.symm ▸ owned))
      · exact equal
      · obtain ⟨middle, prefixRun, owned⟩ := earlier (remainingSteps start) greater
        have same : middle = installedCfg names symbols registers labels (finalCfg start) :=
          Option.some.inj (prefixRun.symm.trans canonical.1)
        exact False.elim (canonical.2.1 (same ▸ owned))
    rw [count] at run
    exact ⟨count, Option.some.inj (run.symm.trans canonical.1)⟩
  · rintro ⟨rfl, rfl⟩
    exact canonical

def installed_owned_timed
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start)
      (some (installedCfg names symbols registers labels (finalCfg start)))
      (remainingSteps start) where
  steps := remainingSteps start
  evals_in_steps :=
    (installed_owned_firstRun names symbols registers labels caller ambient installed start).1
  steps_le_m := Nat.le_refl _

@[simp] theorem installed_owned_timed_steps
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) :
    (installed_owned_timed names symbols registers labels caller ambient installed start).steps =
      remainingSteps start := rfl

def installed_owned_prefix_timed
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start)
      (some (installedCfg names symbols registers labels reached)) n where
  steps := n
  evals_in_steps := by
    change (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = _
    rw [installed_owned_prefix names symbols registers labels caller ambient installed start n bound,
      executed]
    rfl
  steps_le_m := Nat.le_refl _

@[simp] theorem installed_owned_prefix_timed_steps
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    (installed_owned_prefix_timed names symbols registers labels caller ambient installed start n
      bound reached executed).steps = n := rfl

/-- Pull an actual source prefix bound through the complete physical map for
the same supplied ambient endpoint. No external store is omitted. -/
theorem installed_prefix_cells_of_source_bound [Fintype K] [Fintype K']
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) (budget : Nat)
    (estimate : ∀ before, (next caller)^[n] (some start) = some before →
      ∑ k, (before.stk k).length ≤ budget)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = some reached) :
    ∑ k, (reached.stk k).length ≤ budget := by
  obtain ⟨before, run, _, _, _⟩ := owned_prefix caller start n bound
  have mapped := installed_owned_prefix names symbols registers labels caller ambient installed start n bound
  rw [run, Option.map_some, executed] at mapped
  have same := Option.some.inj mapped
  rw [same, installed_stack_cells]
  exact estimate before run

end Resources.RotationCertificate.StreamMachine

-- END INSTALLATION CANONICAL PASSED3

-- BEGIN INITIALIZER PREFIX PASSED3
namespace Resources.RotationCertificate.StreamMachine

variable {K Λ R : Type} {Γ : K → Type}

/-- These five proof-side labels record only the genuine four-step initializer
path. They are not callbacks in the finite runtime program. -/
def initPrefixLabel (raw : Word) : Nat → Label Λ
  | 0 => phaseLabel inspectPhase
  | 1 => if raw.isEmpty then phaseLabel (fuelJoinPhase .atEnd) else phaseLabel (counterPhase .borrow)
  | 2 => if raw.isEmpty then phaseLabel comparePhase else phaseLabel (counterPhase .restoreFalse)
  | 3 => if raw.isEmpty then phaseLabel (equalityJoinPhase .equal) else phaseLabel (fuelJoinPhase .zero)
  | _ => resultLabel raw.isEmpty

def initPrefixCfg (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k)) (n : Nat) : Cfg Γ Λ R :=
  cfg (some (initPrefixLabel raw n)) (initialRegisters initial) { certificate := raw } ctx

theorem initPrefix_data (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k)) (n : Nat) :
    dataOfCfg (initPrefixCfg (Λ := Λ) initial raw ctx n) = { certificate := raw } := rfl

theorem initPrefix_registers (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k)) (n : Nat) :
    (initPrefixCfg (Λ := Λ) initial raw ctx n).var = initialRegisters initial := rfl

theorem initPrefix_context (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k)) (n : Nat) :
    contextOfCfg (initPrefixCfg (Λ := Λ) initial raw ctx n) = ctx := rfl

theorem initPrefix_owned_iff (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ 4) :
    Owned (initPrefixCfg (Λ := Λ) initial raw ctx n).l ↔ n < 4 := by
  have possibilities : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases possibilities with rfl | rfl | rfl | rfl | rfl
  all_goals cases raw <;> simp [initPrefixCfg, initPrefixLabel, cfg]

theorem initPrefix_cells [Fintype K] (initial : R) (raw : Word)
    (ctx : ∀ k, List (Γ k)) (n : Nat) :
    ∑ k, ((initPrefixCfg (Λ := Λ) initial raw ctx n).stk k).length =
      raw.length + ∑ k, (ctx k).length := by
  rw [Fintype.sum_sum_type]
  change (∑ k ∈ ({.certificate, .moveReverse, .path, .source, .saved, .scratch,
      .units, .fuel, .target} : Finset LocalStack),
      ((initPrefixCfg (Λ := Λ) initial raw ctx n).stk (.inl k)).length) +
      (∑ k, (ctx k).length) = _
  simp [initPrefixCfg, cfg]

variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem init_borrow_step (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (counterPhase .borrow))) (initialRegisters initial)
      { certificate := raw } ctx) =
      some (cfg (some (phaseLabel (counterPhase .restoreFalse))) (initialRegisters initial)
        { certificate := raw } ctx) := by
  let D : LocalData := { certificate := raw }
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  have component := Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil
    (FuelDispatchMachine.callerHandler localCaller) (initialRegisters initial) []
    (FuelDispatchMachine.stores raw (fuelContext D ctx))
  have actual := counter_step_of_step caller localCaller .borrow D (initialRegisters initial) ctx
    (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel .restoreFalse))
    (initialRegisters initial) [] [] component
  simpa only [Option.map_some, fuelLabelEquiv_counter] using actual

theorem init_restoreFalse_step (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (counterPhase .restoreFalse))) (initialRegisters initial)
      { certificate := raw } ctx) =
      some (cfg (some (phaseLabel (fuelJoinPhase .zero))) (initialRegisters initial)
        { certificate := raw } ctx) := by
  let D : LocalData := { certificate := raw }
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  have component := Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil
    (FuelDispatchMachine.callerHandler localCaller) [] (initialRegisters initial)
    (FuelDispatchMachine.stores raw (fuelContext D ctx))
  have actual := counter_step_of_step caller localCaller .restoreFalse D (initialRegisters initial) ctx
    (some (Resources.BinaryCounter.FixedWidthMachine.resultLabel .zero))
    (initialRegisters initial) [] [] component
  have labelEq : fuelLabelEquiv (Λ := Λ) (Resources.BinaryCounter.FixedWidthMachine.resultLabel .zero) =
      phaseLabel (fuelJoinPhase .zero) := fuelLabelEquiv_exit .zero
  simpa only [Option.map_some, labelEq, D] using actual

theorem init_compare_step (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel comparePhase)) (initialRegisters initial)
      { certificate := raw } ctx) =
      some (cfg (some (phaseLabel (equalityJoinPhase .equal))) (initialRegisters initial)
        { certificate := raw } ctx) := by
  let D : LocalData := { certificate := raw }
  let localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R :=
    fun _ => .halt
  have component := TreeEqualityMachine.compare_step_nil_nil localCaller
    (equalityRegisterEquiv.symm (initialRegisters initial)) (equalityContext D ctx)
  have actual := equality_step_of_step caller localCaller D (initialRegisters initial) ctx
    (some (TreeEqualityMachine.resultLabel .equal))
    (TreeEqualityMachine.reset (equalityRegisterEquiv.symm (initialRegisters initial))) [] [] component
  simpa only [Option.map_some, equalityLabelEquiv_result, equalityRegisterEquiv_reset,
    Equiv.apply_symm_apply, D, resetEquality, initialRegisters] using actual

theorem initPrefix_step (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k))
    (n : Nat) (strict : n < 4) :
    step caller (initPrefixCfg initial raw ctx n) = some (initPrefixCfg initial raw ctx (n + 1)) := by
  have possibilities : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases possibilities with rfl | rfl | rfl | rfl
  · cases raw with
    | nil => exact inspect_step_nil caller { certificate := [] } rfl (initialRegisters initial) ctx
    | cons tag raw =>
        exact inspect_step_cons caller { certificate := tag :: raw }
          tag raw rfl (initialRegisters initial) ctx
  · cases raw with
    | nil => exact fuel_join_step caller .atEnd { certificate := [] } (initialRegisters initial) ctx
    | cons tag raw => exact init_borrow_step caller initial (tag :: raw) ctx
  · cases raw with
    | nil => exact init_compare_step caller initial [] ctx
    | cons tag raw => exact init_restoreFalse_step caller initial (tag :: raw) ctx
  · cases raw with
    | nil => exact equality_join_step caller .equal { certificate := [] } (initialRegisters initial) ctx
    | cons tag raw =>
        exact fuel_join_step caller .zero { certificate := tag :: raw }
          (initialRegisters initial) ctx

theorem initPrefix_iterate (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ 4) :
    (next caller)^[n] (some (cfg (some (phaseLabel inspectPhase)) (initialRegisters initial)
      { certificate := raw } ctx)) = some (initPrefixCfg initial raw ctx n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (by omega), next_some,
        initPrefix_step caller initial raw ctx n (by omega)]

/-- The inclusive prefix's exact cells, complete data and ownership describe
the same supplied reached configuration. -/
theorem initPrefix_exact [Fintype K] (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ 4) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel inspectPhase)) (initialRegisters initial)
        { certificate := raw } ctx)) = some reached) :
    reached = initPrefixCfg initial raw ctx n ∧
      dataOfCfg reached = { certificate := raw } ∧
      reached.var = initialRegisters initial ∧ contextOfCfg reached = ctx ∧
      (Owned reached.l ↔ n < 4) ∧
      (∑ k, (reached.stk k).length) = raw.length + ∑ k, (ctx k).length := by
  have same : reached = initPrefixCfg initial raw ctx n :=
    Option.some.inj (executed.symm.trans (initPrefix_iterate caller initial raw ctx n bound))
  subst reached
  exact ⟨rfl, rfl, rfl, rfl, initPrefix_owned_iff initial raw ctx n bound,
    initPrefix_cells initial raw ctx n⟩

section StreamInitializerPrefixPackage

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

theorem machine_init_prefix (initial : R) (raw : Word) (n : Nat) (bound : n ≤ 4) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
      (some (Turing.initList (machine caller initial) raw)) =
      some (initPrefixCfg initial raw (fun _ => []) n) := by
  rw [initList_eq]
  exact initPrefix_iterate caller initial raw (fun _ => []) n bound

theorem machine_init_prefix_cells (initial : R) (raw : Word) (n : Nat) (bound : n ≤ 4)
    (reached : Cfg Γ Λ R)
    (executed : (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
      (some (Turing.initList (machine caller initial) raw)) = some reached) :
    (∑ k, (reached.stk k).length) = raw.length := by
  have same : reached = initPrefixCfg initial raw (fun _ => []) n :=
    Option.some.inj (executed.symm.trans (machine_init_prefix caller initial raw n bound))
  rw [same, initPrefix_cells]
  simp

theorem machine_init_exact_peak (initial : R) (raw : Word) :
    (∀ n, n ≤ 4 → ∀ reached : Cfg Γ Λ R,
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
        (some (Turing.initList (machine caller initial) raw)) = some reached →
      (∑ k, (reached.stk k).length) ≤ raw.length) ∧
    ∃ n reached, n ≤ 4 ∧
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
        (some (Turing.initList (machine caller initial) raw)) = some reached ∧
      (∑ k, (reached.stk k).length) = raw.length := by
  constructor
  · intro n bound reached executed
    exact Nat.le_of_eq (machine_init_prefix_cells caller initial raw n bound reached executed)
  · refine ⟨0, Turing.initList (machine caller initial) raw, by omega, rfl, ?_⟩
    exact machine_init_prefix_cells caller initial raw 0 (by omega) _ rfl

end StreamInitializerPrefixPackage

end Resources.RotationCertificate.StreamMachine

-- END INITIALIZER PREFIX PASSED3

-- BEGIN STAGED REGISTERS PASSED2
namespace Resources.RotationCertificate.StreamMachine

variable {K Λ R : Type} {Γ : K → Type}

/-! ## The first paid outer join and staged temporary registers -/

/-- The first *outer* join includes the whole initial component and its paid
one-tick join. A component result label is still owned before this tick. -/
def firstJoinSteps (q : Phase) (D : LocalData) : Nat :=
  match q with
  | .inl (.inl q) => (counterFinish q D).steps + 1
  | .inl (.inr (.inl _)) => 1
  | .inl (.inr (.inr (.inl .inspectCertificate))) => (inspectStageFinish D).steps + 1
  | .inl (.inr (.inr (.inl .atEnd))) => 1
  | .inl (.inr (.inr (.inr impossible))) => Empty.elim impossible
  | .inr (.inl (.inl q)) => (applyFinish (MoveApplyMachine.movePhase q) D).steps + 1
  | .inr (.inl (.inr (.inl r))) => (applyFinish (MoveApplyMachine.dispatchPhase r) D).steps + 1
  | .inr (.inl (.inr (.inr (.inl q)))) => (applyFinish (MoveApplyMachine.positionPhase q) D).steps + 1
  | .inr (.inl (.inr (.inr (.inr (.inl _))))) => 1
  | .inr (.inl (.inr (.inr (.inr (.inr impossible))))) => Empty.elim impossible
  | .inr (.inr (.inl .compare)) => (equalityFinish D).steps + 1
  | .inr (.inr (.inr (.inl _))) => 1
  | .inr (.inr (.inr (.inr impossible))) => Empty.elim impossible

def firstJoinCfg (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  match q with
  | .inl (.inl q) =>
      cfg (some (fuelJoinTarget (FuelDispatchMachine.exitOfResult (counterFinish q D).result)))
        (resetAll regs) (counterFinish q D).data ctx
  | .inl (.inr (.inl r)) => cfg (some (fuelJoinTarget (FuelDispatchMachine.exitOfResult r))) (resetAll regs) D ctx
  | .inl (.inr (.inr (.inl .inspectCertificate))) =>
      cfg (some (fuelJoinTarget (inspectStageFinish D).result)) (resetAll regs) (inspectStageFinish D).data ctx
  | .inl (.inr (.inr (.inl .atEnd))) => cfg (some (fuelJoinTarget .atEnd)) (resetAll regs) D ctx
  | .inl (.inr (.inr (.inr impossible))) => Empty.elim impossible
  | .inr (.inl (.inl q)) =>
      cfg (some (applyJoinTarget (applyFinish (MoveApplyMachine.movePhase q) D).result))
        (resetAll regs) (applyFinish (MoveApplyMachine.movePhase q) D).data ctx
  | .inr (.inl (.inr (.inl r))) =>
      cfg (some (applyJoinTarget (applyFinish (MoveApplyMachine.dispatchPhase r) D).result))
        (resetAll regs) (applyFinish (MoveApplyMachine.dispatchPhase r) D).data ctx
  | .inr (.inl (.inr (.inr (.inl q)))) =>
      cfg (some (applyJoinTarget (applyFinish (MoveApplyMachine.positionPhase q) D).result))
        (resetAll regs) (applyFinish (MoveApplyMachine.positionPhase q) D).data ctx
  | .inr (.inl (.inr (.inr (.inr (.inl r))))) => cfg (some (applyJoinTarget r)) (resetAll regs) D ctx
  | .inr (.inl (.inr (.inr (.inr (.inr impossible))))) => Empty.elim impossible
  | .inr (.inr (.inl .compare)) =>
      cfg (some (equalityJoinTarget (equalityFinish D).result)) (resetAll regs) (equalityFinish D).data ctx
  | .inr (.inr (.inr (.inl r))) => cfg (some (equalityJoinTarget r)) (resetAll regs) D ctx
  | .inr (.inr (.inr (.inr impossible))) => Empty.elim impossible

@[simp] theorem firstJoinSteps_counter (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) :
    firstJoinSteps (counterPhase q) D = Resources.BinaryCounter.FixedWidthMachine.phaseSteps q D.fuel D.units + 1 := by
  exact congrArg (fun n => n + 1) (counterFinish_steps q D)

@[simp] theorem firstJoinSteps_apply (q : MoveApplyMachine.Phase) (D : LocalData) :
    firstJoinSteps (applyPhase q) D = MoveApplyMachine.phaseSteps q (applyData D) + 1 := by
  rcases q with q | (r | q) <;> rfl

@[simp] theorem firstJoinSteps_compare (D : LocalData) :
    firstJoinSteps comparePhase D = TreeEqualityMachine.runSteps D.source D.target + 1 := rfl

@[simp] theorem firstJoinSteps_fuel_join (r : FuelDispatchMachine.Exit) (D : LocalData) :
    firstJoinSteps (fuelJoinPhase r) D = 1 := by cases r <;> rfl

@[simp] theorem firstJoinSteps_apply_join (r : MoveApplyMachine.FinalResult) (D : LocalData) :
    firstJoinSteps (applyJoinPhase r) D = 1 := rfl

@[simp] theorem firstJoinSteps_equality_join (r : TreeEqualityMachine.Result) (D : LocalData) :
    firstJoinSteps (equalityJoinPhase r) D = 1 := rfl

theorem firstJoinSteps_inspect_nil (D : LocalData) (empty : D.certificate = []) :
    firstJoinSteps inspectPhase D = 2 := by
  change (inspectStageFinish D).steps + 1 = 2
  simp only [inspectStageFinish, empty]

theorem firstJoinSteps_inspect_cons (D : LocalData) (tag : Tag) (raw : Word)
    (nonempty : D.certificate = tag :: raw) :
    firstJoinSteps inspectPhase D = Resources.BinaryCounter.FixedWidthMachine.runSteps D.fuel + D.units.length + 2 := by
  change (inspectStageFinish D).steps + 1 = _
  simp only [inspectStageFinish, nonempty, counterFinish]
  omega

theorem firstJoinCfg_var (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : (firstJoinCfg (Λ := Λ) q regs D ctx).var = resetAll regs := by
  rcases q with fuel | (applied | equality)
  · rcases fuel with q | (r | (d | impossible))
    · rfl
    · rfl
    · cases d <;> rfl
    · exact Empty.elim impossible
  · rcases applied with q | (r | (q | (r | impossible))) <;> try rfl
    exact Empty.elim impossible
  · rcases equality with q | (r | impossible)
    · cases q; rfl
    · rfl
    · exact Empty.elim impossible

variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem firstJoin_localRun (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (firstJoinSteps q D) (cfg (some (phaseLabel q)) regs D ctx)
      (firstJoinCfg q regs D ctx) := by
  have counter (q : Resources.BinaryCounter.FixedWidthMachine.Phase) :
      LocalRun caller ((counterFinish q D).steps + 1)
        (cfg (some (phaseLabel (counterPhase q))) regs D ctx)
        (cfg (some (fuelJoinTarget (FuelDispatchMachine.exitOfResult (counterFinish q D).result)))
          (resetAll regs) (counterFinish q D).data ctx) := by
    simpa only [resetAll_resetFuel] using LocalRun.trans caller
      (counter_phase_localRun caller q D regs ctx)
      (fuel_join_localRun caller (FuelDispatchMachine.exitOfResult (counterFinish q D).result)
        (counterFinish q D).data (resetFuel regs) ctx)
  have applied (q : MoveApplyMachine.Phase) :
      LocalRun caller ((applyFinish q D).steps + 1)
        (cfg (some (phaseLabel (applyPhase q))) regs D ctx)
        (cfg (some (applyJoinTarget (applyFinish q D).result)) (resetAll regs) (applyFinish q D).data ctx) := by
    simpa only [resetAll_resetApply] using LocalRun.trans caller
      (apply_phase_localRun caller q D regs ctx)
      (apply_join_localRun caller (applyFinish q D).result (applyFinish q D).data (resetApply regs) ctx)
  rcases q with fuel | (application | equality)
  · rcases fuel with q | (r | (d | impossible))
    · exact counter q
    · cases r with
      | positive => exact fuel_join_localRun caller .positive D regs ctx
      | zero => exact fuel_join_localRun caller .zero D regs ctx
    · cases d with
      | inspectCertificate =>
          change LocalRun caller ((inspectStageFinish D).steps + 1)
            (cfg (some (phaseLabel inspectPhase)) regs D ctx)
            (cfg (some (fuelJoinTarget (inspectStageFinish D).result))
              (resetAll regs) (inspectStageFinish D).data ctx)
          simpa only [resetAll_resetFuel] using LocalRun.trans caller
            (inspect_stage_localRun caller D regs ctx)
            (fuel_join_localRun caller (inspectStageFinish D).result (inspectStageFinish D).data (resetFuel regs) ctx)
      | atEnd => exact fuel_join_localRun caller .atEnd D regs ctx
    · exact Empty.elim impossible
  · rcases application with q | (r | (q | (r | impossible)))
    · exact applied (MoveApplyMachine.movePhase q)
    · exact applied (MoveApplyMachine.dispatchPhase r)
    · exact applied (MoveApplyMachine.positionPhase q)
    · exact apply_join_localRun caller r D regs ctx
    · exact Empty.elim impossible
  · rcases equality with q | (r | impossible)
    · cases q
      change LocalRun caller ((equalityFinish D).steps + 1)
        (cfg (some (phaseLabel comparePhase)) regs D ctx)
        (cfg (some (equalityJoinTarget (equalityFinish D).result))
          (resetAll regs) (equalityFinish D).data ctx)
      simpa only [resetAll_resetEquality] using LocalRun.trans caller
        (equality_phase_localRun caller D regs ctx)
        (equality_join_localRun caller (equalityFinish D).result (equalityFinish D).data (resetEquality regs) ctx)
    · exact equality_join_localRun caller r D regs ctx
    · exact Empty.elim impossible

omit [DecidableEq K] in
theorem firstJoinSteps_le_phaseSteps (q : Phase) (D : LocalData) : firstJoinSteps q D ≤ phaseSteps q D := by
  let localCaller : External Empty → Statement (fun _ : Empty => Empty) Empty Unit := fun _ => .halt
  let regs : Registers Unit := (none, ((none, (none, none)), ()))
  have rank := LocalRun.remaining localCaller (firstJoin_localRun localCaller q D regs (fun k : Empty => Empty.elim k))
  rw [remainingSteps_phase_cfg] at rank
  omega

theorem prefix_reset_after_firstJoin (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (afterJoin : firstJoinSteps q D ≤ n) (bound : n ≤ phaseSteps q D)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached) :
    reached.var = resetAll regs := by
  have segment := firstJoin_localRun caller q D regs ctx
  have rank := LocalRun.remaining caller segment
  rw [remainingSteps_phase_cfg] at rank
  have count : firstJoinSteps q D + (n - firstJoinSteps q D) = n := by omega
  have rest : (next caller)^[n - firstJoinSteps q D] (some (firstJoinCfg q regs D ctx)) = some reached := by
    rw [← prefix_iterate_after_localRun caller segment, count]
    exact executed
  have clean : resetAll (firstJoinCfg (Λ := Λ) q regs D ctx).var = (firstJoinCfg (Λ := Λ) q regs D ctx).var := by
    rw [firstJoinCfg_var, resetAll_resetAll]
  have registers := prefix_resetAll caller (firstJoinCfg q regs D ctx) reached
    (n - firstJoinSteps q D) (by omega) rest clean
  rwa [firstJoinCfg_var] at registers

theorem fuel_prefix_reset
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (start : FuelCfg Γ Λ R) (n : Nat) (positive : 0 < n)
    (bound : n ≤ FuelDispatchMachine.remainingSteps start) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (fuelCfg start)) = some reached) :
    reached.var = resetFuel start.var := by
  obtain ⟨middle, run, path, rfl⟩ := fuel_prefix_lift caller localCaller start n bound reached executed
  have cleared := FuelDispatchMachine.prefix_local_register localCaller n start middle bound run positive
  have kept := (fuel_local_reaches_frame localCaller path).1
  change middle.var = (none, start.var.2)
  exact Prod.ext cleared kept

theorem counter_stage_prefix_reset (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (positive : 0 < n) (bound : n ≤ (counterFinish q D).steps)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel (counterPhase q))) regs D ctx)) = some reached) :
    reached.var = resetFuel regs := by
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  let start : FuelCfg Γ Λ R := fuelView (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel q)) regs D ctx
  have startEq : fuelCfg start = cfg (some (phaseLabel (counterPhase q))) regs D ctx := by
    rw [fuelCfg_view]
    rfl
  have rank : FuelDispatchMachine.remainingSteps start = (counterFinish q D).steps := by cases q <;> rfl
  exact fuel_prefix_reset caller localCaller start n positive (by rwa [rank]) reached (by rwa [startEq])

theorem inspect_stage_prefix_reset (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : Cfg Γ Λ R) (positive : 0 < n) (bound : n ≤ (inspectStageFinish D).steps)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel inspectPhase)) regs D ctx)) = some reached) :
    reached.var = resetFuel regs := by
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  let start : FuelCfg Γ Λ R := fuelView (some FuelDispatchMachine.inspectLabel) regs D ctx
  have startEq : fuelCfg start = cfg (some (phaseLabel inspectPhase)) regs D ctx := by
    rw [fuelCfg_view]
    rfl
  have rank : FuelDispatchMachine.remainingSteps start = (inspectStageFinish D).steps := by
    cases cert : D.certificate with
    | nil => simp only [start, fuelView, FuelDispatchMachine.remainingSteps, FuelDispatchMachine.cfg,
        Resources.BinaryCounter.FixedWidthMachine.cfg, FuelDispatchMachine.inspectLabel,
        Resources.BinaryCounter.FixedWidthMachine.callerLabel, FuelDispatchMachine.stores,
        cert, inspectStageFinish]
    | cons tag raw =>
        simp only [start, fuelView, FuelDispatchMachine.remainingSteps, FuelDispatchMachine.cfg,
          Resources.BinaryCounter.FixedWidthMachine.cfg, FuelDispatchMachine.inspectLabel,
          Resources.BinaryCounter.FixedWidthMachine.callerLabel, FuelDispatchMachine.stores,
          cert, inspectStageFinish, counterFinish]
        omega
  exact fuel_prefix_reset caller localCaller start n positive (by rwa [rank]) reached (by rwa [startEq])

omit [DecidableEq K] in
theorem toApplyCfg_applyCfg (start : ApplyCfg Γ Λ R) : toApplyCfg (applyCfg start) = start := by
  apply FrontEndMachine.Transport.cfg_injective applyStackEquiv applySymbolEquiv applyRegisterEquiv
    applyLabelEquiv applyLabelEquiv.injective
  exact applyCfg_toApplyCfg (applyCfg start)

theorem apply_stage_prefix_reset (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ (applyFinish q D).steps)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel (applyPhase q))) regs D ctx)) = some reached) :
    reached.var = applyRegisterEquiv (MoveApplyMachine.registersAt
      (toApplyCfg (cfg (some (phaseLabel (Λ := Λ) (applyPhase q))) regs D ctx)) n) := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let start : ApplyCfg Γ Λ R := applyView (some (MoveApplyMachine.phaseLabel q)) (applyRegisterEquiv.symm regs) D ctx
  have startEq : applyCfg start = cfg (some (phaseLabel (applyPhase q))) regs D ctx := by
    rw [applyCfg_view]
    simp only [Option.map_some, applyLabelEquiv_phase, Equiv.apply_symm_apply]
  have rank : MoveApplyMachine.remainingSteps start = (applyFinish q D).steps := by
    change MoveApplyMachine.remainingSteps (MoveApplyMachine.cfg _ _ _ _) = _
    rw [MoveApplyMachine.remainingSteps_phase_cfg]
    rfl
  obtain ⟨middle, run, _, rfl⟩ := apply_prefix_lift caller localCaller start n
    (by rwa [rank]) reached (by rwa [startEq])
  change applyRegisterEquiv middle.var = _
  rw [MoveApplyMachine.prefix_reset localCaller start middle n (by rwa [rank]) run,
    ← startEq, toApplyCfg_applyCfg]

theorem equality_stage_prefix_reset (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : Cfg Γ Λ R) (positive : 0 < n) (bound : n ≤ (equalityFinish D).steps)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel comparePhase)) regs D ctx)) = some reached) :
    reached.var = resetEquality regs := by
  let localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R := fun _ => .halt
  let start : EqualityCfg Γ Λ R := equalityView (some (TreeEqualityMachine.phaseLabel .compare))
    (equalityRegisterEquiv.symm regs) D ctx
  have startEq : equalityCfg start = cfg (some (phaseLabel comparePhase)) regs D ctx := by
    rw [equalityCfg_view]
    simp only [Option.map_some, equalityLabelEquiv_phase, Equiv.apply_symm_apply]
  have rank : TreeEqualityMachine.remainingSteps start = (equalityFinish D).steps := rfl
  obtain ⟨middle, run, _, rfl⟩ := equality_prefix_lift caller localCaller start n
    (by rwa [rank]) reached (by rwa [startEq])
  have registers := TreeEqualityMachine.prefix_reset localCaller D.source D.target
    (equalityRegisterEquiv.symm regs) (equalityContext D ctx) n middle positive bound run
  change equalityRegisterEquiv middle.var = _
  rw [registers, equalityRegisterEquiv_reset, Equiv.apply_symm_apply]

omit [DecidableEq K] in
def phaseRegistersBeforeJoin (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) (n : Nat) : Registers R :=
  match q with
  | .inl _ => resetFuel regs
  | .inr (.inl _) => applyRegisterEquiv (MoveApplyMachine.registersAt
      (toApplyCfg (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx)) n)
  | .inr (.inr _) => resetEquality regs

omit [DecidableEq K] in
def phaseRegistersAt (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) (n : Nat) : Registers R :=
  if n = 0 then regs else if n < firstJoinSteps q D
    then phaseRegistersBeforeJoin (Λ := Λ) q regs D ctx n else resetAll regs

omit [DecidableEq K] in
/-- This is the register value at the same actual inclusive prefix. Before
the first paid outer join, only the active component's temporary fields clear;
after the join all four temporary fields are none. -/
def registersAt (start : Cfg Γ Λ R) (n : Nat) : Registers R :=
  match start.l with
  | some (.inl q) => phaseRegistersAt (Λ := Λ) (.inl q) start.var (dataOfCfg start) (contextOfCfg start) n
  | some (.inr (.inl q)) => phaseRegistersAt (Λ := Λ) (.inr (.inl q)) start.var (dataOfCfg start) (contextOfCfg start) n
  | some (.inr (.inr (.inl q))) => phaseRegistersAt (Λ := Λ) (.inr (.inr q)) start.var (dataOfCfg start) (contextOfCfg start) n
  | _ => start.var

omit [DecidableEq K] in
theorem registersAt_phase_cfg (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) (n : Nat) :
    registersAt (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) n =
      phaseRegistersAt (Λ := Λ) q regs D ctx n := by
  rcases q with q | (q | q) <;> rfl

theorem phase_prefix_reset (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R) (bound : n ≤ phaseSteps q D)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached) :
    reached.var = phaseRegistersAt (Λ := Λ) q regs D ctx n := by
  by_cases zero : n = 0
  · subst n
    have same : cfg (some (phaseLabel q)) regs D ctx = reached := Option.some.inj executed
    subst reached
    rfl
  have positive : 0 < n := by omega
  by_cases early : n < firstJoinSteps q D
  · simp only [phaseRegistersAt, zero, ite_false, early, ite_true]
    rcases q with fuel | (application | equality)
    · rcases fuel with q | (r | (d | impossible))
      · exact counter_stage_prefix_reset caller q D regs ctx n reached positive (by
          change n < (counterFinish q D).steps + 1 at early
          omega) executed
      · cases r <;> change n < 1 at early <;> omega
      · cases d with
        | inspectCertificate =>
            exact inspect_stage_prefix_reset caller D regs ctx n reached positive (by
              change n < (inspectStageFinish D).steps + 1 at early
              omega) executed
        | atEnd => change n < 1 at early; omega
      · exact Empty.elim impossible
    · rcases application with q | (r | (q | (r | impossible)))
      · exact apply_stage_prefix_reset caller (MoveApplyMachine.movePhase q) D regs ctx n reached (by
          change n < (applyFinish (MoveApplyMachine.movePhase q) D).steps + 1 at early
          omega) executed
      · exact apply_stage_prefix_reset caller (MoveApplyMachine.dispatchPhase r) D regs ctx n reached (by
          change n < (applyFinish (MoveApplyMachine.dispatchPhase r) D).steps + 1 at early
          omega) executed
      · exact apply_stage_prefix_reset caller (MoveApplyMachine.positionPhase q) D regs ctx n reached (by
          change n < (applyFinish (MoveApplyMachine.positionPhase q) D).steps + 1 at early
          omega) executed
      · change n < 1 at early; omega
      · exact Empty.elim impossible
    · rcases equality with q | (r | impossible)
      · cases q
        exact equality_stage_prefix_reset caller D regs ctx n reached positive (by
          change n < (equalityFinish D).steps + 1 at early
          omega) executed
      · change n < 1 at early; omega
      · exact Empty.elim impossible
  · simp only [phaseRegistersAt, zero, ite_false, early]
    exact prefix_reset_after_firstJoin caller q D regs ctx n reached (by omega) bound executed

theorem prefix_reset (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) : reached.var = registersAt start n := by
  by_cases owned : Owned start.l
  · obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases start owned
    rw [registersAt_phase_cfg]
    rw [remainingSteps_phase_cfg] at bound
    exact phase_prefix_reset caller q D regs ctx n reached bound executed
  · have rank : remainingSteps start = 0 := by
      have := (remainingSteps_pos_iff start).not.mpr owned
      omega
    have zero : n = 0 := by omega
    subst n
    have same : start = reached := Option.some.inj executed
    subst reached
    cases labelEq : start.l with
    | none => simp only [registersAt, labelEq]
    | some label =>
        rcases label with fuel | (applied | (equality | external))
        · exact False.elim (owned (by simp only [labelEq, Owned]))
        · exact False.elim (owned (by simp only [labelEq, Owned]))
        · exact False.elim (owned (by simp only [labelEq, Owned]))
        · simp only [registersAt, labelEq]

/-- One actual witness carries execution, exact remaining rank, local closure,
ownership at precisely the strict prefixes, zero-prefix identity, staged
registers, the caller register, and every protected stack. No finiteness of K
is needed for these operational and frame facts. -/
theorem owned_prefix_frame (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      reached.var.2.2 = start.var.2.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨reached, executed, rank, path, owned⟩ := owned_prefix caller start n bound
  refine ⟨reached, executed, rank, path, owned, ?_, prefix_reset caller start reached n bound executed,
    local_reaches_frame caller path⟩
  intro zero
  subst n
  exact (Option.some.inj executed).symm

end Resources.RotationCertificate.StreamMachine

-- END STAGED REGISTERS PASSED2

-- BEGIN SHARED DIRTY PREFIX SPACE
namespace Resources.RotationCertificate.StreamMachine

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)

/-- A single actual reached configuration carries the full dirty prefix
contract, including staged registers and the literal whole physical sum. -/
theorem owned_prefix_space (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      reached.var.2.2 = start.var.2.2 ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
      stackCells reached ≤ allowance start := by
  obtain ⟨reached, executed, rank, path, live, zero, registers, callerRegister, frame⟩ :=
    owned_prefix_frame caller start n bound
  exact ⟨reached, executed, rank, path, live, zero, registers, callerRegister, frame,
    prefix_stackCells_le_dirty caller start n bound reached executed⟩

end Resources.RotationCertificate.StreamMachine

-- END SHARED DIRTY PREFIX SPACE

