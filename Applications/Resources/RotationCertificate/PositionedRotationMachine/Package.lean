import Applications.Resources.RotationCertificate.PositionedRotationMachine.Space

/-!
# PositionedRotationMachine: Package
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.PositionedRotationMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-! ## Finite package and genuine initializer -/

section PositionFinitePackage

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

def initialRegisters (initial : R) : Registers R := ((none, (none, none)), initial)

/-- Caller, direction and initial caller state are fixed before the raw input. -/
def machine (d : RotationDirection) (initial : R) : Turing.FinTM2 where
  K := StackId K
  k₀ := .inl .source
  k₁ := .inl .source
  Γ := alphabet Γ
  Λ := Label Λ
  main := phaseLabel (.seek d)
  σ := Registers R
  initialState := initialRegisters initial
  Γk₀Fin := alphabetFintype (.inl .source)
  m := program caller

/-- The stronger finite alphabet evidence is exhibited at every actual index. -/
@[instance_reducible]
def machineAlphabetFintype (d : RotationDirection) (initial : R)
    (k : (machine caller d initial).K) :
    Fintype ((machine caller d initial).Γ k) := alphabetFintype k

theorem machine_card_stackId (d : RotationDirection) (initial : R) :
    @Fintype.card (machine caller d initial).K (machine caller d initial).kFin = 5 + Fintype.card K :=
  card_stackId

theorem machine_card_label (d : RotationDirection) (initial : R) :
    @Fintype.card (machine caller d initial).Λ (machine caller d initial).ΛFin = 18 + Fintype.card Λ :=
  card_label

theorem machine_card_registers (d : RotationDirection) (initial : R) :
    @Fintype.card (machine caller d initial).σ (machine caller d initial).σFin = 102 * Fintype.card R :=
  card_registers

theorem machine_step_eq (d : RotationDirection) (initial : R) (c : Cfg Γ Λ R) :
    (machine caller d initial).step c = step caller c := rfl

/-- A real one-input initializer: every store other than source is empty. -/
theorem initList_eq (d : RotationDirection) (initial : R) (raw : Word) :
    Turing.initList (machine caller d initial) raw =
      entry d (initialRegisters initial) raw [] (fun _ => []) := by
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem machine_phase_run (d : RotationDirection) (initial : R) (q : Phase)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller d initial).step)^[phaseSteps q D]
        (some (cfg (some (phaseLabel q)) regs D ctx)) = some (phaseResult q regs D ctx) :=
  phase_iterate caller q D regs ctx

theorem machine_cfg_run (d : RotationDirection) (initial : R)
    (raw : Word) (path : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller d initial).step)^[runSteps d raw path]
        (some (entry d regs raw path ctx)) =
      some (phaseResult (.seek d) regs { source := raw, path := path } ctx) :=
  phase_iterate caller (.seek d) { source := raw, path := path } regs ctx

theorem machine_init_run (d : RotationDirection) (initial : R) (raw : Word) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller d initial).step)^[runSteps d raw []]
        (some (Turing.initList (machine caller d initial) raw)) =
      some (phaseResult (.seek d) (initialRegisters initial) { source := raw } (fun _ => [])) := by
  rw [initList_eq]
  exact machine_cfg_run caller d initial raw [] (initialRegisters initial) (fun _ => [])

def machinePhaseInTime (d : RotationDirection) (initial : R) (q : Phase)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller d initial).step
      (cfg (some (phaseLabel q)) regs D ctx) (some (phaseResult q regs D ctx)) (phaseSteps q D) where
  steps := phaseSteps q D
  evals_in_steps := machine_phase_run caller d initial q D regs ctx
  steps_le_m := Nat.le_refl _

def machineCfgInTime (d : RotationDirection) (initial : R)
    (raw : Word) (path : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller d initial).step (entry d regs raw path ctx)
      (some (phaseResult (.seek d) regs { source := raw, path := path } ctx))
      (runSteps d raw path) where
  steps := runSteps d raw path
  evals_in_steps := machine_cfg_run caller d initial raw path regs ctx
  steps_le_m := Nat.le_refl _

def machineInitInTime (d : RotationDirection) (initial : R) (raw : Word) :
    StateTransition.EvalsToInTime (machine caller d initial).step
      (Turing.initList (machine caller d initial) raw)
      (some (phaseResult (.seek d) (initialRegisters initial) { source := raw } (fun _ => [])))
      (runSteps d raw []) where
  steps := runSteps d raw []
  evals_in_steps := machine_init_run caller d initial raw
  steps_le_m := Nat.le_refl _

def machineInitInLinearTime (d : RotationDirection) (initial : R) (raw : Word) :
    StateTransition.EvalsToInTime (machine caller d initial).step
      (Turing.initList (machine caller d initial) raw)
      (some (phaseResult (.seek d) (initialRegisters initial) { source := raw } (fun _ => [])))
      (3 * raw.length + 5) where
  steps := runSteps d raw []
  evals_in_steps := machine_init_run caller d initial raw
  steps_le_m := by simpa using runSteps_le d raw []

def machineInitInConservativeTime (d : RotationDirection) (initial : R) (raw : Word) :
    StateTransition.EvalsToInTime (machine caller d initial).step
      (Turing.initList (machine caller d initial) raw)
      (some (phaseResult (.seek d) (initialRegisters initial) { source := raw } (fun _ => [])))
      (4 * raw.length + 12) where
  steps := runSteps d raw []
  evals_in_steps := machine_init_run caller d initial raw
  steps_le_m := by simpa using runSteps_le_conservative d raw []

/-- The installed-path contract is distinct from source-only initialization. -/
theorem machine_cfg_prefix_stackCells_le (d : RotationDirection) (initial : R)
    (raw : Word) (path : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps d raw path) (reached : Cfg Γ Λ R)
    (executed :
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller d initial).step)^[n]
        (some (entry d regs raw path ctx)) = some reached) :
    stackCells reached ≤ 2 * raw.length + path.length + contextCells ctx :=
  prefix_stackCells_le caller d raw path regs ctx n bound reached executed

theorem machine_prefix_stackCells_le (d : RotationDirection) (initial : R)
    (raw : Word) (n : Nat) (bound : n ≤ runSteps d raw []) (reached : Cfg Γ Λ R)
    (executed :
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller d initial).step)^[n]
        (some (Turing.initList (machine caller d initial) raw)) = some reached) :
    stackCells reached ≤ 2 * raw.length := by
  rw [initList_eq] at executed
  have cells := machine_cfg_prefix_stackCells_le caller d initial raw [] (initialRegisters initial)
    (fun _ => []) n bound reached executed
  simpa [contextCells] using cells

end PositionFinitePackage

end Resources.RotationCertificate.PositionedRotationMachine
