import Applications.Resources.RotationCertificate.MoveApplyMachine.PrincipalSpace

/-!
# MoveApplyMachine: Package
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.MoveApplyMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-! ## Actual finite package and certificate-only initialization -/

section MoveApplyFinitePackage

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

def initialRegisters (initial : R) : Registers R := ((none, (none, none)), initial)

/-- The program, finite carrier and caller state are fixed before the input word. -/
def machine (initial : R) : Turing.FinTM2 where
  K := StackId K
  k₀ := .inl .certificate
  k₁ := .inl .source
  Γ := alphabet Γ
  Λ := Label Λ
  main := moveLabel .start
  σ := Registers R
  initialState := initialRegisters initial
  Γk₀Fin := alphabetFintype (.inl .certificate)
  m := program caller

@[instance_reducible]
def machineAlphabetFintype (initial : R) (k : (machine caller initial).K) :
    Fintype ((machine caller initial).Γ k) := alphabetFintype k

theorem machine_card_stackId (initial : R) :
    @Fintype.card (machine caller initial).K (machine caller initial).kFin =
      7 + Fintype.card K := card_stackId

theorem machine_card_label (initial : R) :
    @Fintype.card (machine caller initial).Λ (machine caller initial).ΛFin =
      29 + Fintype.card Λ := card_label

theorem machine_card_registers (initial : R) :
    @Fintype.card (machine caller initial).σ (machine caller initial).σFin =
      102 * Fintype.card R := card_registers

theorem machine_step_eq (initial : R) (c : Cfg Γ Λ R) :
    (machine caller initial).step c = step caller c := rfl

/-- The initializer installs only the certificate; source and all other stores are empty. -/
theorem initList_eq (initial : R) (raw : Word) :
    Turing.initList (machine caller initial) raw =
      cfg (some (moveLabel .start)) (initialRegisters initial) { certificate := raw }
        (fun _ => []) := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

theorem machine_phase_run (initial : R) (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[phaseSteps q D]
      (some (cfg (some (phaseLabel q)) regs D ctx)) = some (phaseResult q regs D ctx) :=
  phase_iterate caller q D regs ctx

/-- This package-step execution theorem accepts every physically installed configuration. -/
theorem machine_cfg_run (initial : R) (start : Cfg Γ Λ R) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[remainingSteps start]
      (some start) = some (finalCfg start) := cfg_iterate caller start

theorem machine_init_run (initial : R) (raw : Word) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[
      phaseSteps (movePhase .start) { certificate := raw }]
      (some (Turing.initList (machine caller initial) raw)) =
        some (phaseResult (movePhase .start) (initialRegisters initial)
          { certificate := raw } (fun _ => [])) := by
  rw [initList_eq]
  exact machine_phase_run caller initial (movePhase .start) { certificate := raw }
    (initialRegisters initial) (fun _ => [])

def machinePhaseInTime (initial : R) (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (cfg (some (phaseLabel q)) regs D ctx) (some (phaseResult q regs D ctx)) (phaseSteps q D) where
  steps := phaseSteps q D
  evals_in_steps := machine_phase_run caller initial q D regs ctx
  steps_le_m := Nat.le_refl _

def machineCfgInTime (initial : R) (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (machine caller initial).step start
      (some (finalCfg start)) (remainingSteps start) where
  steps := remainingSteps start
  evals_in_steps := machine_cfg_run caller initial start
  steps_le_m := Nat.le_refl _

def machineInitInTimeExact (initial : R) (raw : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw)
      (some (phaseResult (movePhase .start) (initialRegisters initial)
        { certificate := raw } (fun _ => [])))
      (phaseSteps (movePhase .start) { certificate := raw }) where
  steps := phaseSteps (movePhase .start) { certificate := raw }
  evals_in_steps := machine_init_run caller initial raw
  steps_le_m := Nat.le_refl _

@[simp] theorem machineInitInTimeExact_steps (initial : R) (raw : Word) :
    (machineInitInTimeExact caller initial raw).steps =
      phaseSteps (movePhase .start) { certificate := raw } := rfl

theorem machine_init_first_return (initial : R) (raw : Word) :
    ¬ Owned (phaseResult (Γ := Γ) (Λ := Λ) (movePhase .start) (initialRegisters initial)
      { certificate := raw } (fun _ : K => [])).l ∧
    ∀ n, n < phaseSteps (movePhase .start) { certificate := raw } → ∃ reached,
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
        (some (Turing.initList (machine caller initial) raw)) = some reached ∧ Owned reached.l := by
  rw [initList_eq]
  exact phase_first_return caller (movePhase .start) { certificate := raw }
    (initialRegisters initial) (fun _ => [])

end MoveApplyFinitePackage

/-! The next lemmas expose the actual initializer outcome, including the consumed
first path branch on empty source. They are statements about the live result,
not Boolean cleanup or haltList. -/

theorem position_empty_evaluate (d : RotationDirection) (p : List Branch) :
    PositionedRotationMachine.evaluate (.inl (.seek d)) { path := p } =
      ⟨.failure, { path := p.tail }, if p = [] then 4 else 3⟩ := by
  cases p with
  | nil =>
      cases d <;> simp only [PositionedRotationMachine.evaluate_phase,
        PositionedRotationMachine.advance, PositionedRotationMachine.evaluate_result]
      <;> rfl
  | cons b p =>
      simp only [PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance,
        PositionedRotationMachine.evaluate_result]
      rfl

def initOutcome (raw : Word) : FinalResult :=
  match (parseMoveRun raw).1 with
  | none => parseFailure
  | some _ => rotationFailure

def initClock (raw : Word) : Nat :=
  match (parseMoveRun raw).1 with
  | none => MoveParserMachine.fullSteps raw + 1
  | some (move, _) => if move.position = [] then 8 else 2 * move.position.length + 7

def initData (raw : Word) : LocalData :=
  match (parseMoveRun raw).1 with
  | none => { certificate := raw }
  | some (move, rest) => { certificate := rest, path := move.position.tail }

theorem initClock_eq (raw : Word) :
    runSteps raw [] [] [] [] [] = initClock raw := by
  cases parsed : (parseMoveRun raw).1 with
  | none =>
      rw [runSteps_of_none raw [] [] [] [] [] parsed]
      simp only [initClock, parsed]
  | some pair =>
      rcases pair with ⟨move, rest⟩
      rw [runSteps_of_some raw move rest [] [] [] [] [] parsed,
        MoveParserMachine.fullSteps_of_some raw move rest parsed]
      simp only [List.append_nil, PositionedRotationMachine.phaseSteps, position_empty_evaluate,
        initClock, parsed]
      split_ifs with empty
      · simp only [empty, List.length_nil]
      · omega

include caller in
theorem initResult_eq (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runResult (Λ := Λ) regs raw [] [] [] [] [] ctx =
      cfg (some (resultLabel (initOutcome raw))) (reset regs) (initData raw) ctx := by
  cases parsed : (parseMoveRun raw).1 with
  | none =>
      rw [runResult_of_none caller raw [] [] [] [] [] regs ctx parsed]
      simp only [initOutcome, initData, parsed, entryData]
  | some pair =>
      rcases pair with ⟨move, rest⟩
      rw [runResult_of_some caller raw move rest [] [] [] [] [] regs ctx parsed]
      simp only [phaseResult, positionPhase, evaluate, evaluatePosition, parsedData, entryData,
        positionData, List.append_nil, position_empty_evaluate, setPositionData,
        initOutcome, initData, parsed, rotationFailure]

theorem initOutcome_failure (raw : Word) :
    initOutcome raw = parseFailure ∨ initOutcome raw = rotationFailure := by
  cases parsed : (parseMoveRun raw).1 <;> simp [initOutcome, parsed]

section MoveApplyInitializerResult

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

theorem machine_init_first_result (initial : R) (raw : Word) :
    (initOutcome raw = parseFailure ∨ initOutcome raw = rotationFailure) ∧
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[initClock raw]
      (some (Turing.initList (machine caller initial) raw)) =
        some (cfg (some (resultLabel (initOutcome raw))) (initialRegisters initial)
          (initData raw) (fun _ => [])) ∧
    ∀ j, j < initClock raw → ∃ reached,
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[j]
        (some (Turing.initList (machine caller initial) raw)) = some reached ∧ Owned reached.l := by
  refine ⟨initOutcome_failure raw, ?_, ?_⟩
  · have run := machine_init_run caller initial raw
    change (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[
      runSteps raw [] [] [] [] []] (some (Turing.initList (machine caller initial) raw)) =
      some (runResult (initialRegisters initial) raw [] [] [] [] [] (fun _ => [])) at run
    rw [initClock_eq, initResult_eq caller] at run
    exact run
  · intro j before
    have clock : phaseSteps (movePhase .start) { certificate := raw } = initClock raw :=
      initClock_eq raw
    exact (machine_init_first_return caller initial raw).2 j (by simpa only [clock] using before)

end MoveApplyInitializerResult

/-! ## Actual package timing on physically installed principal and represented states -/

section MoveApplyPackageRepresented

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

def machineRunInTimeExact (initial : R) (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (entry regs raw path source saved scratch pending ctx)
      (some (runResult regs raw path source saved scratch pending ctx))
      (runSteps raw path source saved scratch pending) :=
  runInTimeExact caller raw path source saved scratch pending regs ctx

def machineRunInLinearTime (initial : R) (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (entry regs raw path source saved scratch pending ctx)
      (some (runResult regs raw path source saved scratch pending ctx))
      (3 * raw.length + 3 * source.length + saved.length + scratch.length +
        pending.length + path.length + 3) :=
  runInLinearTime caller raw path source saved scratch pending regs ctx

@[simp] theorem machineRunInLinearTime_steps (initial : R) (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (machineRunInLinearTime caller initial raw path source saved scratch pending regs ctx).steps =
      runSteps raw path source saved scratch pending := rfl

def machineRepresentedInTime (initial : R) (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)
      (some (cfg (some (resultLabel (representedResult move oldPath s))) (reset regs)
        (representedFinalData move certificateRest oldPath s saved suffix) ctx))
      (representedSteps move oldPath s saved) :=
  representedInTime caller move certificateRest oldPath s saved suffix regs ctx

@[simp] theorem machineRepresentedInTime_steps (initial : R) (move : RotationMove)
    (certificateRest : Word) (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (machineRepresentedInTime caller initial move certificateRest oldPath s saved suffix regs ctx).steps =
      representedSteps move oldPath s saved := rfl

/-- Branch-explicit initializer timing carries the same actual tick count. -/
def machineInitResultInTime (initial : R) (raw : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw)
      (some (cfg (some (resultLabel (initOutcome raw))) (initialRegisters initial)
        (initData raw) (fun _ => []))) (initClock raw) where
  steps := initClock raw
  evals_in_steps := (machine_init_first_result caller initial raw).2.1
  steps_le_m := Nat.le_refl _

@[simp] theorem machineInitResultInTime_steps (initial : R) (raw : Word) :
    (machineInitResultInTime caller initial raw).steps = initClock raw := rfl

end MoveApplyPackageRepresented

/-! ## Space contracts for the actual finite package -/

section MoveApplyPackageSpace

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

theorem machine_prefix_space (initial : R) (start : Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ remainingSteps start) (reached : Cfg Γ Λ R)
    (executed : (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
      (some start) = some reached) : stackCells reached ≤ potential start :=
  prefix_stackCells_le_dirty caller start n bound reached executed

/-- Every real initializer prefix, including the live final result, fits the input length. -/
theorem machine_init_space (initial : R) (raw : Word) (n : Nat)
    (bound : n ≤ initClock raw) (reached : Cfg Γ Λ R)
    (executed : (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
      (some (Turing.initList (machine caller initial) raw)) = some reached) :
    stackCells reached ≤ raw.length := by
  rw [initList_eq] at executed
  have bounded : n ≤ remainingSteps
      (cfg (some (phaseLabel (Λ := Λ) (movePhase .start))) (initialRegisters initial)
        { certificate := raw } (fun k : K => ([] : List (Γ k)))) := by
    change n ≤ runSteps raw [] [] [] [] []
    rwa [initClock_eq]
  have mass := prefix_stackCells_le_dirty caller
    (cfg (some (phaseLabel (movePhase .start))) (initialRegisters initial)
      { certificate := raw } (fun _ => [])) n bounded reached executed
  rw [potential_phase_cfg] at mass
  simpa [localCells, phaseDebt, phaseCredit, movePhase, MoveParserMachine.phaseDebt,
    contextCells] using mass

@[simp] theorem machineInitInTimeExact_steps_clock (initial : R) (raw : Word) :
    (machineInitInTimeExact caller initial raw).steps = initClock raw :=
  initClock_eq raw

theorem machine_principal_prefix_space (initial : R) (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ runSteps raw path source saved scratch pending)
    (reached : Cfg Γ Λ R)
    (executed : (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
      (some (entry regs raw path source saved scratch pending ctx)) = some reached) :
    stackCells reached ≤ principalCells raw path source saved scratch pending ctx + source.length :=
  prefix_stackCells_le caller raw path source saved scratch pending regs ctx n bound reached executed

theorem machine_principal_prefix_space_of_none (initial : R) (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (failed : (parseMoveRun raw).1 = none)
    (n : Nat) (bound : n ≤ runSteps raw path source saved scratch pending) (reached : Cfg Γ Λ R)
    (executed : (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
      (some (entry regs raw path source saved scratch pending ctx)) = some reached) :
    stackCells reached ≤ principalCells raw path source saved scratch pending ctx :=
  prefix_stackCells_le_of_none caller raw path source saved scratch pending regs ctx failed n bound reached executed

theorem machine_principal_prefix_space_of_some (initial : R) (raw : Word) (move : RotationMove)
    (rest : Word) (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (parsed : (parseMoveRun raw).1 = some (move, rest))
    (n : Nat) (bound : n ≤ runSteps raw path source saved scratch pending) (reached : Cfg Γ Λ R)
    (executed : (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
      (some (entry regs raw path source saved scratch pending ctx)) = some reached) :
    stackCells reached ≤ max (principalCells raw path source saved scratch pending ctx)
      (parsedCellsBound move rest path source saved scratch pending ctx) :=
  prefix_stackCells_le_of_some caller raw move rest path source saved scratch pending regs ctx parsed
    n bound reached executed

end MoveApplyPackageSpace

/-! ## One-call space specialization of actual successful FrontEnd physical data -/

section FrontEndPhysicalSpace

variable [Fintype K]

theorem frontEnd_success_prefix_space
    (physicalCaller : External Λ → Statement (frontEndProtectedAlphabet Γ) Λ
      (OpenDecoderMachine.Temporaries × R))
    (regs : FrontEndMachine.Registers (Option Branch × R))
    (source target : BinaryTree Unit) (fuel : List Bool) (cert : Word)
    (ctx : ∀ k, List (Γ k)) (n : Nat)
    (bound : n ≤ phaseSteps (movePhase .start) (frontEndSuccessData source cert [] []))
    (reached : Cfg (frontEndProtectedAlphabet Γ) Λ (OpenDecoderMachine.Temporaries × R))
    (executed : (next physicalCaller)^[n]
      (some (cfg (some (moveLabel .start))
        (frontEndRegisterEquiv (FrontEndMachine.reset regs))
        (frontEndSuccessData source cert [] []) (frontEndSuccessContext target fuel ctx))) = some reached) :
    stackCells reached ≤ cert.length + 2 * (treeCode source).length +
      (treeCode target).length + fuel.length + ∑ k, (ctx k).length := by
  have mass := prefix_stackCells_le_dirty physicalCaller
    (cfg (some (phaseLabel (movePhase .start)))
      (frontEndRegisterEquiv (FrontEndMachine.reset regs))
      (frontEndSuccessData source cert [] []) (frontEndSuccessContext target fuel ctx))
    n bound reached executed
  rw [potential_phase_cfg] at mass
  change stackCells reached ≤ localCells (frontEndSuccessData source cert [] []) +
    phaseDebt (movePhase .start) + phaseCredit (movePhase .start) (frontEndSuccessData source cert [] []) +
    (∑ k, (frontEndSuccessContext target fuel ctx k).length) at mass
  rw [frontEnd_success_context_cells] at mass
  simp only [localCells, frontEndSuccessData, phaseDebt, phaseCredit, movePhase,
    MoveParserMachine.phaseDebt, List.length_nil, Nat.add_zero] at mass
  omega

end FrontEndPhysicalSpace


end Resources.RotationCertificate.MoveApplyMachine
