import Applications.Resources.RotationCertificate.MoveApplyMachine.Package

/-!
# MoveApplyMachine: Installation
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.MoveApplyMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-! ## Further installation through complete carrier equivalences -/

section FurtherInstallation

variable {K' Λ' R' : Type} {Γ' : K' → Type} [DecidableEq K']
variable (names : StackId K ≃ K') (symbols : ∀ k, Alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')

def installedCfg (c : Cfg Γ Λ R) : Turing.TM2.Cfg Γ' Λ' R' :=
  FrontEndMachine.Transport.cfg names symbols registers labels c

omit [DecidableEq K] [DecidableEq K'] in
theorem installedCfg_injective :
    Function.Injective (installedCfg names symbols registers labels) :=
  FrontEndMachine.Transport.cfg_injective names symbols registers labels labels.injective

/-- Every owned body, including each paid dispatch, must be literally installed. -/
theorem installed_owned_prefix
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) := by
  apply FrontEndMachine.Transport.iterate_owned names symbols registers labels
    (program caller) ambient Owned installed n start
  intro j strict
  obtain ⟨reached, executed, _, _, ownership⟩ := owned_prefix caller start j (by omega)
  exact ⟨reached, executed, ownership.mp (by omega)⟩

def installedOwnedTimed
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start)
      (some (installedCfg names symbols registers labels (finalCfg start)))
      (remainingSteps start) where
  steps := remainingSteps start
  evals_in_steps := by
    change (FrontEndMachine.Transport.next ambient)^[remainingSteps start]
      (some (installedCfg names symbols registers labels start)) = _
    rw [installed_owned_prefix caller names symbols registers labels ambient installed start
      (remainingSteps start) (Nat.le_refl _), cfg_iterate caller start]
    rfl
  steps_le_m := Nat.le_refl _

@[simp] theorem installedOwnedTimed_steps
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) :
    (installedOwnedTimed caller names symbols registers labels ambient installed start).steps =
      remainingSteps start := rfl

def installedOwnedPrefixTimed
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
    rw [installed_owned_prefix caller names symbols registers labels ambient installed start n bound, executed]
    rfl
  steps_le_m := Nat.le_refl _

/-- Arbitrary later iterations require agreement on every label, including callers. -/
theorem installed_iterate
    (installed : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (n : Nat) (start : Option (Cfg Γ Λ R)) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (start.map (installedCfg names symbols registers labels)) =
      ((next caller)^[n] start).map (installedCfg names symbols registers labels) :=
  FrontEndMachine.Transport.iterate names symbols registers labels (program caller) ambient installed n start

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
    (installedTimed caller names symbols registers labels ambient installed start final bound run).steps =
      run.steps := rfl

omit [DecidableEq K] [DecidableEq K'] in
theorem installed_stack_cells [Fintype K] [Fintype K'] (c : Cfg Γ Λ R) :
    ∑ k, ((installedCfg names symbols registers labels c).stk k).length = stackCells c :=
  FrontEndMachine.Transport.stackEquiv_total_length names symbols c.stk

theorem installed_owned_prefix_space [Fintype K] [Fintype K']
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = some reached) :
    ∑ k, (reached.stk k).length ≤ potential start := by
  obtain ⟨before, run, _, _, _⟩ := owned_prefix caller start n bound
  have mapped := installed_owned_prefix caller names symbols registers labels ambient installed start n bound
  rw [run, Option.map_some, executed] at mapped
  have same := Option.some.inj mapped
  rw [same, installed_stack_cells]
  exact prefix_stackCells_le_dirty caller start n bound before run

end FurtherInstallation

/-! ## Principal exact timing and sharper physical bounds after complete installation -/

section InstalledPrincipal

variable {K' Λ' R' : Type} {Γ' : K' → Type} [DecidableEq K']
variable (names : StackId K ≃ K') (symbols : ∀ k, Alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
variable (installed : ∀ label, Owned (some label) → ambient (labels label) =
  FrontEndMachine.Transport.statement names symbols registers labels (program caller label))

def installedRunInTimeExact (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels (entry regs raw path source saved scratch pending ctx))
      (some (installedCfg names symbols registers labels
        (runResult regs raw path source saved scratch pending ctx)))
      (runSteps raw path source saved scratch pending) :=
  installedOwnedTimed caller names symbols registers labels ambient installed
    (entry regs raw path source saved scratch pending ctx)

def installedRunInLinearTime (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels (entry regs raw path source saved scratch pending ctx))
      (some (installedCfg names symbols registers labels
        (runResult regs raw path source saved scratch pending ctx)))
      (3 * raw.length + 3 * source.length + saved.length + scratch.length +
        pending.length + path.length + 3) where
  steps := runSteps raw path source saved scratch pending
  evals_in_steps := (installedRunInTimeExact caller names symbols registers labels ambient installed
    raw path source saved scratch pending regs ctx).evals_in_steps
  steps_le_m := runSteps_le raw path source saved scratch pending

def installedParsedRunInLinearTime (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels (entry regs raw path source saved scratch pending ctx))
      (some (installedCfg names symbols registers labels
        (runResult regs raw path source saved scratch pending ctx)))
      (3 * source.length + saved.length + scratch.length + pending.length +
        3 * move.position.length + path.length + 9) where
  steps := runSteps raw path source saved scratch pending
  evals_in_steps := (installedRunInTimeExact caller names symbols registers labels ambient installed
    raw path source saved scratch pending regs ctx).evals_in_steps
  steps_le_m := runSteps_le_of_some raw move rest path source saved scratch pending parsed

def installedRepresentedInTime (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels
        (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx))
      (some (installedCfg names symbols registers labels
        (cfg (some (resultLabel (representedResult move oldPath s))) (reset regs)
          (representedFinalData move certificateRest oldPath s saved suffix) ctx)))
      (representedSteps move oldPath s saved) := by
  have bounded : representedSteps move oldPath s saved ≤ remainingSteps
      (entry (Λ := Λ) regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx) := by
    change representedSteps move oldPath s saved ≤
      runSteps (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] []
    rw [(represented_run_data caller move certificateRest oldPath s saved suffix regs ctx).1]
  exact installedOwnedPrefixTimed caller names symbols registers labels ambient installed
    (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)
    (representedSteps move oldPath s saved) bounded _
    (run_code_represented caller move certificateRest oldPath s saved suffix regs ctx)

variable [Fintype K] [Fintype K']

include installed in
/-- The same reached source state proves the installed physical sum bound. -/
theorem installed_prefix_cells_of_source_bound (start : Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ remainingSteps start) (budget : Nat)
    (sourceBound : ∀ before, (next caller)^[n] (some start) = some before → stackCells before ≤ budget)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = some reached) :
    ∑ k, (reached.stk k).length ≤ budget := by
  obtain ⟨before, run, _, _, _⟩ := owned_prefix caller start n bound
  have mapped := installed_owned_prefix caller names symbols registers labels ambient installed start n bound
  rw [run, Option.map_some, executed] at mapped
  rw [Option.some.inj mapped, installed_stack_cells]
  exact sourceBound before run

include installed in
theorem installed_prefix_stackCells_le (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ runSteps raw path source saved scratch pending)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels
        (entry regs raw path source saved scratch pending ctx))) = some reached) :
    ∑ k, (reached.stk k).length ≤ principalCells raw path source saved scratch pending ctx + source.length :=
  installed_prefix_cells_of_source_bound caller names symbols registers labels ambient installed
    (entry regs raw path source saved scratch pending ctx) n bound _
    (fun before run => prefix_stackCells_le caller raw path source saved scratch pending regs ctx
      n bound before run) reached executed

include installed in
theorem installed_prefix_stackCells_le_of_none (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (failed : (parseMoveRun raw).1 = none)
    (n : Nat) (bound : n ≤ runSteps raw path source saved scratch pending)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels
        (entry regs raw path source saved scratch pending ctx))) = some reached) :
    ∑ k, (reached.stk k).length ≤ principalCells raw path source saved scratch pending ctx :=
  installed_prefix_cells_of_source_bound caller names symbols registers labels ambient installed
    (entry regs raw path source saved scratch pending ctx) n bound _
    (fun before run => prefix_stackCells_le_of_none caller raw path source saved scratch pending regs ctx
      failed n bound before run) reached executed

include installed in
theorem installed_prefix_stackCells_le_of_some (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (parsed : (parseMoveRun raw).1 = some (move, rest))
    (n : Nat) (bound : n ≤ runSteps raw path source saved scratch pending)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels
        (entry regs raw path source saved scratch pending ctx))) = some reached) :
    ∑ k, (reached.stk k).length ≤ max (principalCells raw path source saved scratch pending ctx)
      (parsedCellsBound move rest path source saved scratch pending ctx) :=
  installed_prefix_cells_of_source_bound caller names symbols registers labels ambient installed
    (entry regs raw path source saved scratch pending ctx) n bound _
    (fun before run => prefix_stackCells_le_of_some caller raw move rest path source saved scratch pending
      regs ctx parsed n bound before run) reached executed

end InstalledPrincipal

end Resources.RotationCertificate.MoveApplyMachine
