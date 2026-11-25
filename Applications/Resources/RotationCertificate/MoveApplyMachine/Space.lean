import Applications.Resources.RotationCertificate.MoveApplyMachine.Execution

/-!
# MoveApplyMachine: Space
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.MoveApplyMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

section PhysicalSpace
variable [Fintype K]

def contextCells (ctx : ∀ k, List (Γ k)) : Nat := ∑ k, (ctx k).length

/-- A genuine sum over the seven local indices and every protected physical index. -/
def stackCells (c : Cfg Γ Λ R) : Nat := ∑ k : StackId K, (c.stk k).length

omit [DecidableEq K] in
theorem stackCells_eq_sum (c : Cfg Γ Λ R) :
    stackCells c = ∑ k : StackId K, (c.stk k).length := rfl

theorem localStack_sum (f : LocalStack → Nat) :
    ∑ k, f k = f .certificate + f .moveReverse + f .path + f .source +
      f .saved + f .scratch + f .pending := by
  change (∑ k ∈ ({.certificate, .moveReverse, .path, .source, .saved, .scratch, .pending} : Finset LocalStack), f k) = _
  simp [Nat.add_comm, Nat.add_left_comm]

omit [DecidableEq K] in
theorem stackCells_cfg (label : Option (Label Λ)) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg label regs D ctx) = localCells D + contextCells ctx := by
  rw [stackCells, Fintype.sum_sum_type, localStack_sum]
  rfl

omit [DecidableEq K] in
theorem stackCells_moveCfg (c : MoveCfg Γ Λ R) :
    stackCells (moveCfg c) = MoveParserMachine.stackCells c := by
  rw [MoveParserMachine.stackCells_eq_sum]
  exact FrontEndMachine.Transport.stackEquiv_total_length moveStackEquiv moveSymbolEquiv c.stk

omit [DecidableEq K] in
theorem stackCells_positionCfg (c : PositionCfg Γ Λ R) :
    stackCells (positionCfg c) = PositionedRotationMachine.stackCells c :=
  FrontEndMachine.Transport.stackEquiv_total_length positionStackEquiv positionSymbolEquiv c.stk

omit [DecidableEq K] in
theorem moveContext_cells (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    MoveParserMachine.contextCells (moveContext D ctx) =
      D.source.length + D.saved.length + D.scratch.length + D.pending.length + contextCells ctx := by
  have localSum (f : MoveProtected → Nat) :
      ∑ k, f k = f .source + f .saved + f .scratch + f .pending := by
    change (∑ k ∈ ({.source, .saved, .scratch, .pending} : Finset MoveProtected), f k) = _
    simp [Nat.add_comm, Nat.add_left_comm]
  rw [MoveParserMachine.contextCells, Fintype.sum_sum_type, localSum]
  rfl

omit [DecidableEq K] in
theorem positionContext_cells (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    PositionedRotationMachine.contextCells (positionContext D ctx) =
      D.certificate.length + D.moveReverse.length + contextCells ctx := by
  have localSum (f : PositionProtected → Nat) : ∑ k, f k = f .certificate + f .moveReverse := by
    change (∑ k ∈ ({.certificate, .moveReverse} : Finset PositionProtected), f k) = _
    simp
  rw [PositionedRotationMachine.contextCells, Fintype.sum_sum_type, localSum]
  rfl

def potential (c : Cfg Γ Λ R) : Nat := stackCells c + debt c.l + credit c

omit [DecidableEq K] in
theorem potential_phase_cfg (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    potential (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) =
      localCells D + phaseDebt q + phaseCredit q D + contextCells ctx := by
  rw [potential, stackCells_cfg]
  cases D
  cases q with
  | inl q => simp only [phaseLabel, moveLabel, cfg, debt, credit, dataOfCfg, movePhase]; omega
  | inr q => cases q <;>
      simp only [phaseLabel, dispatchLabel, positionLabel, cfg, debt, credit, dataOfCfg,
        dispatchPhase, positionPhase] <;> omega

omit [DecidableEq K] in
theorem potential_result_cfg (r : FinalResult) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    potential (cfg (some (resultLabel (Λ := Λ) r)) regs D ctx) = localCells D + contextCells ctx := by
  rw [potential, stackCells_cfg]
  rfl

omit [DecidableEq K] in
theorem potential_position_control_cfg (control : PositionedRotationMachine.Control)
    (regs : Registers R) (D : LocalData) (E : PositionedRotationMachine.LocalData)
    (ctx : ∀ k, List (Γ k)) :
    potential (cfg (some (positionControlLabel (Λ := Λ) control)) regs (setPositionData D E) ctx) =
      PositionedRotationMachine.localPotential control E + D.certificate.length + D.moveReverse.length +
        contextCells ctx := by
  cases control with
  | inl q =>
      change potential (cfg (some (phaseLabel (positionPhase q))) regs (setPositionData D E) ctx) = _
      rw [potential_phase_cfg]
      simp only [phaseDebt, positionPhase, phaseCredit, positionData_setPositionData]
      simp only [localCells, setPositionData, PositionedRotationMachine.localPotential,
        PositionedRotationMachine.localCells, PositionedRotationMachine.controlDebt,
        PositionedRotationMachine.controlCredit]
      omega
  | inr r =>
      rw [positionControlLabel, potential_result_cfg]
      simp only [localCells, setPositionData, PositionedRotationMachine.localPotential,
        PositionedRotationMachine.localCells, PositionedRotationMachine.controlDebt,
        PositionedRotationMachine.controlCredit]
      omega

omit [DecidableEq K] in
theorem potential_moveCfg (c : MoveCfg Γ Λ R) (boundary : MoveBoundary c.l) :
    potential (moveCfg c) = MoveParserMachine.potential c +
      MoveParserMachine.contextCells (fun k => c.stk (.inr k)) +
        (c.stk (.inr (.inl .source))).length := by
  have debtEq : debt (moveCfg c).l = MoveParserMachine.debt c.l := by
    rw [moveCfg_label]
    rcases boundary with owned | ⟨r, returned⟩
    · cases labelEq : c.l with
      | none => simp only [labelEq, MoveParserMachine.Owned] at owned
      | some label => cases label with
        | inl q => rfl
        | inr external => simp only [labelEq, MoveParserMachine.Owned] at owned
    · rw [returned]
      cases r <;> rfl
  have creditEq : credit (moveCfg c) = (c.stk (.inr (.inl .source))).length := by
    have sourceEq := congrArg List.length (moveCfg_source c)
    rcases boundary with owned | ⟨r, returned⟩
    · cases labelEq : c.l with
      | none => simp only [labelEq, MoveParserMachine.Owned] at owned
      | some label => cases label with
        | inl q =>
            unfold credit
            rw [moveCfg_label, labelEq]
            exact sourceEq
        | inr external => simp only [labelEq, MoveParserMachine.Owned] at owned
    · unfold credit
      rw [moveCfg_label, returned]
      exact sourceEq
  rw [potential, stackCells_moveCfg, debtEq, creditEq]
  unfold MoveParserMachine.stackCells MoveParserMachine.potential
  omega

theorem move_step_potential
    (localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R)
    (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : MoveParserMachine.Registers (MoveCallerRegister R)) (ctx : ∀ k, List (Γ k))
    (after : MoveCfg Γ Λ R)
    (executed : MoveParserMachine.step localCaller
      (moveView (some (MoveParserMachine.phaseLabel q)) regs D ctx) = some after) :
    potential (moveCfg after) =
      potential (moveCfg (Λ := Λ) (moveView (some (MoveParserMachine.phaseLabel q)) regs D ctx)) := by
  obtain ⟨_, _, frame, mass⟩ := MoveParserMachine.local_step_data localCaller
      (before := moveView (some (MoveParserMachine.phaseLabel q)) regs D ctx) ⟨True.intro, executed⟩
  rw [potential_moveCfg after (move_step_boundary localCaller q D regs ctx after executed),
    potential_moveCfg (moveView (Λ := Λ) (some (MoveParserMachine.phaseLabel q)) regs D ctx)
      (.inl True.intro), mass, funext frame, frame (.inl .source)]

omit [DecidableEq K] in
theorem dispatch_success_potential (d : RotationDirection) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    potential (cfg (some (dispatchLabel (Λ := Λ) (.success d))) regs D ctx) =
      potential (cfg (some (positionLabel (Λ := Λ) (.seek d))) (reset regs) D ctx) + 2 := by
  change potential (cfg (some (phaseLabel (dispatchPhase (.success d)))) regs D ctx) =
    potential (cfg (some (phaseLabel (positionPhase (.seek d)))) (reset regs) D ctx) + 2
  rw [potential_phase_cfg, potential_phase_cfg]
  simp only [phaseDebt, dispatchPhase, positionPhase, phaseCredit, PositionedRotationMachine.phaseDebt,
    PositionedRotationMachine.phaseCredit, positionData]
  omega

omit [DecidableEq K] in
theorem dispatch_failure_potential (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    potential (cfg (some (dispatchLabel (Λ := Λ) .failure)) regs D ctx) =
      potential (cfg (some (resultLabel (Λ := Λ) parseFailure)) (reset regs) D ctx) + D.source.length := by
  change potential (cfg (some (phaseLabel (dispatchPhase .failure))) regs D ctx) = _
  rw [potential_phase_cfg, potential_result_cfg]
  simp only [phaseDebt, dispatchPhase, phaseCredit]
  omega

theorem local_step_potential_le {before after : Cfg Γ Λ R} (transition : LocalStep caller before after) :
    potential after ≤ potential before := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before transition.1
  cases q with
  | inl q =>
      let localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R :=
        fun _ => .halt
      let start : MoveCfg Γ Λ R :=
        moveView (some (MoveParserMachine.phaseLabel q)) (moveRegisterEquiv.symm regs) D ctx
      have startEq : moveCfg start = cfg (some (moveLabel q)) regs D ctx := by
        rw [moveCfg_view]
        simp only [Option.map_some, moveLabelEquiv_phase, Equiv.apply_symm_apply]
      obtain ⟨middle, localStep, _⟩ := MoveParserMachine.local_progress localCaller start
        ((MoveParserMachine.remainingSteps_pos_iff start).mpr True.intro)
      have moved := move_step_transport caller localCaller start True.intro
      rw [localStep, Option.map_some, startEq] at moved
      have same : after = moveCfg middle := Option.some.inj (transition.2.symm.trans moved)
      have mass := move_step_potential localCaller q D (moveRegisterEquiv.symm regs) ctx middle localStep
      change potential (moveCfg middle) = potential (moveCfg start) at mass
      rw [startEq] at mass
      rw [same]
      exact Nat.le_of_eq mass
  | inr q => cases q with
    | inl r =>
        have same : after = cfg (some (dispatchTarget r)) (reset regs) D ctx :=
          Option.some.inj (transition.2.symm.trans (dispatch_step caller r D regs ctx))
        rw [same]
        cases r with
        | failure => have mass := dispatch_failure_potential (Λ := Λ) D regs ctx; exact Nat.le.intro mass.symm
        | success d => have mass := dispatch_success_potential (Λ := Λ) d D regs ctx; exact Nat.le.intro mass.symm
    | inr q =>
        have same := Option.some.inj ((position_advance_step caller q D regs ctx).symm.trans transition.2)
        subst after
        change potential (cfg (some (positionControlLabel
          (PositionedRotationMachine.advance q (positionData D)).1)) (reset regs)
            (setPositionData D (PositionedRotationMachine.advance q (positionData D)).2) ctx) ≤
          potential (cfg (some (positionControlLabel (.inl q))) regs D ctx)
        have beforeEq : potential (cfg (some (positionControlLabel (Λ := Λ) (.inl q))) regs D ctx) =
            PositionedRotationMachine.localPotential (.inl q) (positionData D) +
              D.certificate.length + D.moveReverse.length + contextCells ctx := by
          simpa only [setPositionData_positionData] using
            potential_position_control_cfg (Λ := Λ) (.inl q) regs D (positionData D) ctx
        rw [potential_position_control_cfg, beforeEq]
        exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
          (PositionedRotationMachine.advance_mass q (positionData D)).2 D.certificate.length)
          D.moveReverse.length) (contextCells ctx)

theorem local_reaches_potential_le {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) : potential reached ≤ potential start := by
  induction path with
  | refl => exact Nat.le_refl _
  | @tail before after _ transition ih => exact (local_step_potential_le caller transition).trans ih

omit [DecidableEq K] in
theorem stackCells_le_potential (c : Cfg Γ Λ R) : stackCells c ≤ potential c := by
  unfold potential
  omega

theorem prefix_potential_le (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    potential reached ≤ potential start := by
  obtain ⟨actual, run, _, path, _⟩ := owned_prefix caller start n bound
  have same : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  exact local_reaches_potential_le caller path

theorem prefix_stackCells_le_dirty (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    stackCells reached ≤ potential start :=
  (stackCells_le_potential reached).trans (prefix_potential_le caller start n bound reached executed)

/-- Every clause refers to the same actual inclusive-prefix configuration. -/
theorem owned_prefix_space (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
      stackCells reached ≤ potential reached ∧ potential reached ≤ potential start := by
  obtain ⟨reached, executed, rank, path, ownership, zero, registers, frame⟩ :=
    owned_prefix_frame caller start n bound
  exact ⟨reached, executed, rank, path, ownership, zero, registers, frame,
    stackCells_le_potential reached, local_reaches_potential_le caller path⟩

end PhysicalSpace


end Resources.RotationCertificate.MoveApplyMachine
