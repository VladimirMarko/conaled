import Applications.Resources.RotationCertificate.StreamMachine.Execution

/-!
# StreamMachine: Space
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.StreamMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

omit [DecidableEq K] in
def localCells (D : LocalData) : Nat := D.certificate.length + D.moveReverse.length + D.path.length +
  D.source.length + D.saved.length + D.scratch.length + D.units.length + D.fuel.length + D.target.length

section PhysicalSpace
variable [Fintype K]

omit [DecidableEq K] in
def contextCells (ctx : ∀ k, List (Γ k)) : Nat := ∑ k, (ctx k).length

omit [DecidableEq K] in
def mass (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat := localCells D + contextCells ctx

omit [DecidableEq K] in
def stackCells (c : Cfg Γ Λ R) : Nat := ∑ k : StackId K, (c.stk k).length

omit [DecidableEq K] in
theorem stackCells_eq_sum (c : Cfg Γ Λ R) :
    stackCells c = ∑ k : StackId K, (c.stk k).length := rfl

omit [DecidableEq K] in
theorem localStack_sum (f : LocalStack → Nat) :
    ∑ k, f k = f .certificate + f .moveReverse + f .path + f .source +
      f .saved + f .scratch + f .units + f .fuel + f .target := by
  change (∑ k ∈ ({.certificate, .moveReverse, .path, .source, .saved, .scratch,
    .units, .fuel, .target} : Finset LocalStack), f k) = _
  simp [Nat.add_comm, Nat.add_left_comm]

omit [DecidableEq K] in
theorem stackCells_cfg (label : Option (Label Λ)) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : stackCells (cfg label regs D ctx) = mass D ctx := by
  rw [stackCells, Fintype.sum_sum_type, localStack_sum]
  rfl

omit [DecidableEq K] in
theorem stackCells_applyCfg (c : ApplyCfg Γ Λ R) :
    stackCells (applyCfg c) = MoveApplyMachine.stackCells c :=
  FrontEndMachine.Transport.stackEquiv_total_length applyStackEquiv applySymbolEquiv c.stk

omit [DecidableEq K] in
theorem stackCells_equalityCfg (c : EqualityCfg Γ Λ R) :
    stackCells (equalityCfg c) = TreeEqualityMachine.stackCells c := by
  rw [TreeEqualityMachine.stackCells_eq_sum]
  exact FrontEndMachine.Transport.stackEquiv_total_length equalityStackEquiv equalitySymbolEquiv c.stk

omit [DecidableEq K] in
theorem fuelStackCells_eq_sum (c : FuelCfg Γ Λ R) :
    FuelDispatchMachine.stackCells c = ∑ k, (c.stk k).length := by
  rw [Fintype.sum_sum_type]
  have localSum (f : Resources.BinaryCounter.FixedWidthMachine.LocalStack → Nat) : ∑ k, f k = f .fuel + f .borrowed := by
    change (∑ k ∈ ({.fuel, .borrowed} : Finset Resources.BinaryCounter.FixedWidthMachine.LocalStack), f k) = _
    simp
  rw [localSum]
  rfl

omit [DecidableEq K] in
theorem stackCells_fuelCfg (c : FuelCfg Γ Λ R) :
    stackCells (fuelCfg c) = FuelDispatchMachine.stackCells c := by
  rw [fuelStackCells_eq_sum]
  exact FrontEndMachine.Transport.stackEquiv_total_length fuelStackEquiv fuelSymbolEquiv c.stk

omit [DecidableEq K] in
theorem applyContext_cells (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    MoveApplyMachine.contextCells (applyContext D ctx) = D.fuel.length + D.target.length + contextCells ctx := by
  have localSum (f : ApplyProtected → Nat) : ∑ k, f k = f .fuel + f .target := by
    change (∑ k ∈ ({.fuel, .target} : Finset ApplyProtected), f k) = _
    simp
  rw [MoveApplyMachine.contextCells, Fintype.sum_sum_type, localSum]
  rfl

omit [DecidableEq K] in
def hAllowance (q : MoveApplyMachine.Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat :=
  mass D ctx + MoveApplyMachine.phaseDebt q + MoveApplyMachine.phaseCredit q (applyData D)

omit [DecidableEq K] in
theorem hAllowance_eq_potential (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    hAllowance q D ctx = MoveApplyMachine.potential
      (applyView (Λ := Λ) (some (MoveApplyMachine.phaseLabel q)) (applyRegisterEquiv.symm regs) D ctx) := by
  change hAllowance q D ctx = MoveApplyMachine.potential
    (MoveApplyMachine.cfg (some (MoveApplyMachine.phaseLabel q)) (applyRegisterEquiv.symm regs)
      (applyData D) (applyContext D ctx))
  rw [MoveApplyMachine.potential_phase_cfg, applyContext_cells]
  simp only [hAllowance, mass, localCells, MoveApplyMachine.localCells, applyData]
  omega

omit [DecidableEq K] in
def inspectAllowance (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat :=
  if D.certificate = [] then mass D ctx else
    let fuel := counterFinish .borrow D
    match fuel.result with
    | .zero => mass D ctx
    | .positive =>
        let applied := applyFinish (MoveApplyMachine.movePhase .start) fuel.data
        match _returned : applied.result with
        | .inl _ | .inr .failure => max (mass D ctx) (hAllowance (MoveApplyMachine.movePhase .start) fuel.data ctx)
        | .inr .success =>
            max (mass D ctx) (max (hAllowance (MoveApplyMachine.movePhase .start) fuel.data ctx)
              (inspectAllowance applied.data ctx))
termination_by D.certificate.length
decreasing_by
  simpa only [counterFinish_certificate] using
    apply_start_certificate_lt (counterFinish .borrow D).data _returned

omit [DecidableEq K] in
def hJoinAllowance (r : MoveApplyMachine.FinalResult) (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat :=
  match r with
  | .inl _ | .inr .failure => mass D ctx
  | .inr .success => max (mass D ctx) (inspectAllowance D ctx)

omit [DecidableEq K] in
def hPhaseAllowance (q : MoveApplyMachine.Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat :=
  max (hAllowance q D ctx) (hJoinAllowance (applyFinish q D).result (applyFinish q D).data ctx)

omit [DecidableEq K] in
def fuelJoinAllowance (r : FuelDispatchMachine.Exit) (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat :=
  match r with
  | .atEnd | .zero => mass D ctx
  | .positive => max (mass D ctx) (hPhaseAllowance (MoveApplyMachine.movePhase .start) D ctx)

omit [DecidableEq K] in
def counterAllowance (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat :=
  max (mass D ctx) (fuelJoinAllowance (FuelDispatchMachine.exitOfResult (counterFinish q D).result) (counterFinish q D).data ctx)

omit [DecidableEq K] in
def phaseAllowance (q : Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat :=
  match q with
  | .inl (.inl q) => counterAllowance q D ctx
  | .inl (.inr (.inl r)) => fuelJoinAllowance (FuelDispatchMachine.exitOfResult r) D ctx
  | .inl (.inr (.inr (.inl .inspectCertificate))) => inspectAllowance D ctx
  | .inl (.inr (.inr (.inl .atEnd))) => fuelJoinAllowance .atEnd D ctx
  | .inl (.inr (.inr (.inr impossible))) => Empty.elim impossible
  | .inr (.inl (.inl q)) => hPhaseAllowance (MoveApplyMachine.movePhase q) D ctx
  | .inr (.inl (.inr (.inl r))) => hPhaseAllowance (MoveApplyMachine.dispatchPhase r) D ctx
  | .inr (.inl (.inr (.inr (.inl q)))) => hPhaseAllowance (MoveApplyMachine.positionPhase q) D ctx
  | .inr (.inl (.inr (.inr (.inr (.inl r))))) => hJoinAllowance r D ctx
  | .inr (.inl (.inr (.inr (.inr (.inr impossible))))) => Empty.elim impossible
  | .inr (.inr (.inl .compare)) => mass D ctx
  | .inr (.inr (.inr (.inl _))) => mass D ctx
  | .inr (.inr (.inr (.inr impossible))) => Empty.elim impossible

omit [DecidableEq K] in
def allowance (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl q) => phaseAllowance (.inl q) (dataOfCfg c) (contextOfCfg c)
  | some (.inr (.inl q)) => phaseAllowance (.inr (.inl q)) (dataOfCfg c) (contextOfCfg c)
  | some (.inr (.inr (.inl q))) => phaseAllowance (.inr (.inr q)) (dataOfCfg c) (contextOfCfg c)
  | _ => stackCells c

omit [DecidableEq K] in
theorem allowance_phase_cfg (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    allowance (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) = phaseAllowance q D ctx := by
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl

omit [DecidableEq K] in
theorem mass_le_hAllowance (q : MoveApplyMachine.Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    mass D ctx ≤ hAllowance q D ctx := by unfold hAllowance; omega

omit [DecidableEq K] in
theorem mass_le_inspectAllowance (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    mass D ctx ≤ inspectAllowance D ctx := by
  rw [inspectAllowance]
  split
  · exact Nat.le_refl _
  · dsimp only
    split
    · exact Nat.le_refl _
    · split <;> exact Nat.le_max_left _ _

omit [DecidableEq K] in
theorem mass_le_hJoinAllowance (r : MoveApplyMachine.FinalResult) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    mass D ctx ≤ hJoinAllowance r D ctx := by
  cases r with
  | inl u => exact Nat.le_refl _
  | inr r => cases r with
    | failure => exact Nat.le_refl _
    | success => exact Nat.le_max_left _ _

omit [DecidableEq K] in
theorem mass_le_hPhaseAllowance (q : MoveApplyMachine.Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    mass D ctx ≤ hPhaseAllowance q D ctx :=
  (mass_le_hAllowance q D ctx).trans (Nat.le_max_left _ _)

omit [DecidableEq K] in
theorem mass_le_fuelJoinAllowance (r : FuelDispatchMachine.Exit) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    mass D ctx ≤ fuelJoinAllowance r D ctx := by
  cases r with
  | atEnd | zero => exact Nat.le_refl _
  | positive => exact Nat.le_max_left _ _

omit [DecidableEq K] in
theorem mass_le_phaseAllowance (q : Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    mass D ctx ≤ phaseAllowance q D ctx := by
  rcases q with fuel | (applied | equality)
  · rcases fuel with q | (r | (d | impossible))
    · exact Nat.le_max_left _ _
    · exact mass_le_fuelJoinAllowance _ D ctx
    · cases d with
      | inspectCertificate => exact mass_le_inspectAllowance D ctx
      | atEnd => exact Nat.le_refl _
    · exact Empty.elim impossible
  · rcases applied with q | (r | (q | (r | impossible)))
    · exact mass_le_hPhaseAllowance _ D ctx
    · exact mass_le_hPhaseAllowance _ D ctx
    · exact mass_le_hPhaseAllowance _ D ctx
    · exact mass_le_hJoinAllowance r D ctx
    · exact Empty.elim impossible
  · rcases equality with q | (r | impossible)
    · cases q; exact Nat.le_refl _
    · exact Nat.le_refl _
    · exact Empty.elim impossible

omit [DecidableEq K] in
theorem nonowned_allowance (c : Cfg Γ Λ R) (nonowned : ¬ Owned c.l) : allowance c = stackCells c := by
  cases hLabel : c.l with
  | none => simp only [allowance, hLabel]
  | some l =>
      rcases l with q | (q | (q | external))
      · exact False.elim (nonowned (by simp only [hLabel, Owned]))
      · exact False.elim (nonowned (by simp only [hLabel, Owned]))
      · exact False.elim (nonowned (by simp only [hLabel, Owned]))
      · simp only [allowance, hLabel]

omit [DecidableEq K] in
theorem stackCells_le_allowance (c : Cfg Γ Λ R) : stackCells c ≤ allowance c := by
  by_cases owned : Owned c.l
  · obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases c owned
    rw [stackCells_cfg, allowance_phase_cfg]
    exact mass_le_phaseAllowance q D ctx
  · rw [nonowned_allowance c owned]

/-! ### Actual physical bounds of the complete transported component segments -/

theorem fuel_prefix_stackCells
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (start : FuelCfg Γ Λ R) (n : Nat) (bound : n ≤ FuelDispatchMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (fuelCfg start)) = some reached) :
    stackCells reached = stackCells (fuelCfg start) := by
  obtain ⟨middle, _, path, rfl⟩ := fuel_prefix_lift caller localCaller start n bound reached executed
  rw [stackCells_fuelCfg, stackCells_fuelCfg]
  exact (FuelDispatchMachine.local_reaches_preserves localCaller path).2.2.2

theorem apply_prefix_stackCells_le
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (start : ApplyCfg Γ Λ R) (n : Nat) (bound : n ≤ MoveApplyMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (applyCfg start)) = some reached) :
    stackCells reached ≤ MoveApplyMachine.potential start := by
  obtain ⟨middle, run, _, rfl⟩ := apply_prefix_lift caller localCaller start n bound reached executed
  rw [stackCells_applyCfg]
  exact MoveApplyMachine.prefix_stackCells_le_dirty localCaller start n bound middle run

theorem equality_prefix_stackCells_le
    (localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R)
    (start : EqualityCfg Γ Λ R) (n : Nat) (bound : n ≤ TreeEqualityMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (equalityCfg start)) = some reached) :
    stackCells reached ≤ stackCells (equalityCfg start) := by
  obtain ⟨middle, _, path, rfl⟩ := equality_prefix_lift caller localCaller start n bound reached executed
  rw [stackCells_equalityCfg, stackCells_equalityCfg]
  exact (TreeEqualityMachine.local_reaches_preserves localCaller path).2.2

theorem counter_stage_stackCells (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (counterFinish q D).steps)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel (counterPhase q))) regs D ctx)) = some reached) :
    stackCells reached = mass D ctx := by
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  let start : FuelCfg Γ Λ R := fuelView (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel q)) regs D ctx
  have startEq : fuelCfg start = cfg (some (phaseLabel (counterPhase q))) regs D ctx := by
    rw [fuelCfg_view]
    rfl
  have rank : FuelDispatchMachine.remainingSteps start = (counterFinish q D).steps := by cases q <;> rfl
  have cells := fuel_prefix_stackCells caller localCaller start n (by rwa [rank]) reached (by rwa [startEq])
  rwa [startEq, stackCells_cfg] at cells

theorem inspect_stage_stackCells (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (inspectStageFinish D).steps)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel inspectPhase)) regs D ctx)) = some reached) :
    stackCells reached = mass D ctx := by
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  let start : FuelCfg Γ Λ R := fuelView (some FuelDispatchMachine.inspectLabel) regs D ctx
  have startEq : fuelCfg start = cfg (some (phaseLabel inspectPhase)) regs D ctx := by
    rw [fuelCfg_view]
    rfl
  have rank : FuelDispatchMachine.remainingSteps start = (inspectStageFinish D).steps := by
    cases cert : D.certificate with
    | nil => simp only [start, fuelView, FuelDispatchMachine.remainingSteps, FuelDispatchMachine.cfg, Resources.BinaryCounter.FixedWidthMachine.cfg, FuelDispatchMachine.inspectLabel,
        Resources.BinaryCounter.FixedWidthMachine.callerLabel, FuelDispatchMachine.stores, cert, inspectStageFinish]
    | cons a rest =>
        simp only [start, fuelView, FuelDispatchMachine.remainingSteps, FuelDispatchMachine.cfg, Resources.BinaryCounter.FixedWidthMachine.cfg, FuelDispatchMachine.inspectLabel,
          Resources.BinaryCounter.FixedWidthMachine.callerLabel, FuelDispatchMachine.stores, cert, inspectStageFinish, counterFinish]
        omega
  have cells := fuel_prefix_stackCells caller localCaller start n (by rwa [rank]) reached (by rwa [startEq])
  rwa [startEq, stackCells_cfg] at cells

theorem apply_stage_stackCells_le (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (applyFinish q D).steps)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel (applyPhase q))) regs D ctx)) = some reached) :
    stackCells reached ≤ hAllowance q D ctx := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let start : ApplyCfg Γ Λ R := applyView (some (MoveApplyMachine.phaseLabel q)) (applyRegisterEquiv.symm regs) D ctx
  have startEq : applyCfg start = cfg (some (phaseLabel (applyPhase q))) regs D ctx := by
    rw [applyCfg_view]
    simp only [Option.map_some, applyLabelEquiv_phase, Equiv.apply_symm_apply]
  have rank : MoveApplyMachine.remainingSteps start = (applyFinish q D).steps := by
    change MoveApplyMachine.remainingSteps (MoveApplyMachine.cfg _ _ _ _) = _
    rw [MoveApplyMachine.remainingSteps_phase_cfg]
    rfl
  have cells := apply_prefix_stackCells_le caller localCaller start n (by rwa [rank]) reached (by rwa [startEq])
  rwa [← hAllowance_eq_potential q D regs ctx] at cells

theorem equality_stage_stackCells_le (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (equalityFinish D).steps)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel comparePhase)) regs D ctx)) = some reached) :
    stackCells reached ≤ mass D ctx := by
  let localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R := fun _ => .halt
  let start : EqualityCfg Γ Λ R := equalityView (some (TreeEqualityMachine.phaseLabel .compare)) (equalityRegisterEquiv.symm regs) D ctx
  have startEq : equalityCfg start = cfg (some (phaseLabel comparePhase)) regs D ctx := by
    rw [equalityCfg_view]
    simp only [Option.map_some, equalityLabelEquiv_phase, Equiv.apply_symm_apply]
  have rank : TreeEqualityMachine.remainingSteps start = (equalityFinish D).steps := rfl
  have cells := equality_prefix_stackCells_le caller localCaller start n (by rwa [rank]) reached (by rwa [startEq])
  rwa [startEq, stackCells_cfg] at cells

omit [Fintype K] in
/-- Equality's complete store equation, including the exact residual raw words
and every protected store, at each inclusive component prefix. -/
theorem equality_prefix_cfg (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ (equalityFinish D).steps) :
    (next caller)^[n] (some (cfg (some (phaseLabel comparePhase)) regs D ctx)) =
      some (cfg (some (if n < (equalityFinish D).steps then phaseLabel comparePhase
          else phaseLabel (equalityJoinPhase (equalityFinish D).result)))
        (if n = 0 then regs else resetEquality regs)
        { D with source := D.source.drop n, target := D.target.drop n } ctx) := by
  change n ≤ TreeEqualityMachine.runSteps D.source D.target at bound
  let localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R := fun _ => .halt
  let start : EqualityCfg Γ Λ R := equalityView (some (TreeEqualityMachine.phaseLabel .compare)) (equalityRegisterEquiv.symm regs) D ctx
  have startEq : equalityCfg start = cfg (some (phaseLabel comparePhase)) regs D ctx := by
    rw [equalityCfg_view]
    simp only [Option.map_some, equalityLabelEquiv_phase, Equiv.apply_symm_apply]
  have earlier : ∀ j, j < n → ∃ prior,
      (TreeEqualityMachine.next localCaller)^[j] (some start) = some prior ∧ TreeEqualityMachine.Owned prior.l := by
    intro j strict
    obtain ⟨prior, arrived, _, _, live⟩ := TreeEqualityMachine.owned_prefix localCaller start j (by change j ≤ TreeEqualityMachine.runSteps D.source D.target; omega)
    exact ⟨prior, arrived, live.mp (by change j < TreeEqualityMachine.runSteps D.source D.target; omega)⟩
  rw [← startEq, equality_prefix_transport caller localCaller n start earlier]
  have localRun := TreeEqualityMachine.prefix_exact localCaller D.source D.target (equalityRegisterEquiv.symm regs)
    (equalityContext D ctx) n bound
  change (TreeEqualityMachine.next localCaller)^[n] (some start) = _ at localRun
  rw [localRun, Option.map_some]
  unfold TreeEqualityMachine.prefixCfg
  rw [equalityCfg_partial]
  congr 1
  apply cfg_ext
  · change (some (if n < TreeEqualityMachine.runSteps D.source D.target
        then TreeEqualityMachine.phaseLabel .compare
        else TreeEqualityMachine.resultLabel (TreeEqualityMachine.wordResult D.source D.target))).map
        equalityLabelEquiv =
      some (if n < TreeEqualityMachine.runSteps D.source D.target then phaseLabel comparePhase
        else phaseLabel (equalityJoinPhase (TreeEqualityMachine.wordResult D.source D.target)))
    by_cases early : n < TreeEqualityMachine.runSteps D.source D.target
    · simp only [early, ite_true, Option.map_some, equalityLabelEquiv_phase]
    · simp only [early, ite_false, Option.map_some, equalityLabelEquiv_result]
  · change equalityRegisterEquiv (TreeEqualityMachine.prefixRegisters n (equalityRegisterEquiv.symm regs)) =
      if n = 0 then regs else resetEquality regs
    by_cases zero : n = 0
    · simp only [TreeEqualityMachine.prefixRegisters, zero, ite_true, Equiv.apply_symm_apply]
    · simp only [TreeEqualityMachine.prefixRegisters, zero, ite_false,
        equalityRegisterEquiv_reset, Equiv.apply_symm_apply]
  · rfl

theorem equality_prefix_stackCells_exact (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ (equalityFinish D).steps) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel comparePhase)) regs D ctx)) = some reached) :
    stackCells reached =
      mass { D with source := D.source.drop n, target := D.target.drop n } ctx := by
  have same := Option.some.inj (executed.symm.trans (equality_prefix_cfg caller D regs ctx n bound))
  rw [same, stackCells_cfg]

include caller in
theorem counterFinish_mass (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    mass (counterFinish q D).data ctx = mass D ctx := by
  have cells := counter_stage_stackCells caller q D regs ctx (counterFinish q D).steps (Nat.le_refl _)
    _ (LocalRun.iterate caller (counter_phase_localRun caller q D regs ctx))
  rwa [stackCells_cfg] at cells

include caller in
theorem inspectStageFinish_mass (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    mass (inspectStageFinish D).data ctx = mass D ctx := by
  have cells := inspect_stage_stackCells caller D regs ctx (inspectStageFinish D).steps (Nat.le_refl _)
    _ (LocalRun.iterate caller (inspect_stage_localRun caller D regs ctx))
  rwa [stackCells_cfg] at cells

include caller in
theorem applyFinish_mass_le (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    mass (applyFinish q D).data ctx ≤ hAllowance q D ctx := by
  have cells := apply_stage_stackCells_le caller q D regs ctx (applyFinish q D).steps (Nat.le_refl _)
    _ (LocalRun.iterate caller (apply_phase_localRun caller q D regs ctx))
  rwa [stackCells_cfg] at cells

include caller in
theorem equalityFinish_mass_le (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    mass (equalityFinish D).data ctx ≤ mass D ctx := by
  have cells := equality_stage_stackCells_le caller D regs ctx (equalityFinish D).steps (Nat.le_refl _)
    _ (LocalRun.iterate caller (equality_phase_localRun caller D regs ctx))
  rwa [stackCells_cfg] at cells

/-- A paid join preserves the actual sum at both of its two boundary times. -/
theorem stackCells_prefix_one (label target : Label Λ) (D : LocalData) (regs outRegs : Registers R)
    (ctx : ∀ k, List (Γ k))
    (transition : step caller (cfg (some label) regs D ctx) = some (cfg (some target) outRegs D ctx))
    (n : Nat) (bound : n ≤ 1) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some label) regs D ctx)) = some reached) :
    stackCells reached = mass D ctx := by
  have casesN : n = 0 ∨ n = 1 := by omega
  rcases casesN with rfl | rfl
  · have same : reached = cfg (some label) regs D ctx := Option.some.inj executed.symm
    rw [same, stackCells_cfg]
  · have same : reached = cfg (some target) outRegs D ctx := Option.some.inj (executed.symm.trans transition)
    rw [same, stackCells_cfg]

/-! ### All-state actual prefix bounds from explicit stage allowances -/

/-- A property of the actual inclusive owned prefix, not a maximum over an
auxiliary trace or a replacement runtime evaluator. -/
def PrefixBound (start : Cfg Γ Λ R) (limit : Nat) : Prop :=
  ∀ n, n ≤ remainingSteps start → ∀ reached,
    (next caller)^[n] (some start) = some reached → stackCells reached ≤ limit

theorem PrefixBound.mono {start : Cfg Γ Λ R} {a b : Nat}
    (bounded : PrefixBound caller start a) (larger : a ≤ b) : PrefixBound caller start b :=
  fun n bound reached executed => (bounded n bound reached executed).trans larger

theorem result_join_prefix_bound (q : Phase) (result : Bool) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k))
    (transition : step caller (cfg (some (phaseLabel q)) regs D ctx) =
      some (cfg (some (resultLabel result)) (resetAll regs) D ctx)) :
    PrefixBound caller (cfg (some (phaseLabel q)) regs D ctx) (mass D ctx) := by
  have run := phase_step_localRun caller transition
  have rank := LocalRun.remaining caller run
  have finalRank : remainingSteps (cfg (some (resultLabel (Λ := Λ) result)) (resetAll regs) D ctx) = 0 := rfl
  rw [finalRank, Nat.add_zero] at rank
  intro n bound reached executed
  exact Nat.le_of_eq (stackCells_prefix_one caller _ _ D regs (resetAll regs) ctx transition
    n (by omega) reached executed)

theorem equality_join_prefix_bound (r : TreeEqualityMachine.Result) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (cfg (some (phaseLabel (equalityJoinPhase r))) regs D ctx) (mass D ctx) := by
  exact result_join_prefix_bound caller (equalityJoinPhase r) (equalityResult r) D regs ctx
    (equality_join_step caller r D regs ctx)

theorem equality_complete_prefix_bound (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (cfg (some (phaseLabel comparePhase)) regs D ctx) (mass D ctx) := by
  have first := equality_phase_localRun caller D regs ctx
  have composed := prefix_bound_after_localRun caller first stackCells
    (mass D ctx) (mass (equalityFinish D).data ctx)
    (fun n bound reached executed => equality_stage_stackCells_le caller D regs ctx n bound reached executed)
    (equality_join_prefix_bound caller (equalityFinish D).result (equalityFinish D).data (resetEquality regs) ctx)
  rw [max_eq_left (equalityFinish_mass_le caller D regs ctx)] at composed
  exact composed

theorem apply_join_prefix_bound_of_success (r : MoveApplyMachine.FinalResult) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k))
    (continued : r = MoveApplyMachine.success →
      PrefixBound caller (cfg (some (phaseLabel inspectPhase)) (resetAll regs) D ctx) (inspectAllowance D ctx)) :
    PrefixBound caller (cfg (some (phaseLabel (applyJoinPhase r))) regs D ctx) (hJoinAllowance r D ctx) := by
  cases r with
  | inl token =>
      exact result_join_prefix_bound caller (applyJoinPhase (.inl token)) false D regs ctx
        (apply_join_step caller (.inl token) D regs ctx)
  | inr r => cases r with
    | failure =>
        exact result_join_prefix_bound caller (applyJoinPhase (.inr .failure)) false D regs ctx
          (apply_join_step caller (.inr .failure) D regs ctx)
    | success =>
        exact prefix_bound_after_localRun caller (apply_join_localRun caller MoveApplyMachine.success D regs ctx)
          stackCells (mass D ctx) (inspectAllowance D ctx)
          (fun n bound reached executed => Nat.le_of_eq
            (stackCells_prefix_one caller _ _ D regs (resetAll regs) ctx
              (apply_join_step caller MoveApplyMachine.success D regs ctx) n bound reached executed))
          (continued rfl)

theorem apply_phase_prefix_bound_of_success (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k))
    (continued : (applyFinish q D).result = MoveApplyMachine.success →
      PrefixBound caller
        (cfg (some (phaseLabel inspectPhase)) (resetAll regs) (applyFinish q D).data ctx)
        (inspectAllowance (applyFinish q D).data ctx)) :
    PrefixBound caller (cfg (some (phaseLabel (applyPhase q))) regs D ctx) (hPhaseAllowance q D ctx) := by
  apply prefix_bound_after_localRun caller (apply_phase_localRun caller q D regs ctx)
    stackCells (hAllowance q D ctx) (hJoinAllowance (applyFinish q D).result (applyFinish q D).data ctx)
  · exact fun n bound reached executed => apply_stage_stackCells_le caller q D regs ctx n bound reached executed
  · apply apply_join_prefix_bound_of_success caller (applyFinish q D).result (applyFinish q D).data (resetApply regs) ctx
    intro returned
    simpa only [resetAll_resetApply] using continued returned

theorem fuel_join_prefix_bound_of_success (r : FuelDispatchMachine.Exit) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k))
    (continued : (applyFinish (MoveApplyMachine.movePhase .start) D).result = MoveApplyMachine.success →
      PrefixBound caller
        (cfg (some (phaseLabel inspectPhase)) (resetAll regs) (applyFinish (MoveApplyMachine.movePhase .start) D).data ctx)
        (inspectAllowance (applyFinish (MoveApplyMachine.movePhase .start) D).data ctx)) :
    PrefixBound caller (cfg (some (phaseLabel (fuelJoinPhase r))) regs D ctx) (fuelJoinAllowance r D ctx) := by
  cases r with
  | zero =>
      exact result_join_prefix_bound caller (fuelJoinPhase .zero) false D regs ctx
        (fuel_join_step caller .zero D regs ctx)
  | atEnd =>
      have composed := prefix_bound_after_localRun caller (fuel_join_localRun caller .atEnd D regs ctx)
        stackCells (mass D ctx) (mass D ctx)
        (fun n bound reached executed => Nat.le_of_eq
          (stackCells_prefix_one caller _ _ D regs (resetAll regs) ctx
            (fuel_join_step caller .atEnd D regs ctx) n bound reached executed))
        (equality_complete_prefix_bound caller D (resetAll regs) ctx)
      simpa only [PrefixBound, fuelJoinAllowance, max_self] using composed
  | positive =>
      apply prefix_bound_after_localRun caller (fuel_join_localRun caller .positive D regs ctx)
        stackCells (mass D ctx) (hPhaseAllowance (MoveApplyMachine.movePhase .start) D ctx)
      · exact fun n bound reached executed => Nat.le_of_eq
          (stackCells_prefix_one caller _ _ D regs (resetAll regs) ctx
            (fuel_join_step caller .positive D regs ctx) n bound reached executed)
      · apply apply_phase_prefix_bound_of_success caller (MoveApplyMachine.movePhase .start) D (resetAll regs) ctx
        intro returned
        simpa only [resetAll_resetAll] using continued returned

omit [DecidableEq K] in
@[simp] theorem inspectStageFinish_certificate (D : LocalData) :
    (inspectStageFinish D).data.certificate = D.certificate := by
  cases certificate : D.certificate <;> simp only [inspectStageFinish, certificate, counterFinish_certificate]

include caller in
/-- The inspector allowance is exactly the maximum of the conserved Fuel
stage and the allowance of its literal result-join configuration. -/
theorem inspectAllowance_stage (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    inspectAllowance D ctx =
      max (mass D ctx) (fuelJoinAllowance (inspectStageFinish D).result (inspectStageFinish D).data ctx) := by
  rw [inspectAllowance]
  by_cases empty : D.certificate = []
  · simp only [empty, ite_true, inspectStageFinish, fuelJoinAllowance, max_self]
  · rw [ite_eq_right empty]
    obtain ⟨tag, rest, certificate⟩ := List.exists_cons_of_ne_nil empty
    simp only [inspectStageFinish, certificate]
    have conserved := counterFinish_mass caller .borrow D regs ctx
    have endpoint := applyFinish_mass_le caller (MoveApplyMachine.movePhase .start) (counterFinish .borrow D).data regs ctx
    cases fuel : (counterFinish .borrow D).result with
    | zero => simp only [FuelDispatchMachine.exitOfResult, fuelJoinAllowance, conserved, max_self]
    | positive =>
        simp only [FuelDispatchMachine.exitOfResult, fuelJoinAllowance, hPhaseAllowance]
        cases returned : (applyFinish (MoveApplyMachine.movePhase .start) (counterFinish .borrow D).data).result with
        | inl token =>
            simp only [hJoinAllowance, conserved]
            omega
        | inr r => cases r with
          | failure =>
              simp only [hJoinAllowance, conserved]
              omega
          | success =>
              simp only [hJoinAllowance, conserved]
              have nextMass := mass_le_inspectAllowance
                (applyFinish (MoveApplyMachine.movePhase .start) (counterFinish .borrow D).data).data ctx
              omega

/-- The universal dirty inspector space theorem. Recursion occurs only after
a genuine full MoveApplyMachine.start success on its proved shorter certificate suffix. -/
theorem inspect_prefix_bound (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (cfg (some (phaseLabel inspectPhase)) regs D ctx) (inspectAllowance D ctx) := by
  revert regs
  refine (measure (fun D : LocalData => D.certificate.length)).wf.induction
    (C := fun D : LocalData => ∀ regs : Registers R,
      PrefixBound caller (cfg (some (phaseLabel inspectPhase)) regs D ctx) (inspectAllowance D ctx)) D ?_
  intro D ih regs
  rw [inspectAllowance_stage caller D regs ctx]
  apply prefix_bound_after_localRun caller (inspect_stage_localRun caller D regs ctx)
    stackCells (mass D ctx)
    (fuelJoinAllowance (inspectStageFinish D).result (inspectStageFinish D).data ctx)
  · exact fun n bound reached executed => Nat.le_of_eq (inspect_stage_stackCells caller D regs ctx n bound reached executed)
  · apply fuel_join_prefix_bound_of_success caller (inspectStageFinish D).result (inspectStageFinish D).data (resetFuel regs) ctx
    intro returned
    have decrease := apply_start_certificate_lt (inspectStageFinish D).data returned
    have strict : (applyFinish (MoveApplyMachine.movePhase .start) (inspectStageFinish D).data).data.certificate.length < D.certificate.length := by
      simpa only [inspectStageFinish_certificate] using decrease
    exact ih _ strict (resetAll (resetFuel regs))

theorem apply_join_prefix_bound (r : MoveApplyMachine.FinalResult) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (cfg (some (phaseLabel (applyJoinPhase r))) regs D ctx) (hJoinAllowance r D ctx) :=
  apply_join_prefix_bound_of_success caller r D regs ctx (fun _ => inspect_prefix_bound caller D (resetAll regs) ctx)

theorem apply_complete_prefix_bound (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (cfg (some (phaseLabel (applyPhase q))) regs D ctx) (hPhaseAllowance q D ctx) :=
  apply_phase_prefix_bound_of_success caller q D regs ctx
    (fun _ => inspect_prefix_bound caller (applyFinish q D).data (resetAll regs) ctx)

theorem fuel_join_prefix_bound (r : FuelDispatchMachine.Exit) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (cfg (some (phaseLabel (fuelJoinPhase r))) regs D ctx) (fuelJoinAllowance r D ctx) :=
  fuel_join_prefix_bound_of_success caller r D regs ctx
    (fun _ => inspect_prefix_bound caller (applyFinish (MoveApplyMachine.movePhase .start) D).data (resetAll regs) ctx)

theorem counter_complete_prefix_bound (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (cfg (some (phaseLabel (counterPhase q))) regs D ctx) (counterAllowance q D ctx) := by
  exact prefix_bound_after_localRun caller (counter_phase_localRun caller q D regs ctx)
    stackCells (mass D ctx)
    (fuelJoinAllowance (FuelDispatchMachine.exitOfResult (counterFinish q D).result) (counterFinish q D).data ctx)
    (fun n bound reached executed => Nat.le_of_eq (counter_stage_stackCells caller q D regs ctx n bound reached executed))
    (fuel_join_prefix_bound caller _ (counterFinish q D).data (resetFuel regs) ctx)

/-- Every owned starting phase has its explicit endpoint-recursive allowance;
this includes arbitrary partial H and W phases with arbitrary dirty stores. -/
theorem phase_prefix_bound (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (cfg (some (phaseLabel q)) regs D ctx) (phaseAllowance q D ctx) := by
  rcases q with fuel | (applied | equality)
  · rcases fuel with q | (r | (d | impossible))
    · exact counter_complete_prefix_bound caller q D regs ctx
    · cases r with
      | zero => exact fuel_join_prefix_bound caller .zero D regs ctx
      | positive => exact fuel_join_prefix_bound caller .positive D regs ctx
    · cases d with
      | inspectCertificate => exact inspect_prefix_bound caller D regs ctx
      | atEnd => exact fuel_join_prefix_bound caller .atEnd D regs ctx
    · exact Empty.elim impossible
  · rcases applied with q | (r | (q | (r | impossible)))
    · exact apply_complete_prefix_bound caller (MoveApplyMachine.movePhase q) D regs ctx
    · exact apply_complete_prefix_bound caller (MoveApplyMachine.dispatchPhase r) D regs ctx
    · exact apply_complete_prefix_bound caller (MoveApplyMachine.positionPhase q) D regs ctx
    · exact apply_join_prefix_bound caller r D regs ctx
    · exact Empty.elim impossible
  · rcases equality with q | (r | impossible)
    · cases q; exact equality_complete_prefix_bound caller D regs ctx
    · exact equality_join_prefix_bound caller r D regs ctx
    · exact Empty.elim impossible

/-- Actual total physical storage at every inclusive prefix through the first
outer result; callers may act only after that boundary. -/
theorem prefix_stackCells_le_dirty (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    stackCells reached ≤ allowance start := by
  by_cases owned : Owned start.l
  · obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases start owned
    rw [allowance_phase_cfg]
    exact phase_prefix_bound caller q D regs ctx n bound reached executed
  · rw [nonowned_remaining start owned] at bound
    have zero : n = 0 := by omega
    subst n
    have same : reached = start := Option.some.inj executed.symm
    rw [same, nonowned_allowance start owned]

/-- The same reached configuration carries execution, exact remaining time,
local closure, ownership, zero-time identity, caller/frame preservation, and
the universal dirty physical bound. The staged-register enrichment is supplied
by the separately proved exact prefix-reset theorem. -/
theorem owned_prefix_physical (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var.2.2 = start.var.2.2 ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧ stackCells reached ≤ allowance start := by
  obtain ⟨reached, executed, rank, path, live⟩ := owned_prefix caller start n bound
  obtain ⟨registers, frame⟩ := prefix_frame caller start reached n bound executed
  refine ⟨reached, executed, rank, path, live, ?_, registers, frame,
    prefix_stackCells_le_dirty caller start n bound reached executed⟩
  intro zero
  subst n
  exact Option.some.inj executed.symm

end PhysicalSpace

end Resources.RotationCertificate.StreamMachine

