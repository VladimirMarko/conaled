import Examples.RotationCertificateStreamMachine.Source

/-!
# RotationCertificateStreamMachine: Space
-/

namespace Examples.RotationCertificateStreamMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.StreamMachine

/-! ## Explicit dirty allowances and a single complete actual prefix witness -/

section DirtyAllowanceEquations
variable {K : Type} {Γ : K → Type} [Fintype K]

theorem the_dirty_base_counts_all_nine_words_and_every_protected_word
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    mass D ctx = D.certificate.length + D.moveReverse.length + D.path.length +
      D.source.length + D.saved.length + D.scratch.length + D.units.length +
      D.fuel.length + D.target.length + externalCells ctx := rfl

theorem the_dirty_inspector_budget_uses_the_actual_fuel_and_apply_endpoints
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    inspectAllowance D ctx =
      if D.certificate = [] then mass D ctx else
        let borrowed := counterFinish .borrow D
        match borrowed.result with
        | .zero => mass D ctx
        | .positive =>
            let applied := applyFinish (MoveApplyMachine.movePhase .start) borrowed.data
            match applied.result with
            | .inl _ | .inr .failure =>
                max (mass D ctx) (hAllowance (MoveApplyMachine.movePhase .start) borrowed.data ctx)
            | .inr .success =>
                max (mass D ctx)
                  (max (hAllowance (MoveApplyMachine.movePhase .start) borrowed.data ctx)
                    (inspectAllowance applied.data ctx)) := by
  rw [inspectAllowance]
  by_cases empty : D.certificate = []
  · simp only [ite_eq_left empty]
  · simp only [ite_eq_right empty]
    cases fuelResult : (counterFinish .borrow D).result with
    | zero => simp_all only
    | positive =>
        cases applyResult :
            (applyFinish (MoveApplyMachine.movePhase .start) (counterFinish .borrow D).data).result with
        | inl token => simp_all only
        | inr result => cases result <;> simp_all only

theorem dirty_apply_phase_space_retains_debt_credit_and_the_actual_result_join
    (q : MoveApplyMachine.Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    hPhaseAllowance q D ctx =
      max (mass D ctx + MoveApplyMachine.phaseDebt q +
        MoveApplyMachine.phaseCredit q (applyData D))
        (hJoinAllowance (applyFinish q D).result (applyFinish q D).data ctx) := rfl

theorem dirty_counter_phase_space_uses_its_actual_returned_words
    (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    counterAllowance q D ctx = max (mass D ctx)
      (fuelJoinAllowance (FuelDispatchMachine.exitOfResult (counterFinish q D).result)
        (counterFinish q D).data ctx) := rfl

theorem all_three_fuel_join_allowances_keep_their_distinct_continuations
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    fuelJoinAllowance .atEnd D ctx = mass D ctx ∧
      fuelJoinAllowance .zero D ctx = mass D ctx ∧
      fuelJoinAllowance .positive D ctx =
        max (mass D ctx) (hPhaseAllowance (MoveApplyMachine.movePhase .start) D ctx) :=
  ⟨rfl, rfl, rfl⟩

theorem all_three_apply_join_allowances_keep_dirty_success_reentry
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    hJoinAllowance MoveApplyMachine.parseFailure D ctx = mass D ctx ∧
      hJoinAllowance MoveApplyMachine.rotationFailure D ctx = mass D ctx ∧
      hJoinAllowance MoveApplyMachine.success D ctx =
        max (mass D ctx) (inspectAllowance D ctx) := ⟨rfl, rfl, rfl⟩

theorem equality_and_both_boolean_joins_have_no_extra_space_allowance
    (D : LocalData) (ctx : ∀ k, List (Γ k)) (r : TreeEqualityMachine.Result) :
    phaseAllowance comparePhase D ctx = mass D ctx ∧
      phaseAllowance (equalityJoinPhase r) D ctx = mass D ctx := ⟨rfl, rfl⟩

end DirtyAllowanceEquations

section DirtyActualPrefixSpace
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)

theorem every_dirty_configuration_bounds_every_actual_inclusive_prefix
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : Runs (step caller) start n reached) :
    physicalCells reached ≤ allowance start :=
  prefix_stackCells_le_dirty caller start n bound reached executed

theorem one_dirty_prefix_witness_has_execution_rank_stages_frame_and_space
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, Runs (step caller) start n reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧
      reached.var = registersAt start n ∧
      reached.var.2.2 = start.var.2.2 ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
      physicalCells reached ≤ allowance start := by
  obtain ⟨reached, executed, rank, path, owned, zero, registers, user, frame⟩ :=
    owned_prefix_frame caller start n bound
  exact ⟨reached, executed, rank, path, owned, zero, registers, user, frame,
    prefix_stackCells_le_dirty caller start n bound reached executed⟩

omit [Fintype K] in
theorem the_exact_stage_mask_applies_to_the_same_actual_reached_configuration
    (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : Runs (step caller) start n reached) :
    reached.var = registersAt start n := prefix_reset caller start reached n bound executed

omit [Fintype K] in
include caller in
theorem the_zero_step_stage_mask_is_the_original_register_tuple
    (start : Cfg Γ Λ R) : registersAt start 0 = start.var :=
  (prefix_reset caller start start 0 (Nat.zero_le _) rfl).symm

omit [DecidableEq K] in
theorem nonowned_live_configurations_use_exactly_their_existing_physical_mass
    (start : Cfg Γ Λ R) (outside : ¬ Owned start.l) :
    allowance start = physicalCells start := nonowned_allowance start outside

theorem nonowned_prefixes_are_only_the_original_state_at_zero
    (start reached : Cfg Γ Λ R) (outside : ¬ Owned start.l) (n : Nat)
    (bound : n ≤ remainingSteps start) (executed : Runs (step caller) start n reached) :
    n = 0 ∧ reached = start ∧ reached.var = start.var ∧
      physicalCells reached = physicalCells start := by
  have clock := nonowned_remaining start outside
  have zero : n = 0 := by omega
  subst n
  have same : reached = start := Option.some.inj executed.symm
  exact ⟨rfl, same, congrArg Turing.TM2.Cfg.var same, congrArg physicalCells same⟩

end DirtyActualPrefixSpace

/-! ## Clean, represented, finite-package and installed physical specializations -/

section CleanPhysicalConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)

theorem clean_raw_inputs_bound_every_actual_physical_prefix
    (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ runSteps fuel certificate source target)
    (reached : Cfg Γ Λ R)
    (executed : Runs (step caller) (entry regs fuel certificate source target ctx) n reached) :
    physicalCells reached ≤ certificate.length + 2 * source.length + fuel.length +
      target.length + externalCells ctx := by
  have bounded := prefix_stackCells_le_dirty caller
    (entry regs fuel certificate source target ctx) n bound reached executed
  rw [entry, allowance_phase_cfg] at bounded
  exact bounded.trans (inspectAllowance_clean_le fuel certificate source target ctx)

theorem one_clean_prefix_witness_has_every_contract_and_the_closed_physical_bound
    (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ runSteps fuel certificate source target) :
    ∃ reached, Runs (step caller) (entry regs fuel certificate source target ctx) n reached ∧
      remainingSteps reached = runSteps fuel certificate source target - n ∧
      Relation.ReflTransGen (LocalStep caller) (entry regs fuel certificate source target ctx) reached ∧
      (n < runSteps fuel certificate source target ↔ Owned reached.l) ∧
      (n = 0 → reached = entry regs fuel certificate source target ctx) ∧
      reached.var = registersAt (entry (Λ := Λ) regs fuel certificate source target ctx) n ∧
      reached.var.2.2 = regs.2.2 ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      physicalCells reached ≤ certificate.length + 2 * source.length + fuel.length +
        target.length + externalCells ctx := by
  obtain ⟨reached, executed, rank, path, owned, zero, registers, user, frame⟩ :=
    owned_prefix_frame caller (entry regs fuel certificate source target ctx) n bound
  exact ⟨reached, executed, rank, path, owned, zero, registers, user, frame,
    clean_raw_inputs_bound_every_actual_physical_prefix caller regs fuel certificate source target ctx
      n bound reached executed⟩

theorem represented_inputs_keep_the_same_physical_prefix_witness
    (regs : Registers R) (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit)
    (ctx : ∀ k, List (Γ k)) (n : Nat)
    (bound : n ≤ runSteps fuel certificate (treeCode source) (treeCode target)) :
    ∃ reached, Runs (step caller)
        (entry regs fuel certificate (treeCode source) (treeCode target) ctx) n reached ∧
      remainingSteps reached = runSteps fuel certificate (treeCode source) (treeCode target) - n ∧
      Relation.ReflTransGen (LocalStep caller)
        (entry regs fuel certificate (treeCode source) (treeCode target) ctx) reached ∧
      (n < runSteps fuel certificate (treeCode source) (treeCode target) ↔ Owned reached.l) ∧
      (n = 0 → reached = entry regs fuel certificate (treeCode source) (treeCode target) ctx) ∧
      reached.var = registersAt (entry (Λ := Λ) regs fuel certificate (treeCode source) (treeCode target) ctx) n ∧
      reached.var.2.2 = regs.2.2 ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      physicalCells reached ≤ certificate.length + 2 * (treeCode source).length + fuel.length +
        (treeCode target).length + externalCells ctx :=
  one_clean_prefix_witness_has_every_contract_and_the_closed_physical_bound caller regs fuel
    certificate (treeCode source) (treeCode target) ctx n bound

theorem exact_equality_prefixes_count_the_two_actually_consumed_word_tails
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ TreeEqualityMachine.runSteps D.source D.target)
    (reached : Cfg Γ Λ R)
    (executed : Runs (step caller) (cfg (some (phaseLabel comparePhase)) regs D ctx) n reached) :
    physicalCells reached =
      mass { D with source := D.source.drop n, target := D.target.drop n } ctx :=
  equality_prefix_stackCells_exact caller D regs ctx n bound reached executed

end CleanPhysicalConnections

section FinitePackagePhysicalConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : External Λ → Statement Γ Λ R)

theorem the_actual_finite_package_has_the_same_all_state_physical_bound
    (initial : R) (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : Runs (machine caller initial).step start n reached) :
    physicalCells reached ≤ allowance start :=
  prefix_stackCells_le_dirty caller start n bound reached executed

theorem the_actual_finite_package_has_one_clean_rank_frame_and_space_witness
    (initial : R) (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ runSteps fuel certificate source target) :
    ∃ reached, Runs (machine caller initial).step (entry regs fuel certificate source target ctx) n reached ∧
      remainingSteps reached = runSteps fuel certificate source target - n ∧
      Relation.ReflTransGen (LocalStep caller) (entry regs fuel certificate source target ctx) reached ∧
      (n < runSteps fuel certificate source target ↔ Owned reached.l) ∧
      (n = 0 → reached = entry regs fuel certificate source target ctx) ∧
      reached.var = registersAt (entry (Λ := Λ) regs fuel certificate source target ctx) n ∧
      reached.var.2.2 = regs.2.2 ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      physicalCells reached ≤ certificate.length + 2 * source.length + fuel.length +
        target.length + externalCells ctx :=
  one_clean_prefix_witness_has_every_contract_and_the_closed_physical_bound caller regs fuel
    certificate source target ctx n bound

end FinitePackagePhysicalConnections

section ExplicitFrontEndPhysicalSpace
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement (FrontEndProtectedAlphabet Γ)
  Λ (FrontEndDecoderComplement × R))

theorem a_clean_explicit_front_end_entry_has_the_closed_physical_prefix_bound
    (regs : FrontEndMachine.Registers (Option Branch × R))
    (ctx : ∀ k, List (Γ k)) (source target : BinaryTree Unit) (fuel : Bits) (certificate : Word)
    (n : Nat) (bound : n ≤ runSteps fuel certificate (treeCode source) (treeCode target))
    (reached : Cfg (FrontEndProtectedAlphabet Γ) Λ (FrontEndDecoderComplement × R))
    (executed : Runs (step caller)
      (frontEndInstalledEntry regs [] [] ctx source target fuel certificate) n reached) :
    physicalCells reached ≤ certificate.length + 2 * (treeCode source).length + fuel.length +
      (treeCode target).length + externalCells ctx := by
  have bounded := clean_raw_inputs_bound_every_actual_physical_prefix caller
    (frontEndRegisterEquiv (FrontEndMachine.reset regs)) fuel certificate
    (treeCode source) (treeCode target) (frontEndSuccessContext ctx) n bound reached executed
  have cells : externalCells (frontEndSuccessContext ctx) = externalCells ctx :=
    front_end_success_context_cells ctx
  simpa only [cells] using bounded

theorem arbitrary_dirty_front_end_branch_words_use_the_meaningful_dirty_allowance
    (regs : FrontEndMachine.Registers (Option Branch × R)) (B O : List Branch)
    (ctx : ∀ k, List (Γ k)) (source target : BinaryTree Unit) (fuel : Bits) (certificate : Word)
    (n : Nat)
    (bound : n ≤ remainingSteps (frontEndInstalledEntry (Λ := Λ) regs B O ctx source target fuel certificate))
    (reached : Cfg (FrontEndProtectedAlphabet Γ) Λ (FrontEndDecoderComplement × R))
    (executed : Runs (step caller)
      (frontEndInstalledEntry regs B O ctx source target fuel certificate) n reached) :
    physicalCells reached ≤ inspectAllowance
      (frontEndSuccessData source target fuel certificate B O) (frontEndSuccessContext ctx) := by
  have bounded := prefix_stackCells_le_dirty caller
    (frontEndInstalledEntry regs B O ctx source target fuel certificate) n bound reached executed
  rw [frontEndInstalledEntry, allowance_phase_cfg] at bounded
  exact bounded

end ExplicitFrontEndPhysicalSpace

/-! ## Sharper physical bounds for the current parsed call -/

section CurrentCallPhysicalBounds
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)

theorem a_successfully_parsed_current_call_keeps_the_sharper_two_stage_bound
    (regs : Registers R) (fuel : Bits) (certificate source target rest : Word)
    (move : RotationMove) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (n : Nat) (bound : n ≤ MoveApplyMachine.runSteps certificate [] source [] [] [])
    (reached : Cfg Γ Λ R)
    (executed : Runs (step caller)
      (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start))))
        regs (cleanData fuel certificate source target) ctx) n reached) :
    physicalCells reached ≤
      max (certificate.length + source.length) (rest.length + move.position.length + 2 * source.length) +
        fuel.length + target.length + externalCells ctx :=
  apply_clean_prefix_cells_of_some caller fuel certificate source target move rest regs ctx
    parsed n bound reached executed

theorem a_failed_current_parse_does_not_charge_unused_tree_credit
    (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) (failed : (parseMoveRun certificate).1 = none)
    (n : Nat) (bound : n ≤ MoveApplyMachine.runSteps certificate [] source [] [] [])
    (reached : Cfg Γ Λ R)
    (executed : Runs (step caller)
      (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start))))
        regs (cleanData fuel certificate source target) ctx) n reached) :
    physicalCells reached ≤ certificate.length + source.length + fuel.length +
      target.length + externalCells ctx := by
  let D := cleanData fuel certificate source target
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let start : ApplyCfg Γ Λ R := MoveApplyMachine.entry (applyRegisterEquiv.symm regs)
    certificate [] source [] [] [] (applyContext D ctx)
  have mapped : applyCfg start =
      cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) regs D ctx := by
    simp only [start, MoveApplyMachine.entry, applyCfg_partial]
    rfl
  obtain ⟨middle, run, _, same⟩ := apply_prefix_lift caller localCaller start n bound reached
    (by rw [mapped]; exact executed)
  have cells := MoveApplyMachine.prefix_stackCells_le_of_none localCaller certificate
    [] source [] [] [] (applyRegisterEquiv.symm regs) (applyContext D ctx) failed n bound middle run
  change stackCells reached ≤ _
  rw [same, stackCells_applyCfg]
  rw [MoveApplyMachine.principalCells, applyContext_cells] at cells
  dsimp only [D, cleanData] at cells
  simp only [List.length_nil, Nat.add_zero] at cells
  change _ ≤ certificate.length + source.length + fuel.length + target.length + contextCells ctx
  omega

end CurrentCallPhysicalBounds

/-! ## Actual packaged clean and represented execution records -/

section PackagedSourceConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : External Λ → Statement Γ Λ R) (initial : R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem actual_packaged_clean_inputs_have_the_complete_first_handoff
    (fuel : Bits) (certificate source target : Word) :
    FirstRun (machine caller initial).step (entry regs fuel certificate source target ctx)
      (runSteps fuel certificate source target) (runResult regs fuel certificate source target ctx) :=
  run_firstRun caller regs fuel certificate source target ctx

theorem actual_packaged_represented_first_booleans_match_the_source_checker
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) (result : Bool) :
    FirstResult (machine caller initial).step
      (entry regs fuel certificate (treeCode source) (treeCode target) ctx) result ↔
      (checkStreamRun fuel source target certificate).1 = result :=
  represented_firstResult_iff caller regs fuel certificate source target ctx result

def machineExactCleanTiming (fuel : Bits) (certificate source target : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (entry regs fuel certificate source target ctx)
      (some (runResult regs fuel certificate source target ctx))
      (runSteps fuel certificate source target) :=
  runInTimeExact caller regs fuel certificate source target ctx

def machinePolynomialCleanTiming (fuel : Bits) (certificate source target : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (entry regs fuel certificate source target ctx)
      (some (runResult regs fuel certificate source target ctx))
      ((2 * fuel.length + 3 * source.length + 7) * certificate.length + source.length + 4) :=
  runInPolynomialTime caller regs fuel certificate source target ctx

def machineExactRepresentedTiming
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
      (some (runResult regs fuel certificate (treeCode source) (treeCode target) ctx))
      (runSteps fuel certificate (treeCode source) (treeCode target)) :=
  representedInTimeExact caller regs fuel certificate source target ctx

def machinePolynomialRepresentedTiming
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
      (some (runResult regs fuel certificate (treeCode source) (treeCode target) ctx))
      ((2 * fuel.length + 6 * source.numNodes + 10) * certificate.length + 2 * source.numNodes + 5) :=
  representedInPolynomialTime caller regs fuel certificate source target ctx

theorem both_actual_packaged_clean_records_store_the_exact_machine_clock
    (fuel : Bits) (certificate source target : Word) :
    (machineExactCleanTiming caller initial regs ctx fuel certificate source target).steps =
        runSteps fuel certificate source target ∧
      (machinePolynomialCleanTiming caller initial regs ctx fuel certificate source target).steps =
        runSteps fuel certificate source target := ⟨rfl, rfl⟩

theorem both_actual_packaged_represented_records_store_the_exact_machine_clock
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) :
    (machineExactRepresentedTiming caller initial regs ctx fuel certificate source target).steps =
        runSteps fuel certificate (treeCode source) (treeCode target) ∧
      (machinePolynomialRepresentedTiming caller initial regs ctx fuel certificate source target).steps =
        runSteps fuel certificate (treeCode source) (treeCode target) := ⟨rfl, rfl⟩

end PackagedSourceConnections

/-! ## The installed owned-prefix contract retains one actual configuration -/

section InstalledCompletePrefixConnections
variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable [DecidableEq K] [DecidableEq K']
variable (names : StackId K ≃ K') (symbols : ∀ k, Alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable (caller : External Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
variable (installed : ∀ label, Owned (some label) →
  ambient (labels label) =
    FrontEndMachine.Transport.statement names symbols registers labels (program caller label))

include installed in
theorem one_installed_actual_prefix_has_the_complete_source_rank_stages_and_frame
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached : Turing.TM2.Cfg Γ' Λ' R',
      (FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) = some reached ∧
      let source := (installedCfgEquiv names symbols registers labels).symm reached
      Runs (step caller) start n source ∧
        remainingSteps source = remainingSteps start - n ∧
        Relation.ReflTransGen (LocalStep caller) start source ∧
        (n < remainingSteps start ↔ Owned source.l) ∧
        (n = 0 → source = start) ∧ source.var = registersAt start n ∧
        source.var.2.2 = start.var.2.2 ∧
        ∀ k, source.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨source, executed, rank, path, owned, zero, stage, user, frame⟩ :=
    owned_prefix_frame caller start n bound
  refine ⟨installedCfg names symbols registers labels source, ?_, ?_⟩
  · rw [installed_owned_prefix names symbols registers labels caller ambient installed start n bound,
      executed]
    rfl
  · have inverse : (installedCfgEquiv names symbols registers labels).symm
        (installedCfg names symbols registers labels source) = source :=
        (installedCfgEquiv names symbols registers labels).symm_apply_apply source
    dsimp only
    rw [inverse]
    exact ⟨executed, rank, path, owned, zero, stage, user, frame⟩

include installed in
theorem one_installed_actual_dirty_prefix_has_rank_stages_frame_and_space
    [Fintype K] [Fintype K']
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached : Turing.TM2.Cfg Γ' Λ' R',
      (FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) = some reached ∧
      (let source := (installedCfgEquiv names symbols registers labels).symm reached
       Runs (step caller) start n source ∧
         remainingSteps source = remainingSteps start - n ∧
         Relation.ReflTransGen (LocalStep caller) start source ∧
         (n < remainingSteps start ↔ Owned source.l) ∧
         (n = 0 → source = start) ∧ source.var = registersAt start n ∧
         source.var.2.2 = start.var.2.2 ∧
         ∀ k, source.stk (.inr k) = start.stk (.inr k)) ∧
      (∑ k, (reached.stk k).length) ≤ allowance start := by
  obtain ⟨reached, executed, properties⟩ :=
    one_installed_actual_prefix_has_the_complete_source_rank_stages_and_frame
      names symbols registers labels caller ambient installed start n bound
  refine ⟨reached, executed, properties, ?_⟩
  exact installed_prefix_cells_of_source_bound names symbols registers labels caller ambient installed
    start n bound (allowance start)
    (fun source run => prefix_stackCells_le_dirty caller start n bound source run) reached executed

def exactInstalledCleanTiming (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels (entry regs fuel certificate source target ctx))
      (some (installedCfg names symbols registers labels (runResult regs fuel certificate source target ctx)))
      (runSteps fuel certificate source target) :=
  installedOwnedTimed names symbols registers labels caller ambient installed
    (entry regs fuel certificate source target ctx)

def polynomialInstalledCleanTiming (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels (entry regs fuel certificate source target ctx))
      (some (installedCfg names symbols registers labels (runResult regs fuel certificate source target ctx)))
      ((2 * fuel.length + 3 * source.length + 7) * certificate.length + source.length + 4) where
  steps := runSteps fuel certificate source target
  evals_in_steps := (exactInstalledCleanTiming names symbols registers labels caller ambient installed
    regs fuel certificate source target ctx).evals_in_steps
  steps_le_m := runSteps_le fuel certificate source target

def exactInstalledRepresentedTiming (regs : Registers R) (fuel : Bits)
    (certificate : Word) (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels
        (entry regs fuel certificate (treeCode source) (treeCode target) ctx))
      (some (installedCfg names symbols registers labels
        (runResult regs fuel certificate (treeCode source) (treeCode target) ctx)))
      (runSteps fuel certificate (treeCode source) (treeCode target)) :=
  exactInstalledCleanTiming names symbols registers labels caller ambient installed regs fuel
    certificate (treeCode source) (treeCode target) ctx

def polynomialInstalledRepresentedTiming (regs : Registers R) (fuel : Bits)
    (certificate : Word) (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels
        (entry regs fuel certificate (treeCode source) (treeCode target) ctx))
      (some (installedCfg names symbols registers labels
        (runResult regs fuel certificate (treeCode source) (treeCode target) ctx)))
      ((2 * fuel.length + 6 * source.numNodes + 10) * certificate.length + 2 * source.numNodes + 5) where
  steps := runSteps fuel certificate (treeCode source) (treeCode target)
  evals_in_steps := (exactInstalledRepresentedTiming names symbols registers labels caller ambient installed
    regs fuel certificate source target ctx).evals_in_steps
  steps_le_m := runSteps_code_le fuel certificate source target

theorem both_installed_clean_time_records_store_the_exact_clock
    (regs : Registers R) (fuel : Bits) (certificate source target : Word) (ctx : ∀ k, List (Γ k)) :
    (exactInstalledCleanTiming names symbols registers labels caller ambient installed
        regs fuel certificate source target ctx).steps = runSteps fuel certificate source target ∧
      (polynomialInstalledCleanTiming names symbols registers labels caller ambient installed
        regs fuel certificate source target ctx).steps = runSteps fuel certificate source target := ⟨rfl, rfl⟩

theorem both_installed_represented_time_records_store_the_exact_clock
    (regs : Registers R) (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit)
    (ctx : ∀ k, List (Γ k)) :
    (exactInstalledRepresentedTiming names symbols registers labels caller ambient installed
        regs fuel certificate source target ctx).steps =
        runSteps fuel certificate (treeCode source) (treeCode target) ∧
      (polynomialInstalledRepresentedTiming names symbols registers labels caller ambient installed
        regs fuel certificate source target ctx).steps =
        runSteps fuel certificate (treeCode source) (treeCode target) := ⟨rfl, rfl⟩

end InstalledCompletePrefixConnections


/-! ## Exact stage changes and all-prefix frames without finite caller labels -/

section GenericStageContracts
variable {K Λ R : Type} {Γ : K → Type}

theorem the_generic_phase_mask_distinguishes_zero_before_join_and_after_join
    (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) :
    phaseRegistersAt (Λ := Λ) q regs D ctx n =
      if n = 0 then regs else if n < firstJoinSteps q D
        then phaseRegistersBeforeJoin (Λ := Λ) q regs D ctx n else resetAll regs := rfl

theorem the_fuel_component_mask_preserves_all_apply_and_caller_registers
    (q : FuelDispatchMachine.Label Empty) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) :
    phaseRegistersBeforeJoin (Λ := Λ) (.inl q) regs D ctx n = (none, regs.2) := rfl

theorem the_apply_component_mask_uses_its_actual_parser_or_position_stage
    (q : MoveApplyMachine.Label Empty) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) :
    phaseRegistersBeforeJoin (Λ := Λ) (.inr (.inl q)) regs D ctx n =
      applyRegisterEquiv (MoveApplyMachine.registersAt
        (toApplyCfg (cfg (some (phaseLabel (Λ := Λ) (.inr (.inl q)))) regs D ctx)) n) := rfl

theorem the_equality_component_mask_preserves_fuel_branch_and_caller_registers
    (q : TreeEqualityMachine.Label Empty) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) :
    phaseRegistersBeforeJoin (Λ := Λ) (.inr (.inr q)) regs D ctx n =
      (regs.1, ((regs.2.1.1, (none, none)), regs.2.2)) := rfl

variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem one_nonphysical_prefix_witness_has_exact_rank_stages_and_every_protected_word
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, Runs (step caller) start n reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      reached.var.2.2 = start.var.2.2 ∧
      ∀ k, reached.stk (.inr k) = start.stk (.inr k) :=
  owned_prefix_frame caller start n bound

theorem every_actual_prefix_after_the_first_paid_join_has_all_four_temporaries_reset
    (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (afterJoin : firstJoinSteps q D ≤ n) (bound : n ≤ phaseSteps q D)
    (reached : Cfg Γ Λ R)
    (executed : Runs (step caller) (cfg (some (phaseLabel q)) regs D ctx) n reached) :
    reached.var = resetAll regs :=
  prefix_reset_after_first_join caller q D regs ctx n reached afterJoin bound executed

end GenericStageContracts

section PackagedSharedDirtyWitness
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : External Λ → Statement Γ Λ R)

theorem the_finite_package_has_one_dirty_execution_rank_stage_frame_and_space_witness
    (initial : R) (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, Runs (machine caller initial).step start n reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      reached.var.2.2 = start.var.2.2 ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
      physicalCells reached ≤ allowance start :=
  one_dirty_prefix_witness_has_execution_rank_stages_frame_and_space caller start n bound

end PackagedSharedDirtyWitness

section InstalledSharedCleanWitness
variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable [DecidableEq K] [DecidableEq K'] [Fintype K] [Fintype K']
variable (names : StackId K ≃ K') (symbols : ∀ k, Alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable (caller : External Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
variable (installed : ∀ label, Owned (some label) →
  ambient (labels label) =
    FrontEndMachine.Transport.statement names symbols registers labels (program caller label))

include installed in
theorem one_installed_clean_prefix_has_the_same_exact_rank_stages_frame_and_closed_space
    (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ runSteps fuel certificate source target) :
    ∃ reached : Turing.TM2.Cfg Γ' Λ' R',
      (FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels (entry regs fuel certificate source target ctx))) =
          some reached ∧
      (let pulledBack := (installedCfgEquiv names symbols registers labels).symm reached
       Runs (step caller) (entry regs fuel certificate source target ctx) n pulledBack ∧
         remainingSteps pulledBack = runSteps fuel certificate source target - n ∧
         Relation.ReflTransGen (LocalStep caller) (entry regs fuel certificate source target ctx) pulledBack ∧
         (n < runSteps fuel certificate source target ↔ Owned pulledBack.l) ∧
         (n = 0 → pulledBack = entry regs fuel certificate source target ctx) ∧
         pulledBack.var = registersAt (entry (Λ := Λ) regs fuel certificate source target ctx) n ∧
         pulledBack.var.2.2 = regs.2.2 ∧ ∀ k, pulledBack.stk (.inr k) = ctx k) ∧
      (∑ k, (reached.stk k).length) ≤ certificate.length + 2 * source.length + fuel.length +
        target.length + externalCells ctx := by
  obtain ⟨reached, executed, properties⟩ :=
    one_installed_actual_prefix_has_the_complete_source_rank_stages_and_frame
      names symbols registers labels caller ambient installed
      (entry regs fuel certificate source target ctx) n bound
  refine ⟨reached, executed, properties, ?_⟩
  exact installed_prefix_cells_of_source_bound names symbols registers labels caller ambient installed
    (entry regs fuel certificate source target ctx) n bound
    (certificate.length + 2 * source.length + fuel.length + target.length + externalCells ctx)
    (fun pulledBack run => clean_raw_inputs_bound_every_actual_physical_prefix caller regs fuel certificate
      source target ctx n bound pulledBack run) reached executed

end InstalledSharedCleanWitness


/-! ## Parsed raw calls retain actual stopped paths and charged recursive runs -/

section ActualRawRecursion
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem a_parsed_raw_call_has_its_literal_failure_or_actual_recursive_first_run
    (regs : Registers R) (fuel nextFuel : Bits) (certificate source target : Word)
    (move : RotationMove) (rest : Word) (ctx : ∀ k, List (Γ k))
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest)) :
    ∃ result output path,
      MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) (moveCleanData certificate source) =
        ⟨.inr result, { certificate := rest, source := output, path := path },
          2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position⟩ ∧
      output.length = source.length ∧
      (∃ consumed, move.position = consumed ++ path) ∧
      (result = .failure → output = source) ∧
      (result = .failure →
        FirstRun (step caller) (entry regs fuel certificate source target ctx)
          (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
            (2 * move.position.length + 4 +
              PositionedRotationMachine.runSteps move.direction source move.position) + 3)
          (cfg (some (resultLabel false)) (resetAll regs)
            { (cleanData nextFuel rest source target) with path := path } ctx)) ∧
      (result = .success → path = [] ∧
        FirstRun (step caller) (entry regs fuel certificate source target ctx)
          (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
            (2 * move.position.length + 4 +
              PositionedRotationMachine.runSteps move.direction source move.position) + 3 +
            runSteps nextFuel rest output target)
          (runResult (resetAll regs) nextFuel rest output target ctx)) := by
  obtain ⟨result, output, path, applied, length, suffix, restored, failed, succeeded⟩ :=
    runEvaluation_after_parse fuel nextFuel certificate source target move rest decremented parsed
  refine ⟨result, output, path, applied, length, suffix, restored, ?_, ?_⟩
  · intro failure
    exact clean_first_run_from_the_complete_evaluation caller regs ctx fuel certificate source target
      false _ _ (failed failure)
  · intro success
    subst result
    obtain ⟨empty, _⟩ := succeeded rfl
    subst path
    have actual := run_firstRun caller regs fuel certificate source target ctx
    rw [runSteps_step fuel nextFuel certificate source target move rest output decremented parsed applied,
      runResult_step regs fuel nextFuel certificate source target move rest output ctx decremented parsed applied] at actual
    exact ⟨rfl, actual⟩

end ActualRawRecursion


/-! The second finite label package uses its real one-input initializer too. -/
theorem both_literal_inputs_of_the_two_label_package_use_actual_initList
    (caller : External (Fin 2) → Statement IndependentAlphabet (Fin 2) Bool)
    (initial : Bool) :
    FirstRun (twoLabelPackage caller initial).step
      (Turing.initList (twoLabelPackage caller initial) ([] : Word)) 4
      (cfg (some (resultLabel true)) (clean initial) {} (fun _ => [])) ∧
    FirstRun (twoLabelPackage caller initial).step
      (Turing.initList (twoLabelPackage caller initial) ([15] : Word)) 4
      (cfg (some (resultLabel false)) (clean initial) {certificate := [15]} (fun _ => [])) :=
  ⟨machine_init_first_return caller initial [], machine_init_first_return caller initial [15]⟩

end Examples.RotationCertificateStreamMachine
