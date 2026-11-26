import Examples.RotationCertificateFrontEndStreamMachine.PhysicalPaths

/-!
# RotationCertificateFrontEndStreamMachine: Installation
-/

namespace Examples.RotationCertificateFrontEndStreamMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.FrontEndStreamMachine

/-! ## Actual finite-package outputs, exact stored counts and one prefix witness -/

section ActualPackageTiming

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R) (initial : R)

def packageExactOutput (raw : Bits) :
    Turing.TM2OutputsInTime (machine caller initial) raw
      (some [BitPairFraming.verifyFramed raw]) (runSteps raw) :=
  initOutputsInTimeExact caller initial raw

def packagePolynomialOutput (raw : Bits) :
    Turing.TM2OutputsInTime (machine caller initial) raw
      (some [BitPairFraming.verifyFramed raw]) (raw.length * raw.length + 10 * raw.length + 36) :=
  initOutputsInTimePolynomial caller initial raw

def packageActualOutput (raw : Bits) :
    Turing.TM2Outputs (machine caller initial) raw (some [BitPairFraming.verifyFramed raw]) :=
  initOutputs caller initial raw

def packageOuterNoneTime (raw : Bits) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw) none (runSteps raw + 1) :=
  initNoneInTime caller initial raw

theorem package_output_records_keep_the_executed_count_separate_from_the_polynomial_bound
    (raw : Bits) :
    (packageExactOutput caller initial raw).steps = runSteps raw ∧
    (packagePolynomialOutput caller initial raw).steps = runSteps raw ∧
    (packageOuterNoneTime caller initial raw).steps = runSteps raw + 1 := ⟨rfl, rfl, rfl⟩

theorem a_genuine_package_first_halt_converse_fixes_both_time_and_literal_haltList
    (raw : Bits) (n : Nat) (finish : Cfg Γ Λ R) :
    FirstHalt (machine caller initial).step (Turing.initList (machine caller initial) raw) n finish ↔
      n = runSteps raw ∧
      finish = Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw] :=
  init_first_halt_iff caller initial raw n finish

theorem the_genuine_package_has_a_live_output_at_its_exact_clock_and_outer_none_afterward
    (raw : Bits) :
    (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[runSteps raw]
      (some (Turing.initList (machine caller initial) raw)) =
      some (Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw]) ∧
    ∀ n, runSteps raw < n →
      (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[n]
        (some (Turing.initList (machine caller initial) raw)) = none :=
  ⟨init_iterate caller initial raw, init_after_halt caller initial raw⟩

theorem one_genuine_package_prefix_witness_has_rank_reset_empty_context_halt_target_and_space
    (raw : Bits) (n : Nat) (bound : n ≤ runSteps raw) :
    ∃ reached,
      (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[n]
        (some (Turing.initList (machine caller initial) raw)) = some reached ∧
      remainingSteps reached = runSteps raw - n ∧
      Relation.ReflTransGen (LocalStep caller) (Turing.initList (machine caller initial) raw) reached ∧
      (n < runSteps raw ↔ Owned reached.l) ∧
      (n = 0 → reached = Turing.initList (machine caller initial) raw) ∧
      reached.var = registersAt (Turing.initList (machine caller initial) raw) n ∧
      user reached.var = initial ∧
      (∀ k, reached.stk (.inr (.inr k)) = []) ∧
      finalCfg reached = Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw] ∧
      physicalCells reached ≤ max raw.length 1 ∧
      runSteps raw ≤ raw.length * raw.length + 10 * raw.length + 36 :=
  init_prefix caller initial raw n bound

theorem the_genuine_package_peak_is_both_an_upper_bound_and_attained
    (raw : Bits) :
    ExactPeak (machine caller initial).step (Turing.initList (machine caller initial) raw)
      (runSteps raw) (max raw.length 1) :=
  exact_peak_from_the_actual_public_prefix_contract caller (init_peak caller initial raw)

def arbitraryPackageConfigurationTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (machine caller initial).step start
      (some (finalCfg start)) (remainingSteps start) := machineCfgInTime caller initial start

def arbitraryPackagePhaseTime (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (cfg (some (phaseLabel q)) regs D ctx) (some (phaseResult q regs D ctx)) (phaseSteps q D) :=
  machinePhaseInTime caller initial q D regs ctx

theorem arbitrary_package_time_records_do_not_assume_actual_initialization
    (start : Cfg Γ Λ R) (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (arbitraryPackageConfigurationTime caller initial start).steps = remainingSteps start ∧
    (arbitraryPackagePhaseTime caller initial q D regs ctx).steps = phaseSteps q D := ⟨rfl, rfl⟩

end ActualPackageTiming

/-! ## Owned-only installations retain the canonical shared witness and closed halt tail -/

section InstalledCanonicalTiming

variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable [DecidableEq K] [DecidableEq K']
variable (names : StackId K ≃ K') (symbols : ∀ k, Alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable (caller : Λ → Statement Γ Λ R) (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
variable (installed : ∀ label, Owned (some label) →
  ambient (labels label) =
    FrontEndMachine.Transport.statement names symbols registers labels (program caller label))

include installed in
theorem the_actual_installed_first_halt_iff_needs_only_owned_body_agreement
    (start : Cfg Γ Λ R) (owned : Owned start.l) (n : Nat) (finish : Turing.TM2.Cfg Γ' Λ' R') :
    ((FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) = some finish ∧
      finish.l = none ∧
      ∀ j, j < n → ∃ reached,
        (FrontEndMachine.Transport.next ambient)^[j]
          (some (installedCfg names symbols registers labels start)) = some reached ∧
        InstalledOwned labels reached.l) ↔
      n = remainingSteps start ∧ finish = installedCfg names symbols registers labels (finalCfg start) :=
  installed_first_halt_iff names symbols registers labels caller ambient installed start owned n finish

include installed in
theorem all_installed_owned_start_iterates_include_the_real_halt_tail
    (start : Cfg Γ Λ R) (owned : Owned start.l) (n : Nat) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) :=
  installed_iterate_owned_start names symbols registers labels caller ambient installed start owned n

include installed in
theorem one_installed_prefix_witness_has_source_and_ambient_execution_and_the_complete_frame
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, Runs (step caller) start n reached ∧
      (FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) =
        some (installedCfg names symbols registers labels reached) ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ InstalledOwned labels (installedCfg names symbols registers labels reached).l) ∧
      (n = 0 → reached = start) ∧
      (installedCfg names symbols registers labels reached).var = registers (registersAt start n) ∧
      user reached.var = user start.var ∧
      (∀ k, (installedCfg names symbols registers labels reached).stk (names (.inr (.inr k))) =
        (start.stk (.inr (.inr k))).map (symbols (.inr (.inr k)))) ∧
      finalCfg reached = finalCfg start :=
  installed_owned_prefix_frame names symbols registers labels caller ambient installed start n bound

include installed in
def installedConfigurationExactTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start)
      (some (installedCfg names symbols registers labels (finalCfg start))) (remainingSteps start) :=
  installedOwnedInTime names symbols registers labels caller ambient installed start

include installed in
def installedPhaseExactTime (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels (cfg (some (phaseLabel q)) regs D ctx))
      (some (installedCfg names symbols registers labels (phaseResult q regs D ctx))) (phaseSteps q D) :=
  installedPhaseInTime names symbols registers labels caller ambient installed q D regs ctx

include installed in
def installedOuterNoneExactTime (start : Cfg Γ Λ R) (halted : (finalCfg start).l = none) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start) none (remainingSteps start + 1) :=
  installedHaltNoneInTime names symbols registers labels caller ambient installed start halted

theorem installed_type_valued_records_retain_the_exact_source_counts
    (start : Cfg Γ Λ R) (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (halted : (finalCfg start).l = none) :
    (installedConfigurationExactTime names symbols registers labels caller ambient installed start).steps =
      remainingSteps start ∧
    (installedPhaseExactTime names symbols registers labels caller ambient installed q D regs ctx).steps =
      phaseSteps q D ∧
    (installedOuterNoneExactTime names symbols registers labels caller ambient installed start halted).steps =
      remainingSteps start + 1 := ⟨rfl, rfl, rfl⟩

variable [Fintype K] [Fintype K']

include installed in
theorem the_same_installed_prefix_witness_carries_the_actual_full_physical_bound
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, Runs (step caller) start n reached ∧
      (FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) =
        some (installedCfg names symbols registers labels reached) ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ InstalledOwned labels (installedCfg names symbols registers labels reached).l) ∧
      (n = 0 → reached = start) ∧
      (installedCfg names symbols registers labels reached).var = registers (registersAt start n) ∧
      user reached.var = user start.var ∧
      (∀ k, (installedCfg names symbols registers labels reached).stk (names (.inr (.inr k))) =
        (start.stk (.inr (.inr k))).map (symbols (.inr (.inr k)))) ∧
      finalCfg reached = finalCfg start ∧
      (∑ k, ((installedCfg names symbols registers labels reached).stk k).length) ≤ allowance start :=
  installed_owned_prefix_space names symbols registers labels caller ambient installed start n bound

end InstalledCanonicalTiming

/-! ## Exact class clocks, endpoints, staged registers and structural allowances -/

theorem all_seven_owned_class_clock_formulas_use_the_actual_component_endpoint
    (f : FrontEndMachine.OwnedLabels) (s : StreamMachine.Phase) (i : Fin 16)
    (bit : Bool) (D : LocalData) :
    phaseSteps (frontEndPhase f) D =
      (DirtyFrontEnd.frontEndPhaseFinish f (frontEndData D)).steps +
      (match (DirtyFrontEnd.frontEndPhaseFinish f (frontEndData D)).result with
        | .success => (dispatchEvaluation (frontEndFinishData f D)).steps
        | .failure => (answerEvaluation false (frontEndFinishData f D)).steps) ∧
    phaseSteps rejectPhase D = localCells D + 18 ∧
    phaseSteps dispatchPhase D =
      StreamMachine.phaseSteps StreamMachine.inspectPhase (streamData D) +
      localCells (withStream D (StreamMachine.evaluate StreamMachine.inspectPhase (streamData D)).data) + 19 ∧
    phaseSteps (streamPhase s) D = StreamMachine.phaseSteps s (streamData D) +
      localCells (withStream D (StreamMachine.evaluate s (streamData D)).data) + 18 ∧
    phaseSteps (resultPhase bit) D = localCells D + 18 ∧
    phaseSteps (clearPhase i) D = suffixCells i D + (16 - i.val) + 1 ∧
    phaseSteps emitPhase D = 1 :=
  ⟨phaseSteps_frontEndPhase f D, phaseSteps_reject D, phaseSteps_dispatch D,
    phaseSteps_stream s D, phaseSteps_result bit D, phaseSteps_clear i D, phaseSteps_emit D⟩

theorem all_seven_owned_class_endpoints_keep_the_direct_cleaner_answer_and_dirty_emit_fuel
    {K Λ R : Type} {Γ : K → Type}
    (f : FrontEndMachine.OwnedLabels) (s : StreamMachine.Phase) (i : Fin 16)
    (bit : Bool) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) (frontEndPhase f) regs D ctx =
      cfg none (fullReset regs) (frontEndEvaluation f D).data ctx ∧
    phaseResult (Λ := Λ) rejectPhase regs D ctx = cfg none (fullReset regs) { fuel := [false] } ctx ∧
    phaseResult (Λ := Λ) dispatchPhase regs D ctx = cfg none (fullReset regs)
      { fuel := [(StreamMachine.evaluate StreamMachine.inspectPhase (streamData D)).result] } ctx ∧
    phaseResult (Λ := Λ) (streamPhase s) regs D ctx = cfg none (fullReset regs)
      { fuel := [(StreamMachine.evaluate s (streamData D)).result] } ctx ∧
    phaseResult (Λ := Λ) (resultPhase bit) regs D ctx = cfg none (fullReset regs) { fuel := [bit] } ctx ∧
    phaseResult (Λ := Λ) (clearPhase i) regs D ctx =
      cfg none (fullReset regs) (cleanupData i (answer regs) D) ctx ∧
    phaseResult (Λ := Λ) emitPhase regs D ctx =
      cfg none (fullReset regs) { D with fuel := answer regs :: D.fuel } ctx :=
  ⟨phaseResult_frontEndPhase f regs D ctx, phaseResult_reject regs D ctx,
    phaseResult_dispatch regs D ctx, phaseResult_stream s regs D ctx,
    phaseResult_result bit regs D ctx, phaseResult_clear i regs D ctx, phaseResult_emit regs D ctx⟩

section ActualStagedFields

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

theorem an_actual_front_end_prefix_uses_its_component_masks_before_the_paid_join
    (q : FrontEndMachine.OwnedLabels) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D))
    (reached : Cfg Γ Λ R)
    (executed : Runs (step caller) (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx) n reached) :
    reached.var = DirtyFrontEnd.frontEndPhaseRegisters q (frontEndData D) regs n ∧
    user reached.var = user regs ∧ ∀ k, reached.stk (.inr (.inr k)) = ctx k :=
  front_end_component_prefix_state caller q D regs ctx n bound reached executed

theorem an_actual_stream_prefix_keeps_the_complete_decoder_complement_and_staged_masks
    (q : StreamMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ StreamMachine.phaseSteps q (streamData D))
    (reached : Cfg Γ Λ R)
    (executed : Runs (step caller) (cfg (some (phaseLabel (streamPhase q))) regs D ctx) n reached) :
    reached.var = StreamMachine.frontEndRegisterEquiv.symm
      (StreamMachine.phaseRegistersAt (Λ := StreamCallerLabel Λ) q
        (StreamMachine.frontEndRegisterEquiv regs) (streamData D) (streamContext D ctx) n) ∧
    user reached.var = user regs ∧ ∀ k, reached.stk (.inr (.inr k)) = ctx k :=
  stream_component_prefix_state caller q D regs ctx n bound reached executed

theorem every_actual_indexed_clear_prefix_has_the_original_zero_fields_and_exact_positive_occupancy
    (i j : Fin 16) (t : Nat) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (ordered : i.val ≤ j.val) (within : t ≤ slotLength j D) :
    Runs (step caller) (cfg (some (clearLabel i)) regs D ctx) (boundarySteps i j D + t)
      (cleanupPrefixCfg i j t regs D ctx) ∧
    (cleanupPrefixCfg (Λ := Λ) i j t regs D ctx).var =
      (if t = 0 then (if i = j then regs else occupancyRegisters false regs)
       else occupancyRegisters true regs) :=
  ⟨cleanup_prefix_iterate caller i j t D regs ctx ordered within,
    cleanupPrefixCfg_registers i j t regs D ctx⟩

theorem every_actual_pre_emit_prefix_has_a_unique_slot_and_consumed_length
    (i : Fin 16) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (beforeEmit : n < cleanupSteps i D - 1) :
    ∃ j : Fin 16, i.val ≤ j.val ∧ ∃ t, t ≤ slotLength j D ∧
      n = boundarySteps i j D + t ∧
      Runs (step caller) (cfg (some (clearLabel i)) regs D ctx) n (cleanupPrefixCfg i j t regs D ctx) ∧
      ∀ k u, i.val ≤ k.val → u ≤ slotLength k D →
        n = boundarySteps i k D + u → k = j ∧ u = t :=
  clear_prefix caller i D regs ctx n beforeEmit

theorem the_last_empty_pop_reaches_emit_before_the_separate_answer_push
    (i : Fin 16) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (cfg (some (clearLabel i)) regs D ctx) (cleanupSteps i D - 1)
      (cfg (some emitLabel) (occupancyRegisters false regs) (clearSuffix i D) ctx) ∧
    Runs (step caller) (cfg (some (clearLabel i)) regs D ctx) (cleanupSteps i D)
      (cfg none (fullReset regs) (cleanupData i (answer regs) D) ctx) :=
  ⟨cleanup_emit_iterate caller i D regs ctx, (cleanup_localRun caller i D regs ctx).iterate caller⟩

def expectedCleanerFields (i : Fin 16) (regs : Registers R) (D : LocalData) (n : Nat) : Registers R :=
  if n = 0 then regs else
  if n = cleanupSteps i D - 1 then (regs.1, { regs.2.1 with b1 := some false }, regs.2.2) else
  if cleanupSteps i D ≤ n then fullReset regs else
  if ∃ j : Fin 16, i.val ≤ j.val ∧ n = boundarySteps i j D
  then (regs.1, { regs.2.1 with b1 := some false }, regs.2.2)
  else (regs.1, { regs.2.1 with b1 := some true }, regs.2.2)

theorem every_actual_clear_prefix_preserves_all_fields_except_the_recorded_occupancy_until_emit
    (i : Fin 16) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ cleanupSteps i D) (reached : Cfg Γ Λ R)
    (executed : Runs (step caller) (cfg (some (clearLabel i)) regs D ctx) n reached) :
    reached.var = expectedCleanerFields i regs D n ∧ user reached.var = user regs ∧
    ∀ k, reached.stk (.inr (.inr k)) = ctx k :=
  cleanup_prefix_registers caller i D regs ctx n bound reached executed

def frontEndSegmentTime (q : FrontEndMachine.OwnedLabels) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx)
      (some (frontEndComponentCfg q D regs ctx)) (DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D)) :=
  frontEndInTime caller q D regs ctx

def streamSegmentTime (q : StreamMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (streamPhase q))) regs D ctx)
      (some (cfg (some (phaseLabel (resultPhase (StreamMachine.evaluate q (streamData D)).result)))
        (streamReset regs) (withStream D (StreamMachine.evaluate q (streamData D)).data) ctx))
      (StreamMachine.phaseSteps q (streamData D)) := streamInTime caller q D regs ctx

theorem component_time_records_stop_at_the_owned_join_before_the_whole_phase_halt
    (f : FrontEndMachine.OwnedLabels) (s : StreamMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (frontEndSegmentTime caller f D regs ctx).steps = DirtyFrontEnd.frontEndPhaseSteps f (frontEndData D) ∧
    (streamSegmentTime caller s D regs ctx).steps = StreamMachine.phaseSteps s (streamData D) ∧
    (phaseExactTime caller (frontEndPhase f) D regs ctx).steps = phaseSteps (frontEndPhase f) D ∧
    (phaseExactTime caller (streamPhase s) D regs ctx).steps = phaseSteps (streamPhase s) D :=
  ⟨rfl, rfl, rfl, rfl⟩

end ActualStagedFields

section StructuralAllowanceEquations

variable {K : Type} {Γ : K → Type} [Fintype K]

def expectedFrontEndAllowance (q : FrontEndMachine.OwnedLabels) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : Nat :=
  let finish := DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)
  let out := withFrontEnd D finish.data
  max (localCells D + DirtyFrontEnd.frontEndPhaseCredit q (frontEndData D) + externalCells ctx)
    (match finish.result with
      | .success => max (StreamMachine.inspectAllowance (streamData out) (streamContext out ctx))
          (1 + externalCells ctx)
      | .failure => max (localCells out) 1 + externalCells ctx)

theorem the_front_end_allowance_uses_the_actual_dirty_endpoint_and_counts_its_protected_words_once
    (q : FrontEndMachine.OwnedLabels) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    phaseAllowance (frontEndPhase q) D ctx = expectedFrontEndAllowance q D ctx := by
  change (match frontEndClass (frontEndControl (.inl q)) with
    | .inl q => frontEndAllowance q D ctx
    | .inr false => max (localCells D) 1 + contextCells ctx
    | .inr true => max (StreamMachine.inspectAllowance (streamData D) (streamContext D ctx))
        (1 + contextCells ctx)) = _
  rw [frontEndClass_control]
  rfl

theorem all_other_owned_allowances_retain_the_emit_push_and_exact_cleaner_prefix_mass
    (q : StreamMachine.Phase) (i : Fin 16) (bit : Bool) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    phaseAllowance rejectPhase D ctx = max (localCells D) 1 + externalCells ctx ∧
    phaseAllowance dispatchPhase D ctx =
      max (StreamMachine.inspectAllowance (streamData D) (streamContext D ctx)) (1 + externalCells ctx) ∧
    phaseAllowance (streamPhase q) D ctx =
      max (StreamMachine.phaseAllowance q (streamData D) (streamContext D ctx)) (1 + externalCells ctx) ∧
    phaseAllowance (resultPhase bit) D ctx = max (localCells D) 1 + externalCells ctx ∧
    phaseAllowance (clearPhase i) D ctx = max (localCells D) (prefixCells i D + 1) + externalCells ctx ∧
    phaseAllowance emitPhase D ctx = localCells D + 1 + externalCells ctx := by
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩
  · change (match streamClass (streamControl (.inl q)) with
      | .inl q => max (StreamMachine.phaseAllowance q (streamData D) (streamContext D ctx))
          (1 + contextCells ctx)
      | .inr _ => max (localCells D) 1 + contextCells ctx) = _
    rw [streamClass_control]
    rfl
  · cases bit <;> rfl

end StructuralAllowanceEquations

/-! ## Full component configuration inverses and the external reentry boundary -/

section CompleteComponentViews

variable {K Λ R : Type} {Γ : K → Type}

def frontEndReadback (c : Cfg Γ Λ R) : FrontEndCfg Γ Λ R :=
  frontEndView (c.l.map frontEndLabelEquiv.symm) c.var (dataOfCfg c) (contextOfCfg c)

def streamReadback (c : Cfg Γ Λ R) : StreamCfg Γ Λ R :=
  streamView (c.l.map streamLabelEquiv.symm) c.var (dataOfCfg c) (contextOfCfg c)

theorem front_end_readback_restores_every_arbitrary_common_configuration
    (c : Cfg Γ Λ R) : frontEndCfg (frontEndReadback c) = c := by
  rw [frontEndReadback, frontEndCfg_view]
  have labels : (c.l.map frontEndLabelEquiv.symm).map frontEndLabelEquiv = c.l := by
    cases c.l <;> simp
  rw [labels, cfg_eta]

theorem stream_readback_restores_every_arbitrary_common_configuration
    (c : Cfg Γ Λ R) : streamCfg (streamReadback c) = c := by
  rw [streamReadback, streamCfg_view]
  have labels : (c.l.map streamLabelEquiv.symm).map streamLabelEquiv = c.l := by
    cases c.l <;> simp
  rw [labels, cfg_eta]

theorem both_complete_component_views_have_actual_two_sided_configuration_inverses
    (f : FrontEndCfg Γ Λ R) (s : StreamCfg Γ Λ R) (c : Cfg Γ Λ R) :
    frontEndCfg (frontEndReadback c) = c ∧ frontEndReadback (frontEndCfg f) = f ∧
    streamCfg (streamReadback c) = c ∧ streamReadback (streamCfg s) = s := by
  refine ⟨front_end_readback_restores_every_arbitrary_common_configuration c, ?_,
    stream_readback_restores_every_arbitrary_common_configuration c, ?_⟩
  · apply FrontEndMachine.Transport.cfg_injective (Equiv.refl _) (fun _ => Equiv.refl _)
      (Equiv.refl _) frontEndLabelEquiv frontEndLabelEquiv.injective
    exact front_end_readback_restores_every_arbitrary_common_configuration (frontEndCfg f)
  · apply FrontEndMachine.Transport.cfg_injective streamStackEquiv streamSymbolEquiv
      streamRegisterEquiv streamLabelEquiv streamLabelEquiv.injective
    exact stream_readback_restores_every_arbitrary_common_configuration (streamCfg s)

theorem sixteen_local_slots_and_original_external_stores_exhaust_the_physical_carrier
    (k : StackId K) : (∃ i : Fin 16, slot i = k) ∨ ∃ external, k = .inr (.inr external) :=
  slot_complete k

theorem each_literal_local_slot_has_its_unique_physical_index
    (i j : Fin 16) : slot (K := K) i = slot j ↔ i = j :=
  ⟨fun same => slot_injective (K := K) same,
    fun same => congrArg (slot (K := K)) same⟩

theorem every_symbol_equivalence_has_a_complete_inverse
    (k : StreamMachine.StackId (StreamMachine.FrontEndProtected ⊕ K))
    (symbol : StreamMachine.Alphabet (StreamMachine.FrontEndProtectedAlphabet Γ) k) :
    (streamSymbolEquiv k).symm (streamSymbolEquiv k symbol) = symbol :=
  (streamSymbolEquiv k).symm_apply_apply symbol

theorem both_component_maps_preserve_the_complete_physical_sum
    [Fintype K] (f : FrontEndCfg Γ Λ R) (s : StreamCfg Γ Λ R) :
    physicalCells (frontEndCfg f) = FrontEndMachine.stackCells f ∧
    physicalCells (streamCfg s) = StreamMachine.stackCells s :=
  ⟨stackCells_frontEndCfg f, stackCells_streamCfg s⟩

theorem the_component_label_complements_count_every_other_owned_domain
    [Fintype Λ] :
    Fintype.card (FrontEndCallerLabel Λ) = 58 + Fintype.card Λ ∧
    Fintype.card (StreamCallerLabel Λ) = 55 + Fintype.card Λ := by
  have f : Fintype.card (FrontEndMachine.Label Empty) = 38 := by
    simpa only [Fintype.card_empty, Nat.add_zero] using FrontEndMachine.label_card (Λ := Empty)
  have s : Fintype.card (StreamMachine.Label Empty) = 41 := by
    simpa only [Fintype.card_empty, Nat.add_zero] using StreamMachine.card_label (Λ := Empty)
  constructor
  · simp only [FrontEndCallerLabel, Fintype.card_sum, s, card_cleanupPhase]
    omega
  · simp only [StreamCallerLabel, Fintype.card_sum, f, card_cleanupPhase]
    omega

end CompleteComponentViews

section ExternalReentryScope

variable {K R : Type} {Γ : K → Type} [DecidableEq K]

def genericReenteringCaller : Nat → Statement Γ Nat R := fun _ => .goto (fun _ => clearLabel 0)

theorem an_external_reentry_executes_the_caller_before_any_owned_cleanup_step
    (label : Nat) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step genericReenteringCaller (cfg (some (callerLabel label)) regs D ctx) =
      some (cfg (some (clearLabel 0)) regs D ctx) := rfl

theorem an_external_reentry_can_later_halt_but_is_not_an_owned_first_halt
    (label : Nat) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstBoundary (step genericReenteringCaller)
      (cfg (some (callerLabel label)) regs D ctx) 0
      (cfg (some (callerLabel label)) regs D ctx) ∧
    Runs (step genericReenteringCaller) (cfg (some (callerLabel label)) regs D ctx)
      (1 + cleanupSteps 0 D) (cfg none (fullReset regs) (cleanupData 0 (answer regs) D) ctx) ∧
    ¬ FirstHalt (step genericReenteringCaller) (cfg (some (callerLabel label)) regs D ctx)
      (1 + cleanupSteps 0 D) (cfg none (fullReset regs) (cleanupData 0 (answer regs) D) ctx) := by
  refine ⟨external_first_boundary_is_zero_identity genericReenteringCaller label D regs ctx, ?_, ?_⟩
  · change (next genericReenteringCaller)^[1 + cleanupSteps 0 D]
      (some (cfg (some (callerLabel label)) regs D ctx)) = _
    rw [Nat.add_comm 1 _, Function.iterate_succ_apply, next_some,
      an_external_reentry_executes_the_caller_before_any_owned_cleanup_step]
    exact (cleanup_localRun genericReenteringCaller 0 D regs ctx).iterate genericReenteringCaller
  · intro alleged
    obtain ⟨reached, executed, owned⟩ := alleged.2.2 0 (by omega)
    have same := Option.some.inj executed
    subst reached
    exact not_owned_caller label owned

end ExternalReentryScope

/-! ## Component boundaries stay owned until their paid controller joins -/

section ComponentBoundaryDomains

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

theorem all_36_front_end_domains_reach_their_complete_owned_join_before_the_global_halt
    (q : FrontEndMachine.OwnedLabels) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx)
      (DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D)) (frontEndComponentCfg q D regs ctx) ∧
    Owned (frontEndComponentCfg (Λ := Λ) q D regs ctx).l ∧
    (∀ n, n < DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D) →
      ∃ reached, Runs (step caller) (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx)
        n reached ∧ Owned reached.l) ∧
    FirstHalt (step caller) (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx)
      (phaseSteps (frontEndPhase q) D) (phaseResult (frontEndPhase q) regs D ctx) := by
  have component := front_end_phase_localRun caller q D regs ctx
  refine ⟨component.iterate caller, ?_, component.owned_prefix caller,
    phase_first_halt caller (frontEndPhase q) D regs ctx⟩
  exact owned_phase _

theorem all_39_stream_domains_reach_their_complete_owned_boolean_join_before_the_global_halt
    (q : StreamMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (cfg (some (phaseLabel (streamPhase q))) regs D ctx)
      (StreamMachine.phaseSteps q (streamData D))
      (cfg (some (phaseLabel (resultPhase (StreamMachine.evaluate q (streamData D)).result)))
        (streamReset regs) (withStream D (StreamMachine.evaluate q (streamData D)).data) ctx) ∧
    Owned (some (phaseLabel (Λ := Λ) (resultPhase (StreamMachine.evaluate q (streamData D)).result))) ∧
    (∀ n, n < StreamMachine.phaseSteps q (streamData D) →
      ∃ reached, Runs (step caller) (cfg (some (phaseLabel (streamPhase q))) regs D ctx)
        n reached ∧ Owned reached.l) ∧
    FirstHalt (step caller) (cfg (some (phaseLabel (streamPhase q))) regs D ctx)
      (phaseSteps (streamPhase q) D) (phaseResult (streamPhase q) regs D ctx) := by
  have component := stream_phase_localRun caller q D regs ctx
  exact ⟨component.iterate caller, owned_phase _, component.owned_prefix caller,
    phase_first_halt caller (streamPhase q) D regs ctx⟩

theorem neither_component_result_is_already_a_global_first_boundary
    (f : FrontEndMachine.OwnedLabels) (s : StreamMachine.Phase)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ¬ FirstBoundary (step caller) (cfg (some (phaseLabel (frontEndPhase f))) regs D ctx)
        (DirtyFrontEnd.frontEndPhaseSteps f (frontEndData D)) (frontEndComponentCfg f D regs ctx) ∧
    ¬ FirstBoundary (step caller) (cfg (some (phaseLabel (streamPhase s))) regs D ctx)
        (StreamMachine.phaseSteps s (streamData D))
        (cfg (some (phaseLabel (resultPhase (StreamMachine.evaluate s (streamData D)).result)))
          (streamReset regs) (withStream D (StreamMachine.evaluate s (streamData D)).data) ctx) := by
  constructor
  · intro alleged
    exact alleged.2.1 (owned_phase _)
  · intro alleged
    exact alleged.2.1 (owned_phase _)

end ComponentBoundaryDomains

theorem the_81_fixed_closed_runs_retain_the_five_cell_context_and_stale_fields
    (caller : ExampleCaller) (value : Bool) :
    ∀ fixture ∈ allClosedCases,
      FirstHalt (step caller) (fixture.start value ordinaryContext) fixture.ticks
        (fixture.finish value ordinaryContext) ∧
      ExactPeak (step caller) (fixture.start value ordinaryContext) fixture.ticks (fixture.peak + 5) := by
  intro fixture member
  have connected := all_81_positive_closed_cases_have_their_actual_first_halt_and_exact_peak
    caller value ordinaryContext fixture member
  simpa only [ClosedFixture.Expected, ClosedFixture.RunExpected, ordinary_context_has_five_cells] using connected

end Examples.RotationCertificateFrontEndStreamMachine
