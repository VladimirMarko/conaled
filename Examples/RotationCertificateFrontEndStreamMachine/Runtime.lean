import Examples.RotationCertificateFrontEndStreamMachine.Fixtures

/-!
# RotationCertificateFrontEndStreamMachine: Runtime
-/

namespace Examples.RotationCertificateFrontEndStreamMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.FrontEndStreamMachine

/-! ## Complete finite carriers and physical maps -/

theorem cleanup_phase_count : Fintype.card CleanupPhase = 17 := by
  rw [← Fintype.card_congr cleanupPhaseEquiv]
  simp

theorem finite_dimensions_unit :
    Fintype.card (StackId (Fin 2)) = 18 ∧
    Fintype.card (Label Unit) = 97 ∧
    Fintype.card (Registers Bool) = 280908 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using card_stackId (K := Fin 2)
  · simpa only [Fintype.card_unit] using card_label (Λ := Unit)
  · simpa only [Fintype.card_bool] using card_registers (R := Bool)

theorem finite_dimensions_two :
    Fintype.card (StackId (Fin 2)) = 18 ∧
    Fintype.card (Label (Fin 2)) = 98 ∧
    Fintype.card (Registers Bool) = 280908 := by
  refine ⟨finite_dimensions_unit.1, ?_, finite_dimensions_unit.2.2⟩
  simpa only [Fintype.card_fin] using card_label (Λ := Fin 2)

theorem owned_dimensions_with_infinite_labels :
    Fintype.card (OwnedLabel Nat) = 96 := card_ownedLabel

theorem standalone_dimensions :
    Fintype.card (StackId Empty) = 16 ∧
    Fintype.card (Label Empty) = 96 ∧
    Fintype.card (Registers Unit) = 140454 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_empty, Nat.add_zero] using card_stackId (K := Empty)
  · simpa only [Fintype.card_empty, Nat.add_zero] using card_label (Λ := Empty)
  · simpa only [Fintype.card_unit, Nat.mul_one] using card_registers (R := Unit)

theorem all_reset_callbacks_preserve_the_exact_fields {R α : Type}
    (regs : Registers R) (bit : Bool) (head : Option α) :
    (fullReset regs).1 = (none, none) ∧
    (fullReset regs).2.1 = BitDecoderMachine.zeroRegisters ∧
    (fullReset regs).2.2 = (none, user regs) ∧
    answer (answerRegisters bit regs) = bit ∧
    (answerRegisters bit regs).2.2 = (none, user regs) ∧
    (observeOccupied regs head).1 = regs.1 ∧
    (observeOccupied regs head).2.1.b0 = regs.2.1.b0 ∧
    (observeOccupied regs head).2.1.b1 = some head.isSome ∧
    (observeOccupied regs head).2.1.b2 = regs.2.1.b2 ∧
    (observeOccupied regs head).2.1.b3 = regs.2.1.b3 ∧
    (observeOccupied regs head).2.1.tag = regs.2.1.tag ∧
    (observeOccupied regs head).2.2 = regs.2.2 := by
  exact ⟨rfl, rfl, rfl, answer_answerRegisters bit regs, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem front_end_reset_preserves_stale_branch_but_closed_reset_clears_it {R : Type}
    (regs : Registers R) :
    (FrontEndMachine.reset regs).2.2.1 = regs.2.2.1 ∧
    (fullReset regs).2.2.1 = none ∧
    (FrontEndMachine.reset regs).2.2.2 = user regs ∧
    (fullReset regs).2.2.2 = user regs := ⟨rfl, rfl, rfl, rfl⟩

theorem complete_cfg_keeps_all_local_and_original_words {K Λ R : Type} {Γ : K → Type}
    (label : Option (Label Λ)) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    dataOfCfg (cfg label regs D ctx) = D ∧
    contextOfCfg (cfg label regs D ctx) = ctx ∧
    (cfg label regs D ctx).var = regs ∧ (cfg label regs D ctx).l = label :=
  ⟨dataOfCfg_cfg label regs D ctx, contextOfCfg_cfg label regs D ctx, rfl, rfl⟩

theorem complete_component_label_maps_roundtrip {Λ : Type} (label : Label Λ) :
    frontEndLabelEquiv (frontEndLabelEquiv.symm label) = label ∧
    streamLabelEquiv (streamLabelEquiv.symm label) = label :=
  ⟨frontEndLabelEquiv.apply_symm_apply label, streamLabelEquiv.apply_symm_apply label⟩

theorem complete_stream_stack_and_register_maps_roundtrip {K R : Type}
    (k : StackId K) (regs : Registers R) :
    streamStackEquiv (streamStackEquiv.symm k) = k ∧
    streamRegisterEquiv (streamRegisterEquiv.symm regs) = regs :=
  ⟨streamStackEquiv.apply_symm_apply k, streamRegisterEquiv.apply_symm_apply regs⟩

theorem every_listed_domain_is_owned {Λ : Type} (q : Phase) (_member : q ∈ phaseDomains) :
    Owned (some (phaseLabel (Λ := Λ) q)) := owned_phase q

theorem ordinary_context_has_five_cells : externalCells ordinaryContext = 5 := by
  simp only [externalCells, Fin.sum_univ_two, ordinaryContext, independentWords]
  rfl

/-- Complete physical sum; no label or register finiteness is required. -/
theorem actual_physical_cells_of_cfg {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (label : Option (Label Λ)) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    physicalCells (cfg label regs D ctx) = localCells D + externalCells ctx := by
  have base := FrontEndMachine.stackCells_cfg (Λ := Empty) none regs
    (frontEndData D) (frontEndContext D ctx)
  have branchWords : (Finset.univ : Finset StreamMachine.NewBranchStores) =
      {.moveReverse, .path} := by
    ext k
    cases k <;> simp
  change FrontEndMachine.stackCells (FrontEndMachine.cfg (Λ := Empty) none regs
    (frontEndData D) (frontEndContext D ctx)) = _
  rw [base]
  simp only [FrontEndMachine.contextCells, Fintype.sum_sum_type, branchWords]
  simp only [Finset.sum_insert, Finset.mem_singleton, reduceCtorEq, not_false_eq_true,
    Finset.sum_singleton]
  change FrontEndMachine.localCells (frontEndData D) +
    (D.moveReverse.length + D.path.length + externalCells ctx) = _
  simp only [FrontEndMachine.localCells, frontEndData, localCells]
  omega

section ActualRuntimeConnections

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
  (caller : Λ → Statement Γ Λ R)

theorem first_halt_of_actual_local_run {n : Nat} {start finish : Cfg Γ Λ R}
    (executed : LocalRun caller n start finish) (halted : finish.l = none) :
    FirstHalt (step caller) start n finish := by
  exact ⟨executed.iterate caller, halted, executed.owned_prefix caller⟩

theorem first_boundary_of_actual_local_run {n : Nat} {start finish : Cfg Γ Λ R}
    (executed : LocalRun caller n start finish) (external : ¬ Owned finish.l) :
    FirstBoundary (step caller) start n finish := by
  exact ⟨executed.iterate caller, external, executed.owned_prefix caller⟩

theorem first_halt_is_a_first_boundary {n : Nat} {start finish : Cfg Γ Λ R}
    (first : FirstHalt (step caller) start n finish) :
    FirstBoundary (step caller) start n finish := by
  refine ⟨first.1, ?_, first.2.2⟩
  rw [first.2.1]
  exact not_owned_none

theorem actual_first_boundaries_fix_both_time_and_every_field
    {n m : Nat} {start finish other : Cfg Γ Λ R}
    (first : FirstBoundary (step caller) start n finish)
    (second : FirstBoundary (step caller) start m other) : n = m ∧ finish = other :=
  LocalRun.first_unique caller (LocalRun.of_iterate caller first.1 first.2.2)
    (LocalRun.of_iterate caller second.1 second.2.2) first.2.1 second.2.1

theorem all_four_new_joins_execute_one_actual_step (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel rejectPhase)) regs D ctx) =
      some (cfg (some (clearLabel 0)) (answerRegisters false regs) D ctx) ∧
    step caller (cfg (some (phaseLabel dispatchPhase)) regs D ctx) =
      some (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase))) (fullReset regs) D ctx) ∧
    step caller (cfg (some (phaseLabel (resultPhase false))) regs D ctx) =
      some (cfg (some (clearLabel 0)) (answerRegisters false regs) D ctx) ∧
    step caller (cfg (some (phaseLabel (resultPhase true))) regs D ctx) =
      some (cfg (some (clearLabel 0)) (answerRegisters true regs) D ctx) :=
  ⟨reject_step caller D regs ctx, dispatch_step caller D regs ctx,
    result_step caller false D regs ctx, result_step caller true D regs ctx⟩

theorem direct_emit_preserves_other_words_and_pushes_old_fuel
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstHalt (step caller) (cfg (some emitLabel) regs D ctx) 1
      (cfg none (fullReset regs) { D with fuel := answer regs :: D.fuel } ctx) :=
  first_halt_of_actual_local_run caller
    (phase_step_localRun caller (q := emitPhase) (emit_step caller D regs ctx)) rfl

theorem live_halt_has_zero_first_halt_and_keeps_all_dirty_fields
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstHalt (step caller) (cfg none regs D ctx) 0 (cfg none regs D ctx) ∧
    next caller (some (cfg none regs D ctx)) = none := by
  refine ⟨⟨rfl, rfl, ?_⟩, rfl⟩
  intro n strict
  omega

theorem external_first_boundary_is_zero_identity
    (label : Λ) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstBoundary (step caller) (cfg (some (callerLabel label)) regs D ctx) 0
      (cfg (some (callerLabel label)) regs D ctx) := by
  refine ⟨rfl, not_owned_caller label, ?_⟩
  intro n strict
  omega

theorem outer_none_stays_none (n : Nat) : (next caller)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, next_none]

end ActualRuntimeConnections

section EmitPhysicalPeak

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
  (caller : Λ → Statement Γ Λ R)

theorem direct_emitter_has_exact_inclusive_peak
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cfg (some emitLabel) regs D ctx) 1
      (localCells D + 1 + externalCells ctx) := by
  let start : Cfg Γ Λ R := cfg (some emitLabel) regs D ctx
  let finish : Cfg Γ Λ R := cfg none (fullReset regs) (emitData (answer regs) D) ctx
  have one : Runs (step caller) start 1 finish := (direct_emit_preserves_other_words_and_pushes_old_fuel
    caller D regs ctx).1
  have startCells : physicalCells start = localCells D + externalCells ctx :=
    actual_physical_cells_of_cfg _ _ _ _
  have endCells : physicalCells finish = localCells D + 1 + externalCells ctx := by
    rw [show finish = cfg none (fullReset regs) (emitData (answer regs) D) ctx from rfl,
      actual_physical_cells_of_cfg]
    simp only [localCells, emitData, List.length_cons]
    omega
  constructor
  · intro n bound reached executed
    have which : n = 0 ∨ n = 1 := by omega
    rcases which with rfl | rfl
    · have same : start = reached := Option.some.inj executed
      subst reached
      rw [startCells]
      omega
    · have same : finish = reached := Option.some.inj (one.symm.trans executed)
      subst reached
      exact Nat.le_of_eq endCells
  · exact ⟨1, finish, by omega, one, endCells⟩

end EmitPhysicalPeak

/-! ## The exact arbitrary suffix cleaner -/

/-- Independent suffix formula: every earlier word is literal and fuel is one bit. -/
def expectedCleanupData (i : Fin 16) (bit : Bool) (D : LocalData) : LocalData where
  framedRaw := if 0 < i.val then D.framedRaw else []
  frameFirstReverse := if 1 < i.val then D.frameFirstReverse else []
  frameCertReverse := if 2 < i.val then D.frameCertReverse else []
  inputBits := if 3 < i.val then D.inputBits else []
  certificateBits := if 4 < i.val then D.certificateBits else []
  inputRaw := if 5 < i.val then D.inputRaw else []
  decodeReverse := if 6 < i.val then D.decodeReverse else []
  certificateWord := if 7 < i.val then D.certificateWord else []
  sourceTree := if 8 < i.val then D.sourceTree else []
  targetTree := if 9 < i.val then D.targetTree else []
  treeReverse := if 10 < i.val then D.treeReverse else []
  pending := if 11 < i.val then D.pending else []
  bitsReverse := if 12 < i.val then D.bitsReverse else []
  moveReverse := if 13 < i.val then D.moveReverse else []
  path := if 14 < i.val then D.path else []
  fuel := [bit]

theorem actual_cleanup_data_is_the_independent_suffix_formula
    (i : Fin 16) (bit : Bool) (D : LocalData) :
    cleanupData i bit D = expectedCleanupData i bit D := by
  fin_cases i <;> rfl

section CleanupActualRuns

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
  (caller : Λ → Statement Γ Λ R)

theorem cleanup_all_suffixes_execute (i : Fin 16) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstHalt (step caller) (cfg (some (clearLabel i)) regs D ctx)
      (suffixCells i D + (16 - i.val) + 1)
      (cfg none (fullReset regs) (expectedCleanupData i (answer regs) D) ctx) := by
  have run := first_halt_of_actual_local_run caller (cleanup_localRun caller i D regs ctx) rfl
  rw [actual_cleanup_data_is_the_independent_suffix_formula] at run
  exact run

theorem cleanup_current_word_positive_prefix_preserves_the_original_registers_at_zero
    (i : Fin 16) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ slotLength i D) :
    Runs (step caller) (cfg (some (clearLabel i)) regs D ctx) n
      (cfg (some (clearLabel i)) (if n = 0 then regs else occupancyRegisters true regs)
        (dropData i n D) ctx) :=
  (drain_slot_localRun caller i D regs ctx n bound).iterate caller

theorem cleanup_last_occupied_pop_and_the_empty_probe_are_distinct
    (i : Fin 16) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (nonempty : slotLength i D ≠ 0) :
    Runs (step caller) (cfg (some (clearLabel i)) regs D ctx) (slotLength i D)
      (cfg (some (clearLabel i)) (occupancyRegisters true regs) (emptySlot i D) ctx) ∧
    Runs (step caller) (cfg (some (clearLabel i)) regs D ctx) (slotLength i D + 1)
      (cfg (some (nextClear i)) (occupancyRegisters false regs) (emptySlot i D) ctx) := by
  constructor
  · change (next caller)^[slotLength i D]
      (some (cfg (some (clearLabel i)) regs D ctx)) =
      some (cfg (some (clearLabel i)) (occupancyRegisters true regs) (emptySlot i D) ctx)
    simpa only [emptySlot, drainRegisters, nonempty, ite_false] using
      (drain_slot_localRun caller i D regs ctx (slotLength i D) (Nat.le_refl _)).iterate caller
  · exact (clear_slot_localRun caller i D regs ctx).iterate caller

theorem rejecting_join_has_its_whole_halt_after_the_paid_activation
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstHalt (step caller) (cfg (some (phaseLabel rejectPhase)) regs D ctx)
      (1 + cleanupSteps 0 D)
      (cfg none (fullReset regs) (cleanupData 0 false D) ctx) := by
  have head := phase_step_localRun caller (reject_step caller D regs ctx)
  have tail := cleanup_localRun caller 0 D (answerRegisters false regs) ctx
  have run := LocalRun.trans caller head tail
  simp only [fullReset_answerRegisters, answer_answerRegisters] at run
  exact first_halt_of_actual_local_run caller run rfl

theorem boolean_join_has_its_whole_halt_after_the_paid_activation
    (bit : Bool) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstHalt (step caller) (cfg (some (phaseLabel (resultPhase bit))) regs D ctx)
      (1 + cleanupSteps 0 D)
      (cfg none (fullReset regs) (cleanupData 0 bit D) ctx) := by
  have head := phase_step_localRun caller (result_step caller bit D regs ctx)
  have tail := cleanup_localRun caller 0 D (answerRegisters bit regs) ctx
  have run := LocalRun.trans caller head tail
  simp only [fullReset_answerRegisters, answer_answerRegisters] at run
  exact first_halt_of_actual_local_run caller run rfl

theorem clear_C00_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C00.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 0 clear_C00.before (clear_C00.fields.withUser value) ctx

theorem clear_C00E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C00E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 0 clear_C00E.before (clear_C00E.fields.withUser value) ctx

theorem clear_C01_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C01.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 1 clear_C01.before (clear_C01.fields.withUser value) ctx

theorem clear_C01E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C01E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 1 clear_C01E.before (clear_C01E.fields.withUser value) ctx

theorem clear_C02_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C02.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 2 clear_C02.before (clear_C02.fields.withUser value) ctx

theorem clear_C02E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C02E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 2 clear_C02E.before (clear_C02E.fields.withUser value) ctx

theorem clear_C03_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C03.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 3 clear_C03.before (clear_C03.fields.withUser value) ctx

theorem clear_C03E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C03E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 3 clear_C03E.before (clear_C03E.fields.withUser value) ctx

theorem clear_C04_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C04.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 4 clear_C04.before (clear_C04.fields.withUser value) ctx

theorem clear_C04E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C04E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 4 clear_C04E.before (clear_C04E.fields.withUser value) ctx

theorem clear_C05_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C05.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 5 clear_C05.before (clear_C05.fields.withUser value) ctx

theorem clear_C05E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C05E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 5 clear_C05E.before (clear_C05E.fields.withUser value) ctx

theorem clear_C06_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C06.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 6 clear_C06.before (clear_C06.fields.withUser value) ctx

theorem clear_C06E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C06E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 6 clear_C06E.before (clear_C06E.fields.withUser value) ctx

theorem clear_C07_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C07.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 7 clear_C07.before (clear_C07.fields.withUser value) ctx

theorem clear_C07E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C07E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 7 clear_C07E.before (clear_C07E.fields.withUser value) ctx

theorem clear_C08_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C08.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 8 clear_C08.before (clear_C08.fields.withUser value) ctx

theorem clear_C08E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C08E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 8 clear_C08E.before (clear_C08E.fields.withUser value) ctx

theorem clear_C09_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C09.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 9 clear_C09.before (clear_C09.fields.withUser value) ctx

theorem clear_C09E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C09E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 9 clear_C09E.before (clear_C09E.fields.withUser value) ctx

theorem clear_C10_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C10.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 10 clear_C10.before (clear_C10.fields.withUser value) ctx

theorem clear_C10E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C10E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 10 clear_C10E.before (clear_C10E.fields.withUser value) ctx

theorem clear_C11_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C11.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 11 clear_C11.before (clear_C11.fields.withUser value) ctx

theorem clear_C11E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C11E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 11 clear_C11E.before (clear_C11E.fields.withUser value) ctx

theorem clear_C12_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C12.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 12 clear_C12.before (clear_C12.fields.withUser value) ctx

theorem clear_C12E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C12E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 12 clear_C12E.before (clear_C12E.fields.withUser value) ctx

theorem clear_C13_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C13.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 13 clear_C13.before (clear_C13.fields.withUser value) ctx

theorem clear_C13E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C13E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 13 clear_C13E.before (clear_C13E.fields.withUser value) ctx

theorem clear_C14_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C14.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 14 clear_C14.before (clear_C14.fields.withUser value) ctx

theorem clear_C14E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C14E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 14 clear_C14E.before (clear_C14E.fields.withUser value) ctx

theorem clear_C15_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C15.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 15 clear_C15.before (clear_C15.fields.withUser value) ctx

theorem clear_C15E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C15E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 15 clear_C15E.before (clear_C15E.fields.withUser value) ctx

theorem emit_E00_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    emit_E00.toClosedFixture.RunExpected (step caller) value ctx :=
  direct_emit_preserves_other_words_and_pushes_old_fuel caller emit_E00.before (emit_E00.fields.withUser value) ctx

theorem emit_E01_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    emit_E01.toClosedFixture.RunExpected (step caller) value ctx :=
  direct_emit_preserves_other_words_and_pushes_old_fuel caller emit_E01.before (emit_E01.fields.withUser value) ctx

theorem emit_E02_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    emit_E02.toClosedFixture.RunExpected (step caller) value ctx :=
  direct_emit_preserves_other_words_and_pushes_old_fuel caller emit_E02.before (emit_E02.fields.withUser value) ctx

theorem emit_E03_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    emit_E03.toClosedFixture.RunExpected (step caller) value ctx :=
  direct_emit_preserves_other_words_and_pushes_old_fuel caller emit_E03.before (emit_E03.fields.withUser value) ctx

theorem join_J00_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    join_J00.toClosedFixture.RunExpected (step caller) value ctx :=
  rejecting_join_has_its_whole_halt_after_the_paid_activation caller join_J00.before (join_J00.fields.withUser value) ctx

theorem join_J01_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    join_J01.toClosedFixture.RunExpected (step caller) value ctx :=
  boolean_join_has_its_whole_halt_after_the_paid_activation caller false join_J01.before (join_J01.fields.withUser value) ctx

theorem join_J02_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    join_J02.toClosedFixture.RunExpected (step caller) value ctx :=
  boolean_join_has_its_whole_halt_after_the_paid_activation caller true join_J02.before (join_J02.fields.withUser value) ctx

theorem clear_CZERO_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_CZERO.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 0 clear_CZERO.before (clear_CZERO.fields.withUser value) ctx

theorem all_partial_clear_cases_execute (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ fixture ∈ partialClearCases, fixture.toClosedFixture.RunExpected (step caller) value ctx := by
  intro fixture member
  simp only [partialClearCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact clear_C00_actual_first_halt caller value ctx
  · exact clear_C00E_actual_first_halt caller value ctx
  · exact clear_C01_actual_first_halt caller value ctx
  · exact clear_C01E_actual_first_halt caller value ctx
  · exact clear_C02_actual_first_halt caller value ctx
  · exact clear_C02E_actual_first_halt caller value ctx
  · exact clear_C03_actual_first_halt caller value ctx
  · exact clear_C03E_actual_first_halt caller value ctx
  · exact clear_C04_actual_first_halt caller value ctx
  · exact clear_C04E_actual_first_halt caller value ctx
  · exact clear_C05_actual_first_halt caller value ctx
  · exact clear_C05E_actual_first_halt caller value ctx
  · exact clear_C06_actual_first_halt caller value ctx
  · exact clear_C06E_actual_first_halt caller value ctx
  · exact clear_C07_actual_first_halt caller value ctx
  · exact clear_C07E_actual_first_halt caller value ctx
  · exact clear_C08_actual_first_halt caller value ctx
  · exact clear_C08E_actual_first_halt caller value ctx
  · exact clear_C09_actual_first_halt caller value ctx
  · exact clear_C09E_actual_first_halt caller value ctx
  · exact clear_C10_actual_first_halt caller value ctx
  · exact clear_C10E_actual_first_halt caller value ctx
  · exact clear_C11_actual_first_halt caller value ctx
  · exact clear_C11E_actual_first_halt caller value ctx
  · exact clear_C12_actual_first_halt caller value ctx
  · exact clear_C12E_actual_first_halt caller value ctx
  · exact clear_C13_actual_first_halt caller value ctx
  · exact clear_C13E_actual_first_halt caller value ctx
  · exact clear_C14_actual_first_halt caller value ctx
  · exact clear_C14E_actual_first_halt caller value ctx
  · exact clear_C15_actual_first_halt caller value ctx
  · exact clear_C15E_actual_first_halt caller value ctx

end CleanupActualRuns

/-! ## The original FE measurements keep source costs separate from machine time -/

structure FrontEndMeasurements where
  framingTicks : Nat
  inputDecoderTicks : Option Nat
  inputParserTicks : Option Nat
  certificateDecoderTicks : Option Nat
  inputUnpackCost : Option Nat
  inputParseCost : Option Nat
  certificateUnpackCost : Option Nat
  totalFrontEndTicks : Nat
  deriving DecidableEq

/-- Observations of the existing component definitions; this is not controller execution. -/
def observeFrontEndMeasurements (raw : Bits) : FrontEndMeasurements :=
  let f := BitPairFraming.runSteps raw
  match BitPairFraming.unframe raw with
  | none => ⟨f, none, none, none, none, none, none, FrontEndMachine.runSteps raw⟩
  | some (input, cert) =>
    let dI := OpenDecoderMachine.runSteps input
    let cI := (unpackWordRun input).2
    match (unpackWordRun input).1 with
    | none => ⟨f, some dI, none, none, some cI, none, none, FrontEndMachine.runSteps raw⟩
    | some word =>
      let pI := InputParserMachine.inputSteps word
      let cP := (parseInputRun word).2
      match (parseInputRun word).1 with
      | none => ⟨f, some dI, some pI, none, some cI, some cP, none,
          FrontEndMachine.runSteps raw⟩
      | some _ => ⟨f, some dI, some pI, some (OpenDecoderMachine.runSteps cert),
          some cI, some cP, some (unpackWordRun cert).2, FrontEndMachine.runSteps raw⟩

structure SourceObservation where
  fixture : RawFixture
  measurements : FrontEndMeasurements

def SourceObservation.Expected (observation : SourceObservation) : Prop :=
  observeFrontEndMeasurements observation.fixture.raw = observation.measurements ∧
  BitPairFraming.verifyFramed observation.fixture.raw = observation.fixture.result

def source_F01 : SourceObservation :=
  ⟨emptyRawFixture, ⟨2, none, none, none, none, none, none, 2⟩⟩

theorem source_F01_has_its_original_component_tariffs : source_F01.Expected := by
  constructor <;> rfl

def source_F02 : SourceObservation :=
  ⟨truncatedPrefixFixture, ⟨2, none, none, none, none, none, none, 2⟩⟩

theorem source_F02_has_its_original_component_tariffs : source_F02.Expected := by
  constructor <;> rfl

def source_F03 : SourceObservation :=
  ⟨raw_F03, ⟨4, none, none, none, none, none, none, 4⟩⟩

theorem source_F03_has_its_original_component_tariffs : source_F03.Expected := by
  constructor <;> rfl

def source_F04 : SourceObservation :=
  ⟨raw_F04, ⟨4, none, none, none, none, none, none, 4⟩⟩

theorem source_F04_has_its_original_component_tariffs : source_F04.Expected := by
  constructor <;> rfl

def source_F05 : SourceObservation :=
  ⟨raw_F05, ⟨4, some 2, some 5, none, some 2, some 4, none, 11⟩⟩

theorem source_F05_has_its_original_component_tariffs : source_F05.Expected := by
  constructor <;> rfl

def source_F06 : SourceObservation :=
  ⟨raw_F06, ⟨6, some 2, some 5, none, some 2, some 4, none, 13⟩⟩

theorem source_F06_has_its_original_component_tariffs : source_F06.Expected := by
  constructor <;> rfl

def source_F07 : SourceObservation :=
  ⟨raw_F07, ⟨6, some 2, none, none, some 2, none, none, 8⟩⟩

theorem source_F07_has_its_original_component_tariffs : source_F07.Expected := by
  constructor <;> rfl

def source_F08 : SourceObservation :=
  ⟨raw_F08, ⟨12, some 2, none, none, some 2, none, none, 14⟩⟩

theorem source_F08_has_its_original_component_tariffs : source_F08.Expected := by
  constructor <;> rfl

def source_I01 : SourceObservation :=
  ⟨raw_I01, ⟨12, some 4, some 9, none, some 6, some 7, none, 25⟩⟩

theorem source_I01_has_its_original_component_tariffs : source_I01.Expected := by
  constructor <;> rfl

def source_I02 : SourceObservation :=
  ⟨raw_I02, ⟨14, some 4, some 5, none, some 6, some 4, none, 23⟩⟩

theorem source_I02_has_its_original_component_tariffs : source_I02.Expected := by
  constructor <;> rfl

def source_I03 : SourceObservation :=
  ⟨raw_I03, ⟨36, some 10, some 9, none, some 18, some 7, none, 55⟩⟩

theorem source_I03_has_its_original_component_tariffs : source_I03.Expected := by
  constructor <;> rfl

def source_I04 : SourceObservation :=
  ⟨raw_I04, ⟨52, some 14, some 26, none, some 26, some 15, none, 92⟩⟩

theorem source_I04_has_its_original_component_tariffs : source_I04.Expected := by
  constructor <;> rfl

def source_I05 : SourceObservation :=
  ⟨raw_I05, ⟨52, some 14, some 22, none, some 26, some 14, none, 88⟩⟩

theorem source_I05_has_its_original_component_tariffs : source_I05.Expected := by
  constructor <;> rfl

def source_I06 : SourceObservation :=
  ⟨raw_I06, ⟨116, some 26, some 12, none, some 50, some 11, none, 154⟩⟩

theorem source_I06_has_its_original_component_tariffs : source_I06.Expected := by
  constructor <;> rfl

def source_I07 : SourceObservation :=
  ⟨raw_I07, ⟨44, some 12, some 5, none, some 22, some 4, none, 61⟩⟩

theorem source_I07_has_its_original_component_tariffs : source_I07.Expected := by
  constructor <;> rfl

def source_C01 : SourceObservation :=
  ⟨raw_C01, ⟨46, some 12, some 13, some 2, some 22, some 15, some 2, 73⟩⟩

theorem source_C01_has_its_original_component_tariffs : source_C01.Expected := by
  constructor <;> rfl

def source_C02 : SourceObservation :=
  ⟨raw_C02, ⟨70, some 16, some 17, some 4, some 30, some 21, some 4, 107⟩⟩

theorem source_C02_has_its_original_component_tariffs : source_C02.Expected := by
  constructor <;> rfl

def source_C03 : SourceObservation :=
  ⟨raw_C03, ⟨134, some 30, some 31, some 6, some 58, some 46, some 6, 201⟩⟩

theorem source_C03_has_its_original_component_tariffs : source_C03.Expected := by
  constructor <;> rfl

def source_V01 : SourceObservation :=
  ⟨raw_V01, ⟨44, some 12, some 13, some 2, some 22, some 15, some 2, 71⟩⟩

theorem source_V01_has_its_original_component_tariffs : source_V01.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [] (.nil : BinaryTree Unit)
      (.nil : BinaryTree Unit) []).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V02 : SourceObservation :=
  ⟨raw_V02, ⟨60, some 16, some 17, some 2, some 30, some 22, some 2, 95⟩⟩

theorem source_V02_has_its_original_component_tariffs : source_V02.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [] (.nil : BinaryTree Unit)
      (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) []).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V03 : SourceObservation :=
  ⟨raw_V03, ⟨132, some 30, some 31, some 6, some 58, some 46, some 10, 199⟩⟩

theorem source_V03_has_its_original_component_tariffs : source_V03.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 10]).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V04 : SourceObservation :=
  ⟨raw_V04, ⟨132, some 30, some 31, some 6, some 58, some 46, some 10, 199⟩⟩

theorem source_V04_has_its_original_component_tariffs : source_V04.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [7, 10]).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V05 : SourceObservation :=
  ⟨raw_V05, ⟨156, some 32, some 33, some 10, some 62, some 49, some 18, 231⟩⟩

theorem source_V05_has_its_original_component_tariffs : source_V05.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [false, true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [6, 10, 7, 10]).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V06 : SourceObservation :=
  ⟨raw_V06, ⟨148, some 30, some 31, some 10, some 58, some 46, some 18, 219⟩⟩

theorem source_V06_has_its_original_component_tariffs : source_V06.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [6, 10, 7, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V07 : SourceObservation :=
  ⟨raw_V07, ⟨140, some 32, some 33, some 6, some 62, some 49, some 10, 211⟩⟩

theorem source_V07_has_its_original_component_tariffs : source_V07.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [false, false] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [6, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V08 : SourceObservation :=
  ⟨raw_V08, ⟨148, some 34, some 35, some 6, some 66, some 52, some 10, 223⟩⟩

theorem source_V08_has_its_original_component_tariffs : source_V08.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true, false, false] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 10]).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V09 : SourceObservation :=
  ⟨raw_V09, ⟨124, some 30, some 31, some 4, some 58, some 46, some 6, 189⟩⟩

theorem source_V09_has_its_original_component_tariffs : source_V09.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V10 : SourceObservation :=
  ⟨raw_V10, ⟨140, some 30, some 31, some 8, some 58, some 46, some 14, 209⟩⟩

theorem source_V10_has_its_original_component_tariffs : source_V10.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 15, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V11 : SourceObservation :=
  ⟨raw_V11, ⟨140, some 30, some 31, some 8, some 58, some 46, some 14, 209⟩⟩

theorem source_V11_has_its_original_component_tariffs : source_V11.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 8, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V12 : SourceObservation :=
  ⟨raw_V12, ⟨132, some 30, some 31, some 6, some 58, some 46, some 10, 199⟩⟩

theorem source_V12_has_its_original_component_tariffs : source_V12.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [7, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V13 : SourceObservation :=
  ⟨raw_V13, ⟨172, some 38, some 39, some 8, some 74, some 60, some 14, 257⟩⟩

theorem source_V13_has_its_original_component_tariffs : source_V13.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))))
      (.node () (.nil : BinaryTree Unit) (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit))) [6, 9, 10]).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V14 : SourceObservation :=
  ⟨raw_V14, ⟨140, some 30, some 31, some 8, some 58, some 46, some 14, 209⟩⟩

theorem source_V14_has_its_original_component_tariffs : source_V14.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 10, 15]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V15 : SourceObservation :=
  ⟨raw_V15, ⟨60, some 16, some 17, some 2, some 30, some 21, some 2, 95⟩⟩

theorem source_V15_has_its_original_component_tariffs : source_V15.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [false, false] (.nil : BinaryTree Unit)
      (.nil : BinaryTree Unit) []).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V16 : SourceObservation :=
  ⟨raw_V16, ⟨124, some 30, some 31, some 4, some 58, some 46, some 6, 189⟩⟩

theorem source_V16_has_its_original_component_tariffs : source_V16.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [15]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V17 : SourceObservation :=
  ⟨raw_V17, ⟨68, some 14, some 15, some 6, some 26, some 18, some 10, 103⟩⟩

theorem source_V17_has_its_original_component_tariffs : source_V17.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.nil : BinaryTree Unit)
      (.nil : BinaryTree Unit) [6, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V18 : SourceObservation :=
  ⟨raw_V18, ⟨124, some 28, some 29, some 6, some 54, some 43, some 10, 187⟩⟩

theorem source_V18_has_its_original_component_tariffs : source_V18.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def originalSourceObservations : List SourceObservation :=
  [source_F01, source_F02, source_F03, source_F04, source_F05, source_F06, source_F07, source_F08, source_I01, source_I02, source_I03, source_I04, source_I05, source_I06, source_I07, source_C01, source_C02, source_C03, source_V01, source_V02, source_V03, source_V04, source_V05, source_V06, source_V07, source_V08, source_V09, source_V10, source_V11, source_V12, source_V13, source_V14, source_V15, source_V16, source_V17, source_V18]

theorem original_source_observations_count : originalSourceObservations.length = 36 := rfl

theorem original_source_observations_keep_their_own_tariffs :
    ∀ observation ∈ originalSourceObservations, observation.Expected := by
  intro observation member
  simp only [originalSourceObservations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact source_F01_has_its_original_component_tariffs
  · exact source_F02_has_its_original_component_tariffs
  · exact source_F03_has_its_original_component_tariffs
  · exact source_F04_has_its_original_component_tariffs
  · exact source_F05_has_its_original_component_tariffs
  · exact source_F06_has_its_original_component_tariffs
  · exact source_F07_has_its_original_component_tariffs
  · exact source_F08_has_its_original_component_tariffs
  · exact source_I01_has_its_original_component_tariffs
  · exact source_I02_has_its_original_component_tariffs
  · exact source_I03_has_its_original_component_tariffs
  · exact source_I04_has_its_original_component_tariffs
  · exact source_I05_has_its_original_component_tariffs
  · exact source_I06_has_its_original_component_tariffs
  · exact source_I07_has_its_original_component_tariffs
  · exact source_C01_has_its_original_component_tariffs
  · exact source_C02_has_its_original_component_tariffs
  · exact source_C03_has_its_original_component_tariffs
  · exact source_V01_has_its_original_component_tariffs
  · exact source_V02_has_its_original_component_tariffs
  · exact source_V03_has_its_original_component_tariffs
  · exact source_V04_has_its_original_component_tariffs
  · exact source_V05_has_its_original_component_tariffs
  · exact source_V06_has_its_original_component_tariffs
  · exact source_V07_has_its_original_component_tariffs
  · exact source_V08_has_its_original_component_tariffs
  · exact source_V09_has_its_original_component_tariffs
  · exact source_V10_has_its_original_component_tariffs
  · exact source_V11_has_its_original_component_tariffs
  · exact source_V12_has_its_original_component_tariffs
  · exact source_V13_has_its_original_component_tariffs
  · exact source_V14_has_its_original_component_tariffs
  · exact source_V15_has_its_original_component_tariffs
  · exact source_V16_has_its_original_component_tariffs
  · exact source_V17_has_its_original_component_tariffs
  · exact source_V18_has_its_original_component_tariffs

/-- These tariffs refer to the unframed source verifier, not the physical closed clock. -/
theorem all_four_source_tariffs_keep_their_original_priority
    (input cert : Bits) :
    ((unpackWordRun input).1 = none →
      verifyBitsRun input cert = (false, (unpackWordRun input).2 + 2)) ∧
    (∀ word, (unpackWordRun input).1 = some word → (parseInputRun word).1 = none →
      verifyBitsRun input cert = (false, (unpackWordRun input).2 + (parseInputRun word).2 + 2)) ∧
    (∀ word source target fuel, (unpackWordRun input).1 = some word →
      (parseInputRun word).1 = some (source, target, fuel) → (unpackWordRun cert).1 = none →
      verifyBitsRun input cert =
        (false, (unpackWordRun input).2 + (parseInputRun word).2 + (unpackWordRun cert).2 + 2)) ∧
    (∀ word moves source target fuel, (unpackWordRun input).1 = some word →
      (parseInputRun word).1 = some (source, target, fuel) → (unpackWordRun cert).1 = some moves →
      verifyBitsRun input cert =
        ((checkStreamRun fuel source target moves).1,
          (unpackWordRun input).2 + (parseInputRun word).2 + (unpackWordRun cert).2 +
            (checkStreamRun fuel source target moves).2 + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact verifyBitsRun_input_none input cert
  · intro word decoded parsed
    exact verifyBitsRun_parse_none input cert word decoded parsed
  · intro word source target fuel decoded parsed failed
    exact verifyBitsRun_certificate_none input cert word source target fuel decoded parsed failed
  · intro word moves source target fuel decoded parsed certificate
    exact verifyBitsRun_success input cert word moves source target fuel decoded parsed certificate


end Examples.RotationCertificateFrontEndStreamMachine
