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

theorem cleanupC00_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC00.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 0 cleanupC00.before (cleanupC00.fields.withUser value) ctx

theorem cleanupC00E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC00E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 0 cleanupC00E.before (cleanupC00E.fields.withUser value) ctx

theorem cleanupC01_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC01.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 1 cleanupC01.before (cleanupC01.fields.withUser value) ctx

theorem cleanupC01E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC01E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 1 cleanupC01E.before (cleanupC01E.fields.withUser value) ctx

theorem cleanupC02_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC02.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 2 cleanupC02.before (cleanupC02.fields.withUser value) ctx

theorem cleanupC02E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC02E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 2 cleanupC02E.before (cleanupC02E.fields.withUser value) ctx

theorem cleanupC03_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC03.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 3 cleanupC03.before (cleanupC03.fields.withUser value) ctx

theorem cleanupC03E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC03E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 3 cleanupC03E.before (cleanupC03E.fields.withUser value) ctx

theorem cleanupC04_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC04.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 4 cleanupC04.before (cleanupC04.fields.withUser value) ctx

theorem cleanupC04E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC04E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 4 cleanupC04E.before (cleanupC04E.fields.withUser value) ctx

theorem cleanupC05_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC05.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 5 cleanupC05.before (cleanupC05.fields.withUser value) ctx

theorem cleanupC05E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC05E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 5 cleanupC05E.before (cleanupC05E.fields.withUser value) ctx

theorem cleanupC06_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC06.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 6 cleanupC06.before (cleanupC06.fields.withUser value) ctx

theorem cleanupC06E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC06E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 6 cleanupC06E.before (cleanupC06E.fields.withUser value) ctx

theorem cleanupC07_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC07.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 7 cleanupC07.before (cleanupC07.fields.withUser value) ctx

theorem cleanupC07E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC07E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 7 cleanupC07E.before (cleanupC07E.fields.withUser value) ctx

theorem cleanupC08_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC08.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 8 cleanupC08.before (cleanupC08.fields.withUser value) ctx

theorem cleanupC08E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC08E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 8 cleanupC08E.before (cleanupC08E.fields.withUser value) ctx

theorem cleanupC09_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC09.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 9 cleanupC09.before (cleanupC09.fields.withUser value) ctx

theorem cleanupC09E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC09E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 9 cleanupC09E.before (cleanupC09E.fields.withUser value) ctx

theorem cleanupC10_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC10.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 10 cleanupC10.before (cleanupC10.fields.withUser value) ctx

theorem cleanupC10E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC10E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 10 cleanupC10E.before (cleanupC10E.fields.withUser value) ctx

theorem cleanupC11_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC11.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 11 cleanupC11.before (cleanupC11.fields.withUser value) ctx

theorem cleanupC11E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC11E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 11 cleanupC11E.before (cleanupC11E.fields.withUser value) ctx

theorem cleanupC12_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC12.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 12 cleanupC12.before (cleanupC12.fields.withUser value) ctx

theorem cleanupC12E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC12E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 12 cleanupC12E.before (cleanupC12E.fields.withUser value) ctx

theorem cleanupC13_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC13.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 13 cleanupC13.before (cleanupC13.fields.withUser value) ctx

theorem cleanupC13E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC13E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 13 cleanupC13E.before (cleanupC13E.fields.withUser value) ctx

theorem cleanupC14_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC14.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 14 cleanupC14.before (cleanupC14.fields.withUser value) ctx

theorem cleanupC14E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC14E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 14 cleanupC14E.before (cleanupC14E.fields.withUser value) ctx

theorem cleanupC15_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC15.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 15 cleanupC15.before (cleanupC15.fields.withUser value) ctx

theorem cleanupC15E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC15E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 15 cleanupC15E.before (cleanupC15E.fields.withUser value) ctx

theorem emitE00_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    emitE00.toClosedFixture.RunExpected (step caller) value ctx :=
  direct_emit_preserves_other_words_and_pushes_old_fuel caller emitE00.before (emitE00.fields.withUser value) ctx

theorem emitE01_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    emitE01.toClosedFixture.RunExpected (step caller) value ctx :=
  direct_emit_preserves_other_words_and_pushes_old_fuel caller emitE01.before (emitE01.fields.withUser value) ctx

theorem emitE02_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    emitE02.toClosedFixture.RunExpected (step caller) value ctx :=
  direct_emit_preserves_other_words_and_pushes_old_fuel caller emitE02.before (emitE02.fields.withUser value) ctx

theorem emitE03_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    emitE03.toClosedFixture.RunExpected (step caller) value ctx :=
  direct_emit_preserves_other_words_and_pushes_old_fuel caller emitE03.before (emitE03.fields.withUser value) ctx

theorem joinJ00_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    joinJ00.toClosedFixture.RunExpected (step caller) value ctx :=
  rejecting_join_has_its_whole_halt_after_the_paid_activation caller joinJ00.before (joinJ00.fields.withUser value) ctx

theorem joinJ01_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    joinJ01.toClosedFixture.RunExpected (step caller) value ctx :=
  boolean_join_has_its_whole_halt_after_the_paid_activation caller false joinJ01.before (joinJ01.fields.withUser value) ctx

theorem joinJ02_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    joinJ02.toClosedFixture.RunExpected (step caller) value ctx :=
  boolean_join_has_its_whole_halt_after_the_paid_activation caller true joinJ02.before (joinJ02.fields.withUser value) ctx

theorem emptyCleanupFixture_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    emptyCleanupFixture.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 0 emptyCleanupFixture.before (emptyCleanupFixture.fields.withUser value) ctx

theorem all_partial_clear_cases_execute (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ fixture ∈ partialClearCases, fixture.toClosedFixture.RunExpected (step caller) value ctx := by
  intro fixture member
  simp only [partialClearCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cleanupC00_actual_first_halt caller value ctx
  · exact cleanupC00E_actual_first_halt caller value ctx
  · exact cleanupC01_actual_first_halt caller value ctx
  · exact cleanupC01E_actual_first_halt caller value ctx
  · exact cleanupC02_actual_first_halt caller value ctx
  · exact cleanupC02E_actual_first_halt caller value ctx
  · exact cleanupC03_actual_first_halt caller value ctx
  · exact cleanupC03E_actual_first_halt caller value ctx
  · exact cleanupC04_actual_first_halt caller value ctx
  · exact cleanupC04E_actual_first_halt caller value ctx
  · exact cleanupC05_actual_first_halt caller value ctx
  · exact cleanupC05E_actual_first_halt caller value ctx
  · exact cleanupC06_actual_first_halt caller value ctx
  · exact cleanupC06E_actual_first_halt caller value ctx
  · exact cleanupC07_actual_first_halt caller value ctx
  · exact cleanupC07E_actual_first_halt caller value ctx
  · exact cleanupC08_actual_first_halt caller value ctx
  · exact cleanupC08E_actual_first_halt caller value ctx
  · exact cleanupC09_actual_first_halt caller value ctx
  · exact cleanupC09E_actual_first_halt caller value ctx
  · exact cleanupC10_actual_first_halt caller value ctx
  · exact cleanupC10E_actual_first_halt caller value ctx
  · exact cleanupC11_actual_first_halt caller value ctx
  · exact cleanupC11E_actual_first_halt caller value ctx
  · exact cleanupC12_actual_first_halt caller value ctx
  · exact cleanupC12E_actual_first_halt caller value ctx
  · exact cleanupC13_actual_first_halt caller value ctx
  · exact cleanupC13E_actual_first_halt caller value ctx
  · exact cleanupC14_actual_first_halt caller value ctx
  · exact cleanupC14E_actual_first_halt caller value ctx
  · exact cleanupC15_actual_first_halt caller value ctx
  · exact cleanupC15E_actual_first_halt caller value ctx

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

def sourceF01 : SourceObservation :=
  ⟨emptyRawFixture, ⟨2, none, none, none, none, none, none, 2⟩⟩

theorem sourceF01_has_its_original_component_tariffs : sourceF01.Expected := by
  constructor <;> rfl

def sourceF02 : SourceObservation :=
  ⟨truncatedPrefixFixture, ⟨2, none, none, none, none, none, none, 2⟩⟩

theorem sourceF02_has_its_original_component_tariffs : sourceF02.Expected := by
  constructor <;> rfl

def sourceF03 : SourceObservation :=
  ⟨rawF03, ⟨4, none, none, none, none, none, none, 4⟩⟩

theorem sourceF03_has_its_original_component_tariffs : sourceF03.Expected := by
  constructor <;> rfl

def sourceF04 : SourceObservation :=
  ⟨rawF04, ⟨4, none, none, none, none, none, none, 4⟩⟩

theorem sourceF04_has_its_original_component_tariffs : sourceF04.Expected := by
  constructor <;> rfl

def sourceF05 : SourceObservation :=
  ⟨rawF05, ⟨4, some 2, some 5, none, some 2, some 4, none, 11⟩⟩

theorem sourceF05_has_its_original_component_tariffs : sourceF05.Expected := by
  constructor <;> rfl

def sourceF06 : SourceObservation :=
  ⟨rawF06, ⟨6, some 2, some 5, none, some 2, some 4, none, 13⟩⟩

theorem sourceF06_has_its_original_component_tariffs : sourceF06.Expected := by
  constructor <;> rfl

def sourceF07 : SourceObservation :=
  ⟨rawF07, ⟨6, some 2, none, none, some 2, none, none, 8⟩⟩

theorem sourceF07_has_its_original_component_tariffs : sourceF07.Expected := by
  constructor <;> rfl

def sourceF08 : SourceObservation :=
  ⟨rawF08, ⟨12, some 2, none, none, some 2, none, none, 14⟩⟩

theorem sourceF08_has_its_original_component_tariffs : sourceF08.Expected := by
  constructor <;> rfl

def sourceI01 : SourceObservation :=
  ⟨rawI01, ⟨12, some 4, some 9, none, some 6, some 7, none, 25⟩⟩

theorem sourceI01_has_its_original_component_tariffs : sourceI01.Expected := by
  constructor <;> rfl

def sourceI02 : SourceObservation :=
  ⟨rawI02, ⟨14, some 4, some 5, none, some 6, some 4, none, 23⟩⟩

theorem sourceI02_has_its_original_component_tariffs : sourceI02.Expected := by
  constructor <;> rfl

def sourceI03 : SourceObservation :=
  ⟨rawI03, ⟨36, some 10, some 9, none, some 18, some 7, none, 55⟩⟩

theorem sourceI03_has_its_original_component_tariffs : sourceI03.Expected := by
  constructor <;> rfl

def sourceI04 : SourceObservation :=
  ⟨rawI04, ⟨52, some 14, some 26, none, some 26, some 15, none, 92⟩⟩

theorem sourceI04_has_its_original_component_tariffs : sourceI04.Expected := by
  constructor <;> rfl

def sourceI05 : SourceObservation :=
  ⟨rawI05, ⟨52, some 14, some 22, none, some 26, some 14, none, 88⟩⟩

theorem sourceI05_has_its_original_component_tariffs : sourceI05.Expected := by
  constructor <;> rfl

def sourceI06 : SourceObservation :=
  ⟨rawI06, ⟨116, some 26, some 12, none, some 50, some 11, none, 154⟩⟩

theorem sourceI06_has_its_original_component_tariffs : sourceI06.Expected := by
  constructor <;> rfl

def sourceI07 : SourceObservation :=
  ⟨rawI07, ⟨44, some 12, some 5, none, some 22, some 4, none, 61⟩⟩

theorem sourceI07_has_its_original_component_tariffs : sourceI07.Expected := by
  constructor <;> rfl

def sourceC01 : SourceObservation :=
  ⟨rawC01, ⟨46, some 12, some 13, some 2, some 22, some 15, some 2, 73⟩⟩

theorem sourceC01_has_its_original_component_tariffs : sourceC01.Expected := by
  constructor <;> rfl

def sourceC02 : SourceObservation :=
  ⟨rawC02, ⟨70, some 16, some 17, some 4, some 30, some 21, some 4, 107⟩⟩

theorem sourceC02_has_its_original_component_tariffs : sourceC02.Expected := by
  constructor <;> rfl

def sourceC03 : SourceObservation :=
  ⟨rawC03, ⟨134, some 30, some 31, some 6, some 58, some 46, some 6, 201⟩⟩

theorem sourceC03_has_its_original_component_tariffs : sourceC03.Expected := by
  constructor <;> rfl

def sourceV01 : SourceObservation :=
  ⟨rawV01, ⟨44, some 12, some 13, some 2, some 22, some 15, some 2, 71⟩⟩

theorem sourceV01_has_its_original_component_tariffs : sourceV01.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [] (.nil : BinaryTree Unit)
      (.nil : BinaryTree Unit) []).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV02 : SourceObservation :=
  ⟨rawV02, ⟨60, some 16, some 17, some 2, some 30, some 22, some 2, 95⟩⟩

theorem sourceV02_has_its_original_component_tariffs : sourceV02.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [] (.nil : BinaryTree Unit)
      (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) []).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV03 : SourceObservation :=
  ⟨rawV03, ⟨132, some 30, some 31, some 6, some 58, some 46, some 10, 199⟩⟩

theorem sourceV03_has_its_original_component_tariffs : sourceV03.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 10]).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV04 : SourceObservation :=
  ⟨rawV04, ⟨132, some 30, some 31, some 6, some 58, some 46, some 10, 199⟩⟩

theorem sourceV04_has_its_original_component_tariffs : sourceV04.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [7, 10]).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV05 : SourceObservation :=
  ⟨rawV05, ⟨156, some 32, some 33, some 10, some 62, some 49, some 18, 231⟩⟩

theorem sourceV05_has_its_original_component_tariffs : sourceV05.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [false, true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [6, 10, 7, 10]).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV06 : SourceObservation :=
  ⟨rawV06, ⟨148, some 30, some 31, some 10, some 58, some 46, some 18, 219⟩⟩

theorem sourceV06_has_its_original_component_tariffs : sourceV06.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [6, 10, 7, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV07 : SourceObservation :=
  ⟨rawV07, ⟨140, some 32, some 33, some 6, some 62, some 49, some 10, 211⟩⟩

theorem sourceV07_has_its_original_component_tariffs : sourceV07.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [false, false] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [6, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV08 : SourceObservation :=
  ⟨rawV08, ⟨148, some 34, some 35, some 6, some 66, some 52, some 10, 223⟩⟩

theorem sourceV08_has_its_original_component_tariffs : sourceV08.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true, false, false] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 10]).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV09 : SourceObservation :=
  ⟨rawV09, ⟨124, some 30, some 31, some 4, some 58, some 46, some 6, 189⟩⟩

theorem sourceV09_has_its_original_component_tariffs : sourceV09.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV10 : SourceObservation :=
  ⟨rawV10, ⟨140, some 30, some 31, some 8, some 58, some 46, some 14, 209⟩⟩

theorem sourceV10_has_its_original_component_tariffs : sourceV10.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 15, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV11 : SourceObservation :=
  ⟨rawV11, ⟨140, some 30, some 31, some 8, some 58, some 46, some 14, 209⟩⟩

theorem sourceV11_has_its_original_component_tariffs : sourceV11.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 8, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV12 : SourceObservation :=
  ⟨rawV12, ⟨132, some 30, some 31, some 6, some 58, some 46, some 10, 199⟩⟩

theorem sourceV12_has_its_original_component_tariffs : sourceV12.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [7, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV13 : SourceObservation :=
  ⟨rawV13, ⟨172, some 38, some 39, some 8, some 74, some 60, some 14, 257⟩⟩

theorem sourceV13_has_its_original_component_tariffs : sourceV13.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))))
      (.node () (.nil : BinaryTree Unit) (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit))) [6, 9, 10]).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV14 : SourceObservation :=
  ⟨rawV14, ⟨140, some 30, some 31, some 8, some 58, some 46, some 14, 209⟩⟩

theorem sourceV14_has_its_original_component_tariffs : sourceV14.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 10, 15]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV15 : SourceObservation :=
  ⟨rawV15, ⟨60, some 16, some 17, some 2, some 30, some 21, some 2, 95⟩⟩

theorem sourceV15_has_its_original_component_tariffs : sourceV15.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [false, false] (.nil : BinaryTree Unit)
      (.nil : BinaryTree Unit) []).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV16 : SourceObservation :=
  ⟨rawV16, ⟨124, some 30, some 31, some 4, some 58, some 46, some 6, 189⟩⟩

theorem sourceV16_has_its_original_component_tariffs : sourceV16.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [15]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV17 : SourceObservation :=
  ⟨rawV17, ⟨68, some 14, some 15, some 6, some 26, some 18, some 10, 103⟩⟩

theorem sourceV17_has_its_original_component_tariffs : sourceV17.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.nil : BinaryTree Unit)
      (.nil : BinaryTree Unit) [6, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def sourceV18 : SourceObservation :=
  ⟨rawV18, ⟨124, some 28, some 29, some 6, some 54, some 43, some 10, 187⟩⟩

theorem sourceV18_has_its_original_component_tariffs : sourceV18.Expected := by
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
  [sourceF01, sourceF02, sourceF03, sourceF04, sourceF05, sourceF06, sourceF07, sourceF08, sourceI01, sourceI02, sourceI03, sourceI04, sourceI05, sourceI06, sourceI07, sourceC01, sourceC02, sourceC03, sourceV01, sourceV02, sourceV03, sourceV04, sourceV05, sourceV06, sourceV07, sourceV08, sourceV09, sourceV10, sourceV11, sourceV12, sourceV13, sourceV14, sourceV15, sourceV16, sourceV17, sourceV18]

theorem original_source_observations_count : originalSourceObservations.length = 36 := rfl

theorem original_source_observations_keep_their_own_tariffs :
    ∀ observation ∈ originalSourceObservations, observation.Expected := by
  intro observation member
  simp only [originalSourceObservations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sourceF01_has_its_original_component_tariffs
  · exact sourceF02_has_its_original_component_tariffs
  · exact sourceF03_has_its_original_component_tariffs
  · exact sourceF04_has_its_original_component_tariffs
  · exact sourceF05_has_its_original_component_tariffs
  · exact sourceF06_has_its_original_component_tariffs
  · exact sourceF07_has_its_original_component_tariffs
  · exact sourceF08_has_its_original_component_tariffs
  · exact sourceI01_has_its_original_component_tariffs
  · exact sourceI02_has_its_original_component_tariffs
  · exact sourceI03_has_its_original_component_tariffs
  · exact sourceI04_has_its_original_component_tariffs
  · exact sourceI05_has_its_original_component_tariffs
  · exact sourceI06_has_its_original_component_tariffs
  · exact sourceI07_has_its_original_component_tariffs
  · exact sourceC01_has_its_original_component_tariffs
  · exact sourceC02_has_its_original_component_tariffs
  · exact sourceC03_has_its_original_component_tariffs
  · exact sourceV01_has_its_original_component_tariffs
  · exact sourceV02_has_its_original_component_tariffs
  · exact sourceV03_has_its_original_component_tariffs
  · exact sourceV04_has_its_original_component_tariffs
  · exact sourceV05_has_its_original_component_tariffs
  · exact sourceV06_has_its_original_component_tariffs
  · exact sourceV07_has_its_original_component_tariffs
  · exact sourceV08_has_its_original_component_tariffs
  · exact sourceV09_has_its_original_component_tariffs
  · exact sourceV10_has_its_original_component_tariffs
  · exact sourceV11_has_its_original_component_tariffs
  · exact sourceV12_has_its_original_component_tariffs
  · exact sourceV13_has_its_original_component_tariffs
  · exact sourceV14_has_its_original_component_tariffs
  · exact sourceV15_has_its_original_component_tariffs
  · exact sourceV16_has_its_original_component_tariffs
  · exact sourceV17_has_its_original_component_tariffs
  · exact sourceV18_has_its_original_component_tariffs

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
