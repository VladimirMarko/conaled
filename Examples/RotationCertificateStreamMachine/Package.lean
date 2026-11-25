import Examples.RotationCertificateStreamMachine.Boundaries

/-!
# RotationCertificateStreamMachine: Package
-/

namespace Examples.RotationCertificateStreamMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.StreamMachine

/-! ## Actual finite packages, installed configurations and the genuine input -/

def independentPackage (caller : ExampleCaller) (initial : Bool) : Turing.FinTM2 :=
  machine caller initial

def twoLabelPackage
    (caller : External (Fin 2) → Statement IndependentAlphabet (Fin 2) Bool)
    (initial : Bool) : Turing.FinTM2 := machine caller initial

theorem the_actual_unit_label_package_has_eleven_stacks_fortytwo_labels_and_612_registers
    (caller : ExampleCaller) (initial : Bool) :
    @Fintype.card (independentPackage caller initial).K (independentPackage caller initial).kFin = 11 ∧
      @Fintype.card (independentPackage caller initial).Λ (independentPackage caller initial).ΛFin = 42 ∧
      @Fintype.card (independentPackage caller initial).σ (independentPackage caller initial).σFin = 612 := by
  change @Fintype.card (machine caller initial).K (machine caller initial).kFin = 11 ∧
    @Fintype.card (machine caller initial).Λ (machine caller initial).ΛFin = 42 ∧
    @Fintype.card (machine caller initial).σ (machine caller initial).σFin = 612
  exact ⟨by simpa using machine_card_stackId caller initial,
    by simpa using machine_card_label caller initial,
    by simpa using machine_card_registers caller initial⟩

theorem the_actual_two_label_package_has_eleven_stacks_fortythree_labels_and_612_registers
    (caller : External (Fin 2) → Statement IndependentAlphabet (Fin 2) Bool)
    (initial : Bool) :
    @Fintype.card (twoLabelPackage caller initial).K (twoLabelPackage caller initial).kFin = 11 ∧
      @Fintype.card (twoLabelPackage caller initial).Λ (twoLabelPackage caller initial).ΛFin = 43 ∧
      @Fintype.card (twoLabelPackage caller initial).σ (twoLabelPackage caller initial).σFin = 612 := by
  change @Fintype.card (machine caller initial).K (machine caller initial).kFin = 11 ∧
    @Fintype.card (machine caller initial).Λ (machine caller initial).ΛFin = 43 ∧
    @Fintype.card (machine caller initial).σ (machine caller initial).σFin = 612
  exact ⟨by simpa using machine_card_stackId caller initial,
    by simpa using machine_card_label caller initial,
    by simpa using machine_card_registers caller initial⟩

section GenericPackageConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : External Λ → Statement Γ Λ R) (initial : R)

theorem actual_package_indices_and_alphabets_are_certificate_tag_and_fuel_bool :
    (machine caller initial).k₀ = Sum.inl LocalStack.certificate ∧
      (machine caller initial).k₁ = Sum.inl LocalStack.fuel ∧
      (machine caller initial).Γ (machine caller initial).k₀ = Tag ∧
      (machine caller initial).Γ (machine caller initial).k₁ = Bool :=
  ⟨rfl, rfl, rfl, rfl⟩

abbrev actual_package_every_physical_alphabet_is_finite (k : (machine caller initial).K) :
    Fintype ((machine caller initial).Γ k) := machineAlphabetFintype caller initial k

theorem actual_package_step_is_the_same_literal_runtime (c : Cfg Γ Λ R) :
    (machine caller initial).step c = step caller c := machine_step_eq caller initial c

theorem actual_package_retains_arbitrary_installed_registers_and_dirty_words
    (start : Cfg Γ Λ R) :
    FirstRun (machine caller initial).step start (remainingSteps start) (finalCfg start) :=
  machine_cfg_first_return caller initial start

theorem actual_package_first_result_converse_uses_the_complete_installed_endpoint
    (start finish : Cfg Γ Λ R) (ticks : Nat) :
    FirstRun (machine caller initial).step start ticks finish ↔
      ticks = remainingSteps start ∧ finish = finalCfg start :=
  machineFirstRun_iff caller initial start finish ticks

def actual_package_installed_timing (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (machine caller initial).step start
      (some (finalCfg start)) (remainingSteps start) := machineCfgInTime caller initial start

theorem actual_package_installed_timing_stores_the_exact_clock (start : Cfg Γ Λ R) :
    (actual_package_installed_timing caller initial start).steps = remainingSteps start := rfl

theorem the_genuine_initializer_installs_only_the_supplied_certificate (raw : Word) :
    Turing.initList (machine caller initial) raw =
      cfg (some (phaseLabel inspectPhase)) (initialRegisters initial)
        {certificate := raw} (fun _ => []) := initList_eq caller initial raw

theorem every_genuine_certificate_input_reaches_its_live_boolean_in_four_steps (raw : Word) :
    FirstRun (machine caller initial).step (Turing.initList (machine caller initial) raw) 4
      (cfg (some (resultLabel raw.isEmpty)) (initialRegisters initial)
        {certificate := raw} (fun _ => [])) := machine_init_first_return caller initial raw

theorem the_genuine_initializer_has_exact_rank_four_and_never_emits_a_fuel_output (raw : Word) :
    remainingSteps (Turing.initList (machine caller initial) raw) = 4 ∧
      (finalCfg (Turing.initList (machine caller initial) raw)).stk (machine caller initial).k₁ = [] ∧
      (finalCfg (Turing.initList (machine caller initial) raw)).stk (.inl .certificate) = raw ∧
      (finalCfg (Turing.initList (machine caller initial) raw)).l = some (resultLabel raw.isEmpty) :=
  ⟨machine_init_exact_rank caller initial raw, machine_init_final_output_empty caller initial raw,
    machine_init_final_certificate caller initial raw, machine_init_endpoint_live caller initial raw⟩

def actual_initializer_timing (raw : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw)
      (some (cfg (some (resultLabel raw.isEmpty)) (initialRegisters initial)
        {certificate := raw} (fun _ => []))) 4 := machineInitInTimeExact caller initial raw

theorem actual_initializer_timing_stores_four (raw : Word) :
    (actual_initializer_timing caller initial raw).steps = 4 := rfl

theorem every_actual_initializer_prefix_has_exactly_the_input_cell_count
    (raw : Word) (n : Nat) (bound : n ≤ 4) (reached : Cfg Γ Λ R)
    (executed : Runs (machine caller initial).step
      (Turing.initList (machine caller initial) raw) n reached) :
    physicalCells reached = raw.length :=
  machine_init_prefix_cells caller initial raw n bound reached executed

theorem every_genuine_initializer_has_the_exact_inclusive_input_peak (raw : Word) :
    ExactPeak (machine caller initial).step
      (Turing.initList (machine caller initial) raw) 4 raw.length :=
  machine_init_exact_peak caller initial raw

end GenericPackageConnections

theorem both_literal_genuine_inputs_use_the_actual_package_initializer
    (caller : ExampleCaller) (initial : Bool) :
    FirstRun (independentPackage caller initial).step
      (Turing.initList (independentPackage caller initial) ([] : Word)) 4
      (cfg (some (resultLabel true)) (clean initial) {} (fun _ => [])) ∧
    FirstRun (independentPackage caller initial).step
      (Turing.initList (independentPackage caller initial) ([15] : Word)) 4
      (cfg (some (resultLabel false)) (clean initial) {certificate := [15]} (fun _ => [])) :=
  ⟨machine_init_first_return caller initial [], machine_init_first_return caller initial [15]⟩

theorem the_same_actual_package_runs_the_installed_rotation_input_for_twentyfive_steps
    (caller : ExampleCaller) (initial flag : Bool) :
    FirstRun (independentPackage caller initial).step (a12.start (stale flag) ordinaryContext)
      25 (a12.finish (stale flag) ordinaryContext) :=
  a12_actual_first_run caller (stale flag) ordinaryContext

/-! ## Complete FrontEnd physical compatibility and explicit installed entries -/

theorem all_front_end_physical_indices_and_symbols_have_complete_inverses
    {K : Type} {Γ : K → Type}
    (k : FrontEndMachine.StackId (NewBranchStores ⊕ K))
    (j : StackId (FrontEndProtected ⊕ K))
    (symbol : FrontEndMachine.alphabet (frontEndAddedAlphabet Γ) k) :
    frontEndStackEquiv.symm (frontEndStackEquiv k) = k ∧
      frontEndStackEquiv (frontEndStackEquiv.symm j) = j ∧
      (frontEndSymbolEquiv (Γ := Γ) k).symm (frontEndSymbolEquiv k symbol) = symbol :=
  ⟨frontEndStackEquiv.symm_apply_apply k, frontEndStackEquiv.apply_symm_apply j,
    (frontEndSymbolEquiv k).symm_apply_apply symbol⟩

theorem the_front_end_register_map_preserves_all_decoder_and_branch_fields
    {R : Type} (regs : FrontEndMachine.Registers (Option Branch × R)) :
    frontEndRegisterEquiv.symm (frontEndRegisterEquiv regs) = regs ∧
      (frontEndRegisterEquiv regs).1 = regs.2.1.b0 ∧
      (frontEndRegisterEquiv regs).2.1.1 = regs.2.2.1 ∧
      (frontEndRegisterEquiv regs).2.2.1 =
        (regs.2.1.b1, regs.2.1.b2, regs.2.1.b3, regs.2.1.tag) ∧
      (frontEndRegisterEquiv regs).2.2.2 = regs.2.2.2 :=
  ⟨frontEndRegisterEquiv.symm_apply_apply regs, rfl, rfl, rfl, rfl⟩

theorem front_end_reset_really_retains_the_incoming_branch_register
    {R : Type} (regs : FrontEndMachine.Registers (Option Branch × R)) :
    frontEndRegisterEquiv (FrontEndMachine.reset regs) =
      (none, ((regs.2.2.1, (none, none)), (frontEndDecoderZero, regs.2.2.2))) :=
  frontEndRegisterEquiv_reset regs

theorem complete_front_end_physical_cardinalities
    {K R : Type} [Fintype K] [Fintype R] :
    Fintype.card (FrontEndMachine.StackId (NewBranchStores ⊕ K)) = 16 + Fintype.card K ∧
      Fintype.card (StackId (FrontEndProtected ⊕ K)) = 16 + Fintype.card K ∧
      Fintype.card FrontEndDecoderComplement = 459 ∧
      Fintype.card (FrontEndMachine.Registers (Option Branch × R)) = 140454 * Fintype.card R ∧
      Fintype.card (Registers (FrontEndDecoderComplement × R)) = 140454 * Fintype.card R :=
  ⟨frontEnd_source_stack_card, frontEnd_stack_card, frontEnd_decoder_complement_card,
    frontEnd_source_register_card, frontEnd_register_card⟩

theorem the_front_end_map_preserves_the_sum_over_every_physical_stack
    {K : Type} {Γ : K → Type} [Fintype K]
    (allWords : ∀ k, List (FrontEndMachine.alphabet (frontEndAddedAlphabet Γ) k)) :
    ∑ k, (frontEndStacks allWords k).length = ∑ k, (allWords k).length :=
  frontEnd_stack_cells allWords

def frontEndInstalledEntry {K Λ R : Type} {Γ : K → Type}
    (regs : FrontEndMachine.Registers (Option Branch × R))
    (B O : List Branch) (ctx : ∀ k, List (Γ k))
    (source target : BinaryTree Unit) (fuel : Bits) (certificate : Word) :
    Cfg (frontEndProtectedAlphabet Γ) Λ (FrontEndDecoderComplement × R) :=
  cfg (some (phaseLabel inspectPhase)) (frontEndRegisterEquiv (FrontEndMachine.reset regs))
    (frontEndSuccessData source target fuel certificate B O) (frontEndSuccessContext ctx)

theorem the_actual_front_end_success_matches_the_installed_physical_data
    {K Λ R : Type} {Γ : K → Type}
    (regs : FrontEndMachine.Registers (Option Branch × R))
    (B O : List Branch) (ctx : ∀ k, List (Γ k))
    (source target : BinaryTree Unit) (fuel : Bits) (certificate : Word) :
    frontEndPhysicalData (FrontEndMachine.resultCfg (Λ := Λ) regs
      (frontEndAddedContext B O ctx) (.success source target fuel certificate)) =
      ((frontEndInstalledEntry (Λ := Λ) regs B O ctx source target fuel certificate).var,
        (frontEndInstalledEntry (Λ := Λ) regs B O ctx source target fuel certificate).stk) :=
  frontEnd_success_physical_data regs B O ctx source target fuel certificate

def staleFrontEndRegisters (flag : Bool) : FrontEndMachine.Registers (Option Branch × Bool) :=
  ((some 15, some ()),
    (⟨some true, some false, some true, some false, some 7⟩, (some .right, flag)))

def frontEndDirtyEntry (flag : Bool) :
    Cfg (frontEndProtectedAlphabet IndependentAlphabet) Unit (FrontEndDecoderComplement × Bool) :=
  frontEndInstalledEntry (staleFrontEndRegisters flag) [.right] [.left] ordinaryContext
    rightTwo leftTwo [true] [6, 10]

theorem front_end_dirty_entry_retains_both_physical_branch_words_and_stale_branch
    (flag : Bool) :
    frontEndDirtyEntry flag = r10.start
      (none, ((some .right, (none, none)), (frontEndDecoderZero, flag)))
      (frontEndSuccessContext ordinaryContext) := rfl

theorem the_actual_dirty_front_end_data_has_the_fixed_twenty_step_false_result
    (caller : External Unit → Statement (frontEndProtectedAlphabet IndependentAlphabet)
      Unit (FrontEndDecoderComplement × Bool)) (flag : Bool) :
    FirstRun (step caller) (frontEndDirtyEntry flag) 20
      (cfg (some (resultLabel false))
        (none, ((none, (none, none)), (frontEndDecoderZero, flag)))
        (data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0])
        (frontEndSuccessContext ordinaryContext)) ∧
    ExactPeak (step caller) (frontEndDirtyEntry flag) 20 20 := by
  have first := r10_actual_first_run caller
    (none, ((some .right, (none, none)), (frontEndDecoderZero, flag)))
    (frontEndSuccessContext ordinaryContext)
  have peak := r10_actual_exact_peak caller
    (none, ((some .right, (none, none)), (frontEndDecoderZero, flag)))
    (frontEndSuccessContext ordinaryContext)
  have external : externalCells (frontEndSuccessContext ordinaryContext) = 5 := by
    exact (frontEnd_success_context_cells ordinaryContext).trans
      ordinary_protected_context_has_five_physical_cells
  refine ⟨first, ?_⟩
  rw [front_end_dirty_entry_retains_both_physical_branch_words_and_stale_branch]
  have exactPeak : r10.peak + externalCells (frontEndSuccessContext ordinaryContext) = 20 := by
    rw [external]
    rfl
  rw [exactPeak] at peak
  exact peak

theorem the_dirty_front_end_selected_boundaries_use_the_same_actual_registers
    (caller : External Unit → Statement (frontEndProtectedAlphabet IndependentAlphabet)
      Unit (FrontEndDecoderComplement × Bool)) (flag : Bool) :
    ∀ b ∈ frontEndDirtyBoundaries,
      b.Expected (step caller) (frontEndDirtyEntry flag)
        (none, ((some .right, (none, none)), (frontEndDecoderZero, flag)))
        (frontEndSuccessContext ordinaryContext) :=
  all_five_dirty_branch_boundaries_have_their_actual_rank_and_cells caller
    (none, ((some .right, (none, none)), (frontEndDecoderZero, flag)))
    (frontEndSuccessContext ordinaryContext)

theorem explicitly_empty_added_branch_words_give_the_clean_front_end_example
    (caller : External Unit → Statement (frontEndProtectedAlphabet IndependentAlphabet)
      Unit (FrontEndDecoderComplement × Bool)) (flag : Bool) :
    FirstRun (step caller)
      (frontEndInstalledEntry (staleFrontEndRegisters flag) [] [] ordinaryContext
        rightTwo leftTwo [true] [6, 10]) 25
      (cfg (some (resultLabel true))
        (none, ((none, (none, none)), (frontEndDecoderZero, flag)))
        (data [] [] [] [] [] [] [] [false] []) (frontEndSuccessContext ordinaryContext)) :=
  a12_actual_first_run caller
    (frontEndRegisterEquiv (FrontEndMachine.reset (staleFrontEndRegisters flag)))
    (frontEndSuccessContext ordinaryContext)

/-! ## Further installation through complete carriers and owned body agreement -/

section FurtherCompleteInstallation
variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')

theorem further_installation_has_a_complete_configuration_inverse
    (source : Cfg Γ Λ R) (target : Turing.TM2.Cfg Γ' Λ' R') :
    (installedCfgEquiv names symbols registers labels).symm
        (installedCfg names symbols registers labels source) = source ∧
    installedCfg names symbols registers labels
        ((installedCfgEquiv names symbols registers labels).symm target) = target :=
  ⟨(installedCfgEquiv names symbols registers labels).symm_apply_apply source,
    (installedCfgEquiv names symbols registers labels).apply_symm_apply target⟩

theorem further_installation_recovers_every_register_and_physical_word
    (source : Cfg Γ Λ R) :
    registers.symm (installedCfg names symbols registers labels source).var = source.var ∧
    ∀ k, ((installedCfg names symbols registers labels source).stk (names k)).map
      (symbols k).symm = source.stk k :=
  ⟨installedCfg_registers_readback names symbols registers labels source,
    installedCfg_stack_readback names symbols registers labels source⟩

theorem further_installation_preserves_the_complete_physical_sum
    [Fintype K] [Fintype K'] (source : Cfg Γ Λ R) :
    ∑ k, ((installedCfg names symbols registers labels source).stk k).length =
      physicalCells source := installed_stack_cells names symbols registers labels source

variable [DecidableEq K] [DecidableEq K']
variable (caller : External Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')

theorem all_thirtynine_owned_bodies_suffice_for_each_actual_local_prefix
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) :=
  installed_owned_prefix names symbols registers labels caller ambient installed start n bound

theorem further_installation_fixes_the_first_time_and_the_entire_first_endpoint
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (finish : Turing.TM2.Cfg Γ' Λ' R') :
    ((FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) = some finish ∧
      ¬ Owned (finish.l.map labels.symm) ∧
      ∀ j, j < n → ∃ reached,
        (FrontEndMachine.Transport.next ambient)^[j]
          (some (installedCfg names symbols registers labels start)) = some reached ∧
        Owned (reached.l.map labels.symm)) ↔
    n = remainingSteps start ∧
      finish = installedCfg names symbols registers labels (finalCfg start) :=
  installed_firstRun_iff names symbols registers labels caller ambient installed start n finish

def exact_owned_installation_timing
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start)
      (some (installedCfg names symbols registers labels (finalCfg start)))
      (remainingSteps start) :=
  installed_owned_timed names symbols registers labels caller ambient installed start

theorem exact_owned_installation_timing_stores_the_actual_clock
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) :
    (exact_owned_installation_timing names symbols registers labels caller ambient installed start).steps =
      remainingSteps start := rfl

theorem an_actual_installed_prefix_keeps_its_source_physical_bound
    [Fintype K] [Fintype K']
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) (budget : Nat)
    (estimate : ∀ source, Runs (step caller) start n source → physicalCells source ≤ budget)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = some reached) :
    ∑ k, (reached.stk k).length ≤ budget :=
  installed_prefix_cells_of_source_bound names symbols registers labels caller ambient installed
    start n bound budget estimate reached executed

theorem agreement_at_every_label_transports_arbitrary_later_caller_iterations
    (installed : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (n : Nat) (start : Option (Cfg Γ Λ R)) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (start.map (installedCfg names symbols registers labels)) =
      ((next caller)^[n] start).map (installedCfg names symbols registers labels) :=
  installed_iterate names symbols registers labels caller ambient installed n start

end FurtherCompleteInstallation



end Examples.RotationCertificateStreamMachine
