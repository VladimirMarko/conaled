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

theorem independentPackage_card
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

theorem twoLabelPackage_card
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

theorem machine_io_indices_alphabets :
    (machine caller initial).k₀ = Sum.inl LocalStack.certificate ∧
      (machine caller initial).k₁ = Sum.inl LocalStack.fuel ∧
      (machine caller initial).Γ (machine caller initial).k₀ = Tag ∧
      (machine caller initial).Γ (machine caller initial).k₁ = Bool :=
  ⟨rfl, rfl, rfl, rfl⟩

abbrev packageAlphabetFintype (k : (machine caller initial).K) :
    Fintype ((machine caller initial).Γ k) := machineAlphabetFintype caller initial k

theorem machine_step (c : Cfg Γ Λ R) :
    (machine caller initial).step c = step caller c := machine_step_eq caller initial c

theorem machine_firstRun
    (start : Cfg Γ Λ R) :
    FirstRun (machine caller initial).step start (remainingSteps start) (finalCfg start) :=
  machine_cfg_first_return caller initial start

theorem machine_firstRun_iff
    (start finish : Cfg Γ Λ R) (ticks : Nat) :
    FirstRun (machine caller initial).step start ticks finish ↔
      ticks = remainingSteps start ∧ finish = finalCfg start :=
  machineFirstRun_iff caller initial start finish ticks

def packageCfgInTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (machine caller initial).step start
      (some (finalCfg start)) (remainingSteps start) := machineCfgInTime caller initial start

theorem packageCfgInTime_steps (start : Cfg Γ Λ R) :
    (packageCfgInTime caller initial start).steps = remainingSteps start := rfl

theorem machine_initList_eq (raw : Word) :
    Turing.initList (machine caller initial) raw =
      cfg (some (phaseLabel inspectPhase)) (initialRegisters initial)
        {certificate := raw} (fun _ => []) := initList_eq caller initial raw

theorem machine_initList_firstRun (raw : Word) :
    FirstRun (machine caller initial).step (Turing.initList (machine caller initial) raw) 4
      (cfg (some (resultLabel raw.isEmpty)) (initialRegisters initial)
        {certificate := raw} (fun _ => [])) := machine_init_first_return caller initial raw

theorem machine_initList_invariants (raw : Word) :
    remainingSteps (Turing.initList (machine caller initial) raw) = 4 ∧
      (finalCfg (Turing.initList (machine caller initial) raw)).stk (machine caller initial).k₁ = [] ∧
      (finalCfg (Turing.initList (machine caller initial) raw)).stk (.inl .certificate) = raw ∧
      (finalCfg (Turing.initList (machine caller initial) raw)).l = some (resultLabel raw.isEmpty) :=
  ⟨machine_init_exact_rank caller initial raw, machine_init_final_output_empty caller initial raw,
    machine_init_final_certificate caller initial raw, machine_init_endpoint_live caller initial raw⟩

def packageInitInTime (raw : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw)
      (some (cfg (some (resultLabel raw.isEmpty)) (initialRegisters initial)
        {certificate := raw} (fun _ => []))) 4 := machineInitInTimeExact caller initial raw

theorem packageInitInTime_steps (raw : Word) :
    (packageInitInTime caller initial raw).steps = 4 := rfl

theorem machine_initList_prefix_physicalCells
    (raw : Word) (n : Nat) (bound : n ≤ 4) (reached : Cfg Γ Λ R)
    (executed : Runs (machine caller initial).step
      (Turing.initList (machine caller initial) raw) n reached) :
    physicalCells reached = raw.length :=
  machine_init_prefix_cells caller initial raw n bound reached executed

theorem machine_initList_exactPeak (raw : Word) :
    ExactPeak (machine caller initial).step
      (Turing.initList (machine caller initial) raw) 4 raw.length :=
  machine_init_exact_peak caller initial raw

end GenericPackageConnections

theorem independentPackage_literal_inputs_firstRun
    (caller : ExampleCaller) (initial : Bool) :
    FirstRun (independentPackage caller initial).step
      (Turing.initList (independentPackage caller initial) ([] : Word)) 4
      (cfg (some (resultLabel true)) (clean initial) {} (fun _ => [])) ∧
    FirstRun (independentPackage caller initial).step
      (Turing.initList (independentPackage caller initial) ([15] : Word)) 4
      (cfg (some (resultLabel false)) (clean initial) {certificate := [15]} (fun _ => [])) :=
  ⟨machine_init_first_return caller initial [], machine_init_first_return caller initial [15]⟩

theorem independentPackage_rotation_firstRun
    (caller : ExampleCaller) (initial flag : Bool) :
    FirstRun (independentPackage caller initial).step (a12.start (stale flag) ordinaryContext)
      25 (a12.finish (stale flag) ordinaryContext) :=
  a12_actual_first_run caller (stale flag) ordinaryContext

/-! ## Complete FrontEnd physical compatibility and explicit installed entries -/

theorem frontEndStackEquiv_frontEndSymbolEquiv_roundtrip
    {K : Type} {Γ : K → Type}
    (k : FrontEndMachine.StackId (NewBranchStores ⊕ K))
    (j : StackId (FrontEndProtected ⊕ K))
    (symbol : FrontEndMachine.Alphabet (FrontEndAddedAlphabet Γ) k) :
    frontEndStackEquiv.symm (frontEndStackEquiv k) = k ∧
      frontEndStackEquiv (frontEndStackEquiv.symm j) = j ∧
      (frontEndSymbolEquiv (Γ := Γ) k).symm (frontEndSymbolEquiv k symbol) = symbol :=
  ⟨frontEndStackEquiv.symm_apply_apply k, frontEndStackEquiv.apply_symm_apply j,
    (frontEndSymbolEquiv k).symm_apply_apply symbol⟩

theorem frontEndRegisterEquiv_fields
    {R : Type} (regs : FrontEndMachine.Registers (Option Branch × R)) :
    frontEndRegisterEquiv.symm (frontEndRegisterEquiv regs) = regs ∧
      (frontEndRegisterEquiv regs).1 = regs.2.1.b0 ∧
      (frontEndRegisterEquiv regs).2.1.1 = regs.2.2.1 ∧
      (frontEndRegisterEquiv regs).2.2.1 =
        (regs.2.1.b1, regs.2.1.b2, regs.2.1.b3, regs.2.1.tag) ∧
      (frontEndRegisterEquiv regs).2.2.2 = regs.2.2.2 :=
  ⟨frontEndRegisterEquiv.symm_apply_apply regs, rfl, rfl, rfl, rfl⟩

theorem frontEndRegisterEquiv_reset_fields
    {R : Type} (regs : FrontEndMachine.Registers (Option Branch × R)) :
    frontEndRegisterEquiv (FrontEndMachine.reset regs) =
      (none, ((regs.2.2.1, (none, none)), (frontEndDecoderZero, regs.2.2.2))) :=
  frontEndRegisterEquiv_reset regs

theorem front_end_card
    {K R : Type} [Fintype K] [Fintype R] :
    Fintype.card (FrontEndMachine.StackId (NewBranchStores ⊕ K)) = 16 + Fintype.card K ∧
      Fintype.card (StackId (FrontEndProtected ⊕ K)) = 16 + Fintype.card K ∧
      Fintype.card FrontEndDecoderComplement = 459 ∧
      Fintype.card (FrontEndMachine.Registers (Option Branch × R)) = 140454 * Fintype.card R ∧
      Fintype.card (Registers (FrontEndDecoderComplement × R)) = 140454 * Fintype.card R :=
  ⟨front_end_source_stack_card, front_end_stack_card, front_end_decoder_complement_card,
    front_end_source_register_card, front_end_register_card⟩

theorem frontEndStacks_total_length
    {K : Type} {Γ : K → Type} [Fintype K]
    (allWords : ∀ k, List (FrontEndMachine.Alphabet (FrontEndAddedAlphabet Γ) k)) :
    ∑ k, (frontEndStacks allWords k).length = ∑ k, (allWords k).length :=
  front_end_stack_cells allWords

def frontEndInstalledEntry {K Λ R : Type} {Γ : K → Type}
    (regs : FrontEndMachine.Registers (Option Branch × R))
    (B O : List Branch) (ctx : ∀ k, List (Γ k))
    (source target : BinaryTree Unit) (fuel : Bits) (certificate : Word) :
    Cfg (FrontEndProtectedAlphabet Γ) Λ (FrontEndDecoderComplement × R) :=
  cfg (some (phaseLabel inspectPhase)) (frontEndRegisterEquiv (FrontEndMachine.reset regs))
    (frontEndSuccessData source target fuel certificate B O) (frontEndSuccessContext ctx)

theorem frontEndPhysicalData_success
    {K Λ R : Type} {Γ : K → Type}
    (regs : FrontEndMachine.Registers (Option Branch × R))
    (B O : List Branch) (ctx : ∀ k, List (Γ k))
    (source target : BinaryTree Unit) (fuel : Bits) (certificate : Word) :
    frontEndPhysicalData (FrontEndMachine.resultCfg (Λ := Λ) regs
      (frontEndAddedContext B O ctx) (.success source target fuel certificate)) =
      ((frontEndInstalledEntry (Λ := Λ) regs B O ctx source target fuel certificate).var,
        (frontEndInstalledEntry (Λ := Λ) regs B O ctx source target fuel certificate).stk) :=
  front_end_success_physical_data regs B O ctx source target fuel certificate

def staleFrontEndRegisters (flag : Bool) : FrontEndMachine.Registers (Option Branch × Bool) :=
  ((some 15, some ()),
    (⟨some true, some false, some true, some false, some 7⟩, (some .right, flag)))

def frontEndDirtyEntry (flag : Bool) :
    Cfg (FrontEndProtectedAlphabet IndependentAlphabet) Unit (FrontEndDecoderComplement × Bool) :=
  frontEndInstalledEntry (staleFrontEndRegisters flag) [.right] [.left] ordinaryContext
    rightTwo leftTwo [true] [6, 10]

theorem frontEndDirtyEntry_eq
    (flag : Bool) :
    frontEndDirtyEntry flag = r10.start
      (none, ((some .right, (none, none)), (frontEndDecoderZero, flag)))
      (frontEndSuccessContext ordinaryContext) := rfl

theorem frontEndDirtyEntry_firstRun_exactPeak
    (caller : External Unit → Statement (FrontEndProtectedAlphabet IndependentAlphabet)
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
    exact (front_end_success_context_cells ordinaryContext).trans
      ordinary_protected_context_has_five_physical_cells
  refine ⟨first, ?_⟩
  rw [frontEndDirtyEntry_eq]
  have exactPeak : r10.peak + externalCells (frontEndSuccessContext ordinaryContext) = 20 := by
    rw [external]
    rfl
  rw [exactPeak] at peak
  exact peak

theorem frontEndDirtyEntry_boundaries
    (caller : External Unit → Statement (FrontEndProtectedAlphabet IndependentAlphabet)
      Unit (FrontEndDecoderComplement × Bool)) (flag : Bool) :
    ∀ b ∈ frontEndDirtyBoundaries,
      b.Expected (step caller) (frontEndDirtyEntry flag)
        (none, ((some .right, (none, none)), (frontEndDecoderZero, flag)))
        (frontEndSuccessContext ordinaryContext) :=
  all_five_dirty_branch_boundaries_have_their_actual_rank_and_cells caller
    (none, ((some .right, (none, none)), (frontEndDecoderZero, flag)))
    (frontEndSuccessContext ordinaryContext)

theorem frontEndInstalledEntry_empty_branches_firstRun
    (caller : External Unit → Statement (FrontEndProtectedAlphabet IndependentAlphabet)
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
variable (names : StackId K ≃ K') (symbols : ∀ k, Alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')

theorem installedCfgEquiv_roundtrip
    (source : Cfg Γ Λ R) (target : Turing.TM2.Cfg Γ' Λ' R') :
    (installedCfgEquiv names symbols registers labels).symm
        (installedCfg names symbols registers labels source) = source ∧
    installedCfg names symbols registers labels
        ((installedCfgEquiv names symbols registers labels).symm target) = target :=
  ⟨(installedCfgEquiv names symbols registers labels).symm_apply_apply source,
    (installedCfgEquiv names symbols registers labels).apply_symm_apply target⟩

theorem installedCfg_readback
    (source : Cfg Γ Λ R) :
    registers.symm (installedCfg names symbols registers labels source).var = source.var ∧
    ∀ k, ((installedCfg names symbols registers labels source).stk (names k)).map
      (symbols k).symm = source.stk k :=
  ⟨installedCfg_registers_readback names symbols registers labels source,
    installedCfg_stack_readback names symbols registers labels source⟩

theorem installedCfg_physicalCells
    [Fintype K] [Fintype K'] (source : Cfg Γ Λ R) :
    ∑ k, ((installedCfg names symbols registers labels source).stk k).length =
      physicalCells source := installed_stack_cells names symbols registers labels source

variable [DecidableEq K] [DecidableEq K']
variable (caller : External Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')

theorem installedCfg_owned_prefix
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) :=
  installed_owned_prefix names symbols registers labels caller ambient installed start n bound

theorem installedCfg_firstRun_iff
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
  installedFirstRun_iff names symbols registers labels caller ambient installed start n finish

def ownedInstallationInTime
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start)
      (some (installedCfg names symbols registers labels (finalCfg start)))
      (remainingSteps start) :=
  installedOwnedTimed names symbols registers labels caller ambient installed start

theorem ownedInstallationInTime_steps
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) :
    (ownedInstallationInTime names symbols registers labels caller ambient installed start).steps =
      remainingSteps start := rfl

theorem installedCfg_prefix_physicalCells_le
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

theorem installedCfg_iterate
    (installed : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (n : Nat) (start : Option (Cfg Γ Λ R)) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (start.map (installedCfg names symbols registers labels)) =
      ((next caller)^[n] start).map (installedCfg names symbols registers labels) :=
  installed_iterate names symbols registers labels caller ambient installed n start

end FurtherCompleteInstallation



end Examples.RotationCertificateStreamMachine
