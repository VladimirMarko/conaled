import Examples.RotationCertificateFrontEndStreamMachine.RawExecution

/-!
# RotationCertificateFrontEndStreamMachine: Package
-/

namespace Examples.RotationCertificateFrontEndStreamMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.FrontEndStreamMachine

/-! ## Genuine finite packages, with exact initialization and halt conventions -/

def independentPackage (caller : ExampleCaller) (initial : Bool) : Turing.FinTM2 :=
  machine caller initial

def twoLabelPackage (caller : Fin 2 → Statement IndependentAlphabet (Fin 2) Bool)
    (initial : Bool) : Turing.FinTM2 := machine caller initial

theorem independent_package_has_the_actual_bundled_dimensions
    (caller : ExampleCaller) (initial : Bool) :
    @Fintype.card (independentPackage caller initial).K
        (independentPackage caller initial).kFin = 18 ∧
    @Fintype.card (independentPackage caller initial).Λ
        (independentPackage caller initial).ΛFin = 97 ∧
    @Fintype.card (independentPackage caller initial).σ
        (independentPackage caller initial).σFin = 280908 := by
  change @Fintype.card (machine caller initial).K (machine caller initial).kFin = 18 ∧
    @Fintype.card (machine caller initial).Λ (machine caller initial).ΛFin = 97 ∧
    @Fintype.card (machine caller initial).σ (machine caller initial).σFin = 280908
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using machine_card_stackId caller initial
  · simpa only [Fintype.card_unit] using machine_card_label caller initial
  · simpa only [Fintype.card_bool] using machine_card_registers caller initial

theorem two_label_package_has_the_actual_bundled_dimensions
    (caller : Fin 2 → Statement IndependentAlphabet (Fin 2) Bool) (initial : Bool) :
    @Fintype.card (twoLabelPackage caller initial).K
        (twoLabelPackage caller initial).kFin = 18 ∧
    @Fintype.card (twoLabelPackage caller initial).Λ
        (twoLabelPackage caller initial).ΛFin = 98 ∧
    @Fintype.card (twoLabelPackage caller initial).σ
        (twoLabelPackage caller initial).σFin = 280908 := by
  change @Fintype.card (machine caller initial).K (machine caller initial).kFin = 18 ∧
    @Fintype.card (machine caller initial).Λ (machine caller initial).ΛFin = 98 ∧
    @Fintype.card (machine caller initial).σ (machine caller initial).σFin = 280908
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using machine_card_stackId caller initial
  · simpa only [Fintype.card_fin] using machine_card_label caller initial
  · simpa only [Fintype.card_bool] using machine_card_registers caller initial

section ActualFinitePackage

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R]
  [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R) (initial : R)

theorem the_actual_package_uses_distinct_existing_boolean_input_and_output_stores :
    (machine caller initial).k₀ = Sum.inl FrontEndMachine.LocalStack.framedRaw ∧
    (machine caller initial).k₁ = Sum.inl FrontEndMachine.LocalStack.fuel ∧
    (machine caller initial).k₀ ≠ (machine caller initial).k₁ ∧
    (machine caller initial).Γ (machine caller initial).k₀ = Bool ∧
    (machine caller initial).Γ (machine caller initial).k₁ = Bool ∧
    (machine caller initial).main = phaseLabel rawEntryPhase ∧
    (machine caller initial).initialState = initialRegisters initial :=
  ⟨machine_input_index caller initial, machine_output_index caller initial,
    machine_input_ne_output caller initial, machine_input_alphabet caller initial,
    machine_output_alphabet caller initial, machine_main caller initial,
    machine_initialState caller initial⟩

theorem every_actual_physical_alphabet_has_a_finite_type
    (k : (machine caller initial).K) : Finite ((machine caller initial).Γ k) :=
  machine_alphabet_finite caller initial k

theorem genuine_initialization_supplies_only_the_framed_raw_word (raw : Bits) :
    Turing.initList (machine caller initial) raw =
      cfg (some (phaseLabel rawEntryPhase)) (initialRegisters initial)
        { framedRaw := raw } (fun _ => []) := machine_initList_eq caller initial raw

theorem genuine_halt_is_a_live_none_label_with_only_its_output_word (out : Bits) :
    Turing.haltList (machine caller initial) out =
      cfg none (initialRegisters initial) { fuel := out } (fun _ => []) :=
  machine_haltList_eq caller initial out

theorem a_cleaned_endpoint_is_the_literal_package_halt_exactly_for_the_initial_user_and_empty_context
    (out : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    cfg none (fullReset regs) { fuel := out } ctx =
      Turing.haltList (machine caller initial) out ↔
      user regs = initial ∧ ctx = (fun _ => []) :=
  machine_haltList_eq_iff caller initial out regs ctx

def RawFixture.PackageExpected (fixture : RawFixture) : Prop :=
  FirstHalt (machine caller initial).step
      (Turing.initList (machine caller initial) fixture.raw) fixture.ticks
      (Turing.haltList (machine caller initial) [fixture.result]) ∧
  ExactPeak (machine caller initial).step
      (Turing.initList (machine caller initial) fixture.raw) fixture.ticks fixture.peak ∧
  (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[fixture.ticks + 1]
      (some (Turing.initList (machine caller initial) fixture.raw)) = none

theorem a_connected_literal_run_connects_to_actual_initList_and_haltList
    (fixture : RawFixture)
    (output : fixture.after = ({ fuel := [fixture.result] } : LocalData))
    (connected : fixture.Expected (step caller) (initialRegisters initial) (fun _ => [])) :
    fixture.PackageExpected caller initial := by
  have startEq : (Turing.initList (machine caller initial) fixture.raw : Cfg Γ Λ R) =
      fixture.start (initialRegisters initial) (fun _ => []) :=
    machine_initList_eq caller initial fixture.raw
  have finishEq :
      (Turing.haltList (machine caller initial) [fixture.result] : Cfg Γ Λ R) =
        fixture.finish (initialRegisters initial) (fun _ => []) := by
    refine (machine_haltList_eq caller initial [fixture.result]).trans ?_
    change cfg none (initialRegisters initial) { fuel := [fixture.result] } (fun _ => []) =
      cfg none (fullReset (initialRegisters initial)) fixture.after (fun _ => [])
    rw [fullReset_initialRegisters, output]
  have first : FirstHalt (machine caller initial).step
      (Turing.initList (machine caller initial) fixture.raw) fixture.ticks
      (Turing.haltList (machine caller initial) [fixture.result]) := by
    change FirstHalt (step caller)
      (Turing.initList (machine caller initial) fixture.raw) fixture.ticks
      (Turing.haltList (machine caller initial) [fixture.result])
    exact (congrArg₂ (fun start finish : Cfg Γ Λ R =>
      FirstHalt (step caller) start fixture.ticks finish) startEq finishEq).mpr connected.1
  have actualPeak : ExactPeak (step caller)
      (fixture.start (initialRegisters initial) (fun _ => [])) fixture.ticks fixture.peak := by
    simpa only [externalCells, List.length_nil, Finset.sum_const_zero, Nat.add_zero]
      using connected.2.2.2
  have peak : ExactPeak (machine caller initial).step
      (Turing.initList (machine caller initial) fixture.raw) fixture.ticks fixture.peak := by
    change ExactPeak (step caller)
      (Turing.initList (machine caller initial) fixture.raw) fixture.ticks fixture.peak
    exact (congrArg (fun start : Cfg Γ Λ R =>
      ExactPeak (step caller) start fixture.ticks fixture.peak) startEq).mpr actualPeak
  refine ⟨first, peak, ?_⟩
  change (fun state : Option (Cfg Γ Λ R) => state.bind (step caller))^[fixture.ticks + 1]
    (some (Turing.initList (machine caller initial) fixture.raw)) = none
  have reached :
      (fun state : Option (Cfg Γ Λ R) => state.bind (step caller))^[fixture.ticks]
          (some (Turing.initList (machine caller initial) fixture.raw)) =
        some (Turing.haltList (machine caller initial) [fixture.result]) := first.1
  rw [Function.iterate_succ_apply', reached]
  rfl

theorem all_36_literal_rows_use_the_real_finite_package
    (fixture : RawFixture) (member : fixture ∈ rawCases) :
    fixture.PackageExpected caller initial := by
  have connected := all_original_raw_rows_execute_with_their_complete_endpoints_and_peaks
    caller (initialRegisters initial) (fun _ => []) fixture member
  apply a_connected_literal_run_connects_to_actual_initList_and_haltList caller initial
    fixture ?_ connected
  simp only [rawCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

end ActualFinitePackage

theorem both_concrete_packages_execute_every_original_raw_row
    (unitCaller : ExampleCaller)
    (twoCaller : Fin 2 → Statement IndependentAlphabet (Fin 2) Bool)
    (initial : Bool) (fixture : RawFixture) (member : fixture ∈ rawCases) :
    fixture.PackageExpected unitCaller initial ∧
    fixture.PackageExpected twoCaller initial :=
  ⟨all_36_literal_rows_use_the_real_finite_package unitCaller initial fixture member,
    all_36_literal_rows_use_the_real_finite_package twoCaller initial fixture member⟩

theorem a_preserved_nonempty_installed_context_is_not_the_genuine_package_halt
    (caller : ExampleCaller) (initial : Bool) (out : Bits) (regs : Registers Bool) :
    cfg none (fullReset regs) { fuel := out } ordinaryContext ≠
      Turing.haltList (independentPackage caller initial) out := by
  intro equal
  obtain ⟨_, empty⟩ := (machine_haltList_eq_iff caller initial out regs ordinaryContext).1 equal
  have impossible := congrFun empty (0 : Fin 2)
  change [true, false, true] = [] at impossible
  cases impossible

theorem the_preserved_user_register_can_also_separate_a_cleaned_endpoint_from_haltList
    (caller : ExampleCaller) (initial : Bool) (out : Bits) :
    cfg none (fullReset (stale (!initial))) { fuel := out }
        (emptyContext : ∀ k, List (IndependentAlphabet k)) ≠
      Turing.haltList (independentPackage caller initial) out := by
  intro equal
  have impossible := (machine_haltList_eq_iff caller initial out (stale (!initial)) emptyContext).1 equal
  have userEqual : (!initial) = initial := impossible.1
  cases initial <;> cases userEqual

theorem a_late_partial_clear_keeps_lower_slots_and_is_not_a_package_halt
    (caller : ExampleCaller) (initial : Bool) :
    cleanupC15.toClosedFixture.finish initial emptyContext ≠
      Turing.haltList (independentPackage caller initial) [true] := by
  intro equal
  have wordEqual := congrArg (fun c : ExampleCfg => c.stk (.inl .framedRaw)) equal
  change [true, false] = [] at wordEqual
  cases wordEqual

theorem dirty_direct_emit_pushes_onto_old_fuel_and_is_not_a_singleton_package_halt
    (caller : ExampleCaller) (initial : Bool) :
    emitE02.toClosedFixture.finish initial emptyContext ≠
      Turing.haltList (independentPackage caller initial) [true] := by
  intro equal
  have wordEqual := congrArg (fun c : ExampleCfg => c.stk (.inl .fuel)) equal
  change [true, false, true] = [true] at wordEqual
  cases wordEqual

theorem the_empty_direct_emit_fixture_has_the_package_output_without_using_its_initializer
    (caller : ExampleCaller) (initial : Bool) :
    emitE03.toClosedFixture.finish initial emptyContext =
      Turing.haltList (independentPackage caller initial) [false] := by
  exact (machine_haltList_eq caller initial [false]).symm

/-! ## Complete-carrier installations and the owned halt tail -/

section CompleteInstallationMaps

variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable (names : StackId K ≃ K') (symbols : ∀ k, Alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')

theorem complete_installation_reads_back_every_label_register_and_stack_word
    (c : Cfg Γ Λ R) :
    (installedCfgEquiv names symbols registers labels).symm
        (installedCfg names symbols registers labels c) = c ∧
    (installedCfg names symbols registers labels c).l = c.l.map labels ∧
    registers.symm (installedCfg names symbols registers labels c).var = c.var ∧
    ∀ k, ((installedCfg names symbols registers labels c).stk (names k)).map
        (symbols k).symm = c.stk k :=
  ⟨installedCfg_readback names symbols registers labels c,
    installedCfg_label names symbols registers labels c,
    installedCfg_registers_readback names symbols registers labels c,
    installedCfg_stack_readback names symbols registers labels c⟩

theorem complete_installation_preserves_the_full_physical_sum
    [Fintype K] [Fintype K'] (c : Cfg Γ Λ R) :
    (∑ k, ((installedCfg names symbols registers labels c).stk k).length) = physicalCells c :=
  installed_stack_cells names symbols registers labels c

end CompleteInstallationMaps

section OwnedInstallationExecution

variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable [DecidableEq K] [DecidableEq K']
variable (names : StackId K ≃ K') (symbols : ∀ k, Alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable (caller : Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
variable (installed : ∀ label, Owned (some label) →
  ambient (labels label) =
    FrontEndMachine.Transport.statement names symbols registers labels (program caller label))

omit names symbols registers labels caller installed [DecidableEq K] in
theorem any_live_halt_configuration_takes_one_step_to_outer_none
    (halted : Turing.TM2.Cfg Γ' Λ' R') (label : halted.l = none) :
    Turing.TM2.step ambient halted = none := by
  rcases halted with ⟨l, regs, words⟩
  cases label
  rfl

omit names symbols registers labels caller installed [DecidableEq K] in
theorem any_ambient_optional_iterator_keeps_outer_none (n : Nat) :
    (FrontEndMachine.Transport.next ambient)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

include installed in
theorem an_actual_owned_first_halt_transports_its_complete_endpoint_and_every_later_none
    (start finish : Cfg Γ Λ R) (ticks : Nat)
    (first : FirstHalt (step caller) start ticks finish) :
    (FrontEndMachine.Transport.next ambient)^[ticks]
        (some (installedCfg names symbols registers labels start)) =
      some (installedCfg names symbols registers labels finish) ∧
    (installedCfg names symbols registers labels finish).l = none ∧
    (∀ n, n < ticks → ∃ reached,
      (FrontEndMachine.Transport.next ambient)^[n]
          (some (installedCfg names symbols registers labels start)) = some reached ∧
      InstalledOwned labels reached.l) ∧
    ∀ extra, (FrontEndMachine.Transport.next ambient)^[ticks + 1 + extra]
        (some (installedCfg names symbols registers labels start)) = none := by
  have localRun : LocalRun caller ticks start finish :=
    LocalRun.of_iterate caller first.1 first.2.2
  have executed := installed_localRun names symbols registers labels caller ambient installed localRun
  have halted : (installedCfg names symbols registers labels finish).l = none := by
    rw [installedCfg_label, first.2.1]
    rfl
  refine ⟨executed, halted, ?_, ?_⟩
  · intro n strict
    exact installed_localRun_owned_prefix names symbols registers labels caller ambient
      installed localRun n strict
  · intro extra
    have vanished : (FrontEndMachine.Transport.next ambient)^[ticks + 1]
        (some (installedCfg names symbols registers labels start)) = none := by
      rw [Function.iterate_succ_apply', executed]
      exact any_live_halt_configuration_takes_one_step_to_outer_none ambient _ halted
    rw [Nat.add_comm (ticks + 1) extra, Function.iterate_add_apply, vanished]
    exact any_ambient_optional_iterator_keeps_outer_none ambient extra

include installed in
theorem every_actual_owned_prefix_uses_the_same_complete_installation
    (start finish : Cfg Γ Λ R) (ticks : Nat)
    (first : FirstHalt (step caller) start ticks finish) (n : Nat) (bound : n ≤ ticks) :
    (FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) := by
  exact installed_prefix_of_owned names symbols registers labels caller ambient installed n start
    (fun j earlier => first.2.2 j (Nat.lt_of_lt_of_le earlier bound))

include installed in
theorem every_literal_raw_case_has_the_same_installed_first_halt_and_halt_tail
    (fixture : RawFixture) (member : fixture ∈ rawCases)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (FrontEndMachine.Transport.next ambient)^[fixture.ticks]
        (some (installedCfg names symbols registers labels (fixture.start regs ctx))) =
      some (installedCfg names symbols registers labels (fixture.finish regs ctx)) ∧
    (installedCfg names symbols registers labels (fixture.finish regs ctx)).l = none ∧
    (∀ n, n < fixture.ticks → ∃ reached,
      (FrontEndMachine.Transport.next ambient)^[n]
          (some (installedCfg names symbols registers labels (fixture.start regs ctx))) = some reached ∧
      InstalledOwned labels reached.l) ∧
    ∀ extra, (FrontEndMachine.Transport.next ambient)^[fixture.ticks + 1 + extra]
        (some (installedCfg names symbols registers labels (fixture.start regs ctx))) = none := by
  have actual := all_original_raw_rows_have_their_actual_first_halt caller regs ctx fixture member
  exact an_actual_owned_first_halt_transports_its_complete_endpoint_and_every_later_none
    names symbols registers labels caller ambient installed _ _ _ actual

section InstalledPhysicalSpace

variable [Fintype K] [Fintype K']

include installed in
theorem actual_installed_prefixes_preserve_both_the_exact_peak_bound_and_its_attained_witness
    (start finish : Cfg Γ Λ R) (ticks peak : Nat)
    (first : FirstHalt (step caller) start ticks finish)
    (maximum : ExactPeak (step caller) start ticks peak) :
    (∀ n, n ≤ ticks → ∀ reached,
      (FrontEndMachine.Transport.next ambient)^[n]
          (some (installedCfg names symbols registers labels start)) = some reached →
      (∑ k, (reached.stk k).length) ≤ peak) ∧
    ∃ n reached, n ≤ ticks ∧
      (FrontEndMachine.Transport.next ambient)^[n]
          (some (installedCfg names symbols registers labels start)) = some reached ∧
      (∑ k, (reached.stk k).length) = peak := by
  constructor
  · intro n bound reached executed
    obtain ⟨source, sourceRun⟩ : ∃ source, (next caller)^[n] (some start) = some source := by
      by_cases last : n = ticks
      · subst n
        exact ⟨finish, first.1⟩
      · obtain ⟨source, sourceRun, _⟩ := first.2.2 n (by omega)
        exact ⟨source, sourceRun⟩
    have mapped := every_actual_owned_prefix_uses_the_same_complete_installation
      names symbols registers labels caller ambient installed start finish ticks first n bound
    rw [sourceRun] at mapped
    have same : reached = installedCfg names symbols registers labels source :=
      Option.some.inj (executed.symm.trans mapped)
    subst reached
    rw [installed_stack_cells]
    exact maximum.1 n bound source sourceRun
  · obtain ⟨n, source, bound, sourceRun, cells⟩ := maximum.2
    refine ⟨n, installedCfg names symbols registers labels source, bound, ?_, ?_⟩
    · have sourceIteration : (next caller)^[n] (some start) = some source := by
        change Runs (step caller) start n source
        exact sourceRun
      rw [every_actual_owned_prefix_uses_the_same_complete_installation names symbols registers
        labels caller ambient installed start finish ticks first n bound, sourceIteration]
      rfl
    · rw [installed_stack_cells]
      exact cells

end InstalledPhysicalSpace

omit installed in
theorem arbitrary_external_iterations_use_the_distinct_all_label_agreement_hypothesis
    (allLabels : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (n : Nat) (start : Option (Cfg Γ Λ R)) :
    (FrontEndMachine.Transport.next ambient)^[n]
        (start.map (installedCfg names symbols registers labels)) =
      ((next caller)^[n] start).map (installedCfg names symbols registers labels) :=
  installed_iterate names symbols registers labels caller ambient allLabels n start

end OwnedInstallationExecution

/-! ## Every owned domain and every actual configuration -/

section UniversalOwnedExecution

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

theorem every_owned_phase_has_its_exact_live_first_halt
    (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    0 < phaseSteps q D ∧
    FirstHalt (step caller) (cfg (some (phaseLabel q)) regs D ctx)
      (phaseSteps q D) (phaseResult q regs D ctx) :=
  ⟨phaseSteps_pos q D, phase_first_halt caller q D regs ctx⟩

theorem the_independently_listed_96_domains_all_have_the_full_arbitrary_state_contract
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∀ q ∈ phaseDomains,
      0 < phaseSteps q D ∧
      FirstHalt (step caller) (cfg (some (phaseLabel q)) regs D ctx)
        (phaseSteps q D) (phaseResult q regs D ctx) := by
  intro q _
  exact every_owned_phase_has_its_exact_live_first_halt caller q D regs ctx

theorem any_actual_first_boundary_fixes_the_entire_canonical_endpoint
    (start finish : Cfg Γ Λ R) (n : Nat) :
    FirstBoundary (step caller) start n finish ↔
      n = remainingSteps start ∧ finish = finalCfg start :=
  first_boundary_iff caller start finish n

theorem any_actual_first_halt_requires_the_canonical_endpoint_itself_to_be_halted
    (start finish : Cfg Γ Λ R) (n : Nat) :
    FirstHalt (step caller) start n finish ↔
      n = remainingSteps start ∧ finish = finalCfg start ∧ (finalCfg start).l = none :=
  first_halt_iff caller start finish n

theorem every_configuration_has_an_exact_boundary_but_only_owned_starts_force_halt
    (start : Cfg Γ Λ R) :
    FirstBoundary (step caller) start (remainingSteps start) (finalCfg start) ∧
    (Owned start.l → FirstHalt (step caller) start (remainingSteps start) (finalCfg start)) :=
  ⟨cfg_first_return caller start, cfg_first_halt caller start⟩

theorem every_actual_owned_step_decreases_the_exact_natural_rank_and_keeps_the_complete_endpoint
    (before after : Cfg Γ Λ R) (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 ∧ finalCfg before = finalCfg after :=
  ⟨local_step_remaining caller transition, finalCfg_step caller transition⟩

theorem every_positive_rank_has_an_actual_successor
    (start : Cfg Γ Λ R) (positive : 0 < remainingSteps start) :
    ∃ reached, step caller start = some reached ∧
      remainingSteps start = remainingSteps reached + 1 := local_progress caller start positive

theorem one_actual_prefix_witness_carries_rank_registers_context_and_final_state
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, Runs (step caller) start n reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      user reached.var = user start.var ∧
      (∀ k, reached.stk (.inr (.inr k)) = start.stk (.inr (.inr k))) ∧
      finalCfg reached = finalCfg start := owned_prefix_frame caller start n bound

theorem arbitrary_protected_registers_and_words_are_preserved_along_the_actual_local_relation
    (start reached : Cfg Γ Λ R)
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    user reached.var = user start.var ∧
      ∀ k, reached.stk (.inr (.inr k)) = start.stk (.inr (.inr k)) :=
  local_reaches_frame caller path

theorem every_owned_run_is_independent_of_later_caller_bodies_at_all_times
    (other : Λ → Statement Γ Λ R) (start : Cfg Γ Λ R)
    (owned : Owned start.l) (n : Nat) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) :=
  owned_iterate_caller_independent caller other start owned n

theorem an_ambient_program_needs_only_owned_body_agreement_even_after_the_halt
    (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ q, ambient (phaseLabel q) = program (fun _ => .halt) (phaseLabel q))
    (start : Cfg Γ Λ R) (owned : Owned start.l) (n : Nat) :
    (fun state : Option (Cfg Γ Λ R) => state.bind (Turing.TM2.step ambient))^[n] (some start) =
      (next caller)^[n] (some start) := ambient_owned_iterate_eq caller ambient agrees start owned n

theorem the_live_halt_time_and_outer_none_time_differ_by_one
    (start : Cfg Γ Λ R) (owned : Owned start.l) :
    FirstHalt (step caller) start (remainingSteps start) (finalCfg start) ∧
    (next caller)^[remainingSteps start + 1] (some start) = none ∧
    ∀ n, remainingSteps start < n → (next caller)^[n] (some start) = none :=
  ⟨cfg_first_halt caller start owned,
    cfg_halt_then_none caller start (finalCfg_halted_of_owned start owned),
    cfg_after_halt caller start (finalCfg_halted_of_owned start owned)⟩

def phaseExactTime (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel q)) regs D ctx)
      (some (phaseResult q regs D ctx)) (phaseSteps q D) := phaseInTime caller q D regs ctx

def configurationExactTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (step caller) start (some (finalCfg start)) (remainingSteps start) :=
  cfgInTime caller start

def ownedOuterNoneTime (start : Cfg Γ Λ R) (owned : Owned start.l) :
    StateTransition.EvalsToInTime (step caller) start none (remainingSteps start + 1) :=
  haltNoneInTime caller start (finalCfg_halted_of_owned start owned)

theorem exact_type_valued_times_retain_the_actual_activation_counts
    (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (start : Cfg Γ Λ R) (owned : Owned start.l) :
    (phaseExactTime caller q D regs ctx).steps = phaseSteps q D ∧
    (configurationExactTime caller start).steps = remainingSteps start ∧
    (ownedOuterNoneTime caller start owned).steps = remainingSteps start + 1 := ⟨rfl, rfl, rfl⟩

def rejectPrimitiveTime (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel rejectPhase)) regs D ctx)
      (some (cfg (some (clearLabel 0)) (answerRegisters false regs) D ctx)) 1 where
  steps := 1
  evals_in_steps := reject_step caller D regs ctx
  steps_le_m := Nat.le_refl _

def dispatchPrimitiveTime (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel dispatchPhase)) regs D ctx)
      (some (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase))) (fullReset regs) D ctx)) 1 where
  steps := 1
  evals_in_steps := dispatch_step caller D regs ctx
  steps_le_m := Nat.le_refl _

def resultPrimitiveTime (bit : Bool) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel (resultPhase bit))) regs D ctx)
      (some (cfg (some (clearLabel 0)) (answerRegisters bit regs) D ctx)) 1 where
  steps := 1
  evals_in_steps := result_step caller bit D regs ctx
  steps_le_m := Nat.le_refl _

theorem all_four_primitive_join_records_count_only_the_paid_immediate_activation
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (rejectPrimitiveTime caller D regs ctx).steps = 1 ∧
    (dispatchPrimitiveTime caller D regs ctx).steps = 1 ∧
    (resultPrimitiveTime caller false D regs ctx).steps = 1 ∧
    (resultPrimitiveTime caller true D regs ctx).steps = 1 := ⟨rfl, rfl, rfl, rfl⟩

end UniversalOwnedExecution

section UniversalPhysicalSpace

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : Λ → Statement Γ Λ R)

theorem the_dirty_allowance_bounds_the_same_actual_prefix_witness
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, Runs (step caller) start n reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      user reached.var = user start.var ∧
      (∀ k, reached.stk (.inr (.inr k)) = start.stk (.inr (.inr k))) ∧
      finalCfg reached = finalCfg start ∧ physicalCells reached ≤ allowance start :=
  owned_prefix_space caller start n bound

theorem every_actual_rank_bounded_prefix_has_the_total_physical_bound
    (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : Runs (step caller) start n reached) :
    physicalCells reached ≤ allowance start :=
  prefix_stackCells_le_dirty caller start n bound reached executed

theorem the_clean_input_bound_shares_its_rank_register_frame_and_clock_witness
    (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps raw) :
    ∃ reached, Runs (step caller) (entry regs raw ctx) n reached ∧
      remainingSteps reached = runSteps raw - n ∧
      Relation.ReflTransGen (LocalStep caller) (entry regs raw ctx) reached ∧
      (n < runSteps raw ↔ Owned reached.l) ∧
      (n = 0 → reached = entry regs raw ctx) ∧
      reached.var = registersAt (entry (Λ := Λ) regs raw ctx) n ∧ user reached.var = user regs ∧
      (∀ k, reached.stk (.inr (.inr k)) = ctx k) ∧
      finalCfg reached = runResult regs raw ctx ∧
      physicalCells reached ≤ max raw.length 1 + externalCells ctx ∧
      runSteps raw ≤ raw.length * raw.length + 10 * raw.length + 36 :=
  run_owned_prefix caller regs raw ctx n bound

end UniversalPhysicalSpace

/-! ## Complete clean outputs, source recognition, and distinct time tariffs -/

section CompleteCleanOutputs

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

theorem the_complete_first_output_is_fixed_for_both_boolean_results
    (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (finish : Cfg Γ Λ R) :
    FirstHalt (step caller) (entry regs raw ctx) n finish ↔
      n = runSteps raw ∧
      finish = cfg none (fullReset regs) { fuel := [BitPairFraming.verifyFramed raw] } ctx :=
  run_first_halt_iff caller regs raw ctx n finish

theorem a_specified_singleton_boolean_first_output_fixes_the_clock_and_source_boolean
    (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (bit : Bool) :
    FirstHalt (step caller) (entry regs raw ctx) n
        (cfg none (fullReset regs) { fuel := [bit] } ctx) ↔
      n = runSteps raw ∧ BitPairFraming.verifyFramed raw = bit := by
  rw [the_complete_first_output_is_fixed_for_both_boolean_results caller]
  constructor
  · rintro ⟨count, endpoint⟩
    have output := congrArg (fun c : Cfg Γ Λ R => c.stk (.inl .fuel)) endpoint
    change [bit] = [BitPairFraming.verifyFramed raw] at output
    exact ⟨count, (List.cons.inj output).1.symm⟩
  · rintro ⟨count, value⟩
    exact ⟨count, by rw [value]⟩

open Trees.Rotations (applyMoves?)

theorem actual_true_first_output_is_exactly_the_complete_framed_rotation_language
    (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (∃ n finish, FirstHalt (step caller) (entry regs raw ctx) n finish ∧
      finish.stk (.inl .fuel) = [true]) ↔
      ∃ (source target : BinaryTree Unit) (fuel : Bits) (moves : List RotationMove),
        raw = BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits (certCode moves)) ∧
        applyMoves? moves source = some target ∧ moves.length ≤ Resources.BinaryCounter.value fuel :=
  run_accept_iff caller regs raw ctx

theorem actual_false_first_output_is_the_complete_complement_for_every_raw_word
    (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (∃ n, FirstHalt (step caller) (entry regs raw ctx) n
      (cfg none (fullReset regs) { fuel := [false] } ctx)) ↔
      ¬ ∃ (source target : BinaryTree Unit) (fuel : Bits) (moves : List RotationMove),
        raw = BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits (certCode moves)) ∧
        applyMoves? moves source = some target ∧ moves.length ≤ Resources.BinaryCounter.value fuel := by
  rw [← BitPairFraming.verifyFramed_accept_iff_trace]
  constructor
  · rintro ⟨n, first⟩ accepted
    have value := (a_specified_singleton_boolean_first_output_fixes_the_clock_and_source_boolean
      caller raw regs ctx n false).1 first
    rw [accepted] at value
    cases value.2
  · intro rejected
    have value : BitPairFraming.verifyFramed raw = false := by
      cases result : BitPairFraming.verifyFramed raw
      · rfl
      · exact False.elim (rejected result)
    exact ⟨runSteps raw,
      (a_specified_singleton_boolean_first_output_fixes_the_clock_and_source_boolean
        caller raw regs ctx (runSteps raw) false).2 ⟨rfl, value⟩⟩

def rawExactTime (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw ctx)
      (some (runResult regs raw ctx)) (runSteps raw) := runInTimeExact caller regs raw ctx

def rawPolynomialTime (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw ctx)
      (some (runResult regs raw ctx)) (raw.length * raw.length + 10 * raw.length + 36) :=
  runInTimePolynomial caller regs raw ctx

theorem the_polynomial_time_record_still_records_the_exact_executed_count
    (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (rawExactTime caller raw regs ctx).steps = runSteps raw ∧
    (rawPolynomialTime caller raw regs ctx).steps = runSteps raw := ⟨rfl, rfl⟩

end CompleteCleanOutputs

theorem each_front_end_failure_priority_has_its_own_literal_cleanup_cost
    (raw cert : Bits) (input : Word) (source target : BinaryTree Unit) (fuel : Bits) :
    (FrontEndMachine.sourceOutcome raw = .frameFailure →
      runSteps raw = FrontEndMachine.runSteps raw + 18) ∧
    (FrontEndMachine.sourceOutcome raw = .inputDecodeFailure cert →
      runSteps raw = FrontEndMachine.runSteps raw + cert.length + 18) ∧
    (FrontEndMachine.sourceOutcome raw = .inputParseFailure input cert →
      runSteps raw = FrontEndMachine.runSteps raw + input.length + cert.length + 18) ∧
    (FrontEndMachine.sourceOutcome raw = .certificateDecodeFailure source target fuel →
      runSteps raw = FrontEndMachine.runSteps raw + (treeCode source).length +
        (treeCode target).length + fuel.length + 18) :=
  ⟨runSteps_frameFailure raw, runSteps_inputDecodeFailure raw cert,
    runSteps_inputParseFailure raw input cert,
    runSteps_certificateDecodeFailure raw source target fuel⟩

theorem successful_front_end_syntax_charges_the_actual_stream_endpoint_mass
    (raw : Bits) (source target : BinaryTree Unit) (fuel : Bits) (cert : Word)
    (returned : FrontEndMachine.sourceOutcome raw = .success source target fuel cert) :
    runSteps raw = FrontEndMachine.runSteps raw +
      StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) +
      StreamMachine.localCells (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).data + 19 :=
  runSteps_success raw source target fuel cert returned

theorem represented_inputs_retain_the_full_machine_clock_on_success_or_rejection
    (source target : BinaryTree Unit) (fuel : Bits) (cert : Word) :
    runSteps (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) =
      12 * (inputCode source target fuel).length + 10 * cert.length +
      StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) +
      StreamMachine.localCells (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).data + 30 :=
  runSteps_code source target fuel cert

theorem only_the_accepting_stream_premise_reduces_final_mass_to_the_fuel_width
    (source target : BinaryTree Unit) (fuel : Bits) (cert : Word)
    (accepted : (checkStreamRun fuel source target cert).1 = true) :
    runSteps (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) =
      12 * (inputCode source target fuel).length + 10 * cert.length +
      StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) + fuel.length + 30 :=
  runSteps_accepting_code source target fuel cert accepted

theorem represented_raw_boolean_agrees_with_the_measured_stream_source
    (source target : BinaryTree Unit) (fuel : Bits) (cert : Word) :
    BitPairFraming.verifyFramed
        (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) =
      (checkStreamRun fuel source target cert).1 := by
  rw [BitPairFraming.verifyFramed_frame, verifyBitsRun_code_value, verifyRun_code]

section RepresentedCompleteOutputs

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

theorem represented_first_halt_keeps_both_outcomes_and_all_final_fields
    (source target : BinaryTree Unit) (fuel : Bits) (cert : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (finish : Cfg Γ Λ R) :
    FirstHalt (step caller)
        (entry regs (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) ctx)
        n finish ↔
      n = 12 * (inputCode source target fuel).length + 10 * cert.length +
        StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) +
        StreamMachine.localCells (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).data + 30 ∧
      finish = cfg none (fullReset regs) { fuel := [(checkStreamRun fuel source target cert).1] } ctx := by
  rw [the_complete_first_output_is_fixed_for_both_boolean_results caller,
    runSteps_code, represented_raw_boolean_agrees_with_the_measured_stream_source]

def representedExactTime (source target : BinaryTree Unit) (fuel : Bits) (cert : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) ctx)
      (some (cfg none (fullReset regs) { fuel := [(checkStreamRun fuel source target cert).1] } ctx))
      (12 * (inputCode source target fuel).length + 10 * cert.length +
        StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) +
        StreamMachine.localCells (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).data + 30) where
  steps := 12 * (inputCode source target fuel).length + 10 * cert.length +
    StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) +
    StreamMachine.localCells (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).data + 30
  evals_in_steps := by
    rw [← runSteps_code]
    change (next caller)^[runSteps
      (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert))]
        (some (entry regs
          (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) ctx)) = _
    simpa only [represented_raw_boolean_agrees_with_the_measured_stream_source] using
      (run_verifyFramed caller regs
        (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) ctx).1
  steps_le_m := Nat.le_refl _

theorem represented_type_valued_time_retains_the_actual_endpoint_mass
    (source target : BinaryTree Unit) (fuel : Bits) (cert : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (representedExactTime caller source target fuel cert regs ctx).steps =
      12 * (inputCode source target fuel).length + 10 * cert.length +
      StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) +
      StreamMachine.localCells (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).data + 30 := rfl

end RepresentedCompleteOutputs

theorem framing_failure_has_no_invented_bit_verifier_observation
    (raw : Bits) (failed : BitPairFraming.unframe raw = none) : sourceObservation raw = none :=
  sourceObservation_frame_failure raw failed

theorem input_decoder_failure_retains_its_existing_source_tariff
    (raw input cert : Bits) (framed : BitPairFraming.unframe raw = some (input, cert))
    (failed : (unpackWordRun input).1 = none) :
    sourceObservation raw = some (false, (unpackWordRun input).2 + 2) :=
  sourceObservation_input_decode_failure raw input cert framed failed

theorem input_parser_failure_retains_its_existing_source_tariff
    (raw input cert : Bits) (word : Word)
    (framed : BitPairFraming.unframe raw = some (input, cert))
    (decoded : (unpackWordRun input).1 = some word) (failed : (parseInputRun word).1 = none) :
    sourceObservation raw = some (false, (unpackWordRun input).2 + (parseInputRun word).2 + 2) :=
  sourceObservation_input_parse_failure raw input cert word framed decoded failed

theorem certificate_decoder_failure_retains_its_existing_source_tariff
    (raw input cert : Bits) (word : Word) (source target : BinaryTree Unit) (fuel : Bits)
    (framed : BitPairFraming.unframe raw = some (input, cert))
    (decoded : (unpackWordRun input).1 = some word)
    (parsed : (parseInputRun word).1 = some (source, target, fuel))
    (failed : (unpackWordRun cert).1 = none) :
    sourceObservation raw = some (false, (unpackWordRun input).2 + (parseInputRun word).2 +
      (unpackWordRun cert).2 + 2) :=
  sourceObservation_certificate_decode_failure raw input cert word source target fuel framed decoded parsed failed

theorem successful_decoding_retains_the_actual_stream_source_tariff
    (raw input cert : Bits) (word moves : Word) (source target : BinaryTree Unit) (fuel : Bits)
    (framed : BitPairFraming.unframe raw = some (input, cert))
    (decoded : (unpackWordRun input).1 = some word)
    (parsed : (parseInputRun word).1 = some (source, target, fuel))
    (certificate : (unpackWordRun cert).1 = some moves) :
    sourceObservation raw = some ((checkStreamRun fuel source target moves).1,
      (unpackWordRun input).2 + (parseInputRun word).2 + (unpackWordRun cert).2 +
        (checkStreamRun fuel source target moves).2 + 1) :=
  sourceObservation_success raw input cert word moves source target fuel framed decoded parsed certificate


end Examples.RotationCertificateFrontEndStreamMachine
