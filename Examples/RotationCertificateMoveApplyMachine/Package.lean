import Examples.RotationCertificateMoveApplyMachine.Source

/-!
# RotationCertificateMoveApplyMachine: Package
-/

namespace Examples.RotationCertificateMoveApplyMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.MoveApplyMachine

section GenericPackageConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : External Λ → Statement Γ Λ R) (initial : R)

theorem actual_package_executes_every_installed_configuration
    (start : Cfg Γ Λ R) :
    (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[remainingSteps start]
      (some start) = some (finalCfg start) := machine_cfg_run caller initial start

def installedPackageInActualTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (machine caller initial).step start
      (some (finalCfg start)) (remainingSteps start) := machineCfgInTime caller initial start

theorem installed_package_timing_keeps_its_actual_rank (start : Cfg Γ Λ R) :
    (installedPackageInActualTime caller initial start).steps = remainingSteps start := rfl

theorem package_prefix_space_counts_all_seven_local_stores_and_the_context
    (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[n]
      (some start) = some reached) : stackCells reached ≤ potential start :=
  machine_prefix_space caller initial start n bound reached executed

theorem real_initializer_sets_only_certificate_and_resets_all_temporaries (C : Word) :
    Turing.initList (machine caller initial) C =
      cfg (some (moveLabel .start)) ((none, (none, none)), initial)
        (data C [] [] [] [] [] []) (fun _ => []) := initList_eq caller initial C

theorem every_genuine_input_first_returns_one_of_the_two_live_failures (C : Word) :
    (initOutcome C = parseFailure ∨ initOutcome C = rotationFailure) ∧
      (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[initClock C]
        (some (Turing.initList (machine caller initial) C)) =
          some (cfg (some (resultLabel (initOutcome C))) ((none, (none, none)), initial)
            (initData C) (fun _ => [])) ∧
      ∀ j, j < initClock C → ∃ reached,
        (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[j]
          (some (Turing.initList (machine caller initial) C)) = some reached ∧ Owned reached.l :=
  machine_init_first_result caller initial C

def genuineInitializerInActualTime (C : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) C)
      (some (cfg (some (resultLabel (initOutcome C))) ((none, (none, none)), initial)
        (initData C) (fun _ => []))) (initClock C) where
  steps := initClock C
  evals_in_steps := (machine_init_first_result caller initial C).2.1
  steps_le_m := Nat.le_refl _

theorem actual_initializer_time_is_its_branch_specific_count (C : Word) :
    (genuineInitializerInActualTime caller initial C).steps = initClock C := rfl

theorem every_genuine_initializer_prefix_fits_the_actual_input_word
    (C : Word) (n : Nat) (bound : n ≤ initClock C) (reached : Cfg Γ Λ R)
    (executed : (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[n]
      (some (Turing.initList (machine caller initial) C)) = some reached) :
    stackCells reached ≤ C.length := machine_init_space caller initial C n bound reached executed

end GenericPackageConnections

def InitFixture.Expected (c : InitFixture) (caller : ExampleCaller) (initial : Bool) : Prop :=
  let start := Turing.initList (independentPackage caller initial) c.input
  let finish := cfg (some (resultLabel c.result)) (clean initial)
    (data c.certificate [] c.path [] [] [] []) (fun _ : Fin 2 => [])
  FirstRun caller start c.ticks finish ∧
    (fun state : Option ExampleCfg => state.bind (independentPackage caller initial).step)^[c.ticks]
      (some start) = some finish ∧
    HasExactPeak caller start c.ticks c.peak

theorem initializer_fixture_observations (c : InitFixture) (member : c ∈ initFixtures) :
    initClock c.input = c.ticks ∧ initOutcome c.input = c.result ∧
      initData c.input = data c.certificate [] c.path [] [] [] [] ∧ c.input.length = c.peak := by
  simp only [initFixtures, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem all_five_literal_initializers_use_the_actual_package_first_return_and_exact_peak
    (caller : ExampleCaller) (initial : Bool) (c : InitFixture) (member : c ∈ initFixtures) :
    c.Expected caller initial := by
  obtain ⟨clock, outcome, physical, peak⟩ := initializer_fixture_observations c member
  have actual := machine_init_first_result caller initial c.input
  rw [clock, outcome, physical] at actual
  refine ⟨⟨actual.2.1, not_owned_result c.result, actual.2.2⟩, actual.2.1, ?_⟩
  have rank : remainingSteps (Turing.initList (independentPackage caller initial) c.input) = c.ticks := by
    rw [show Turing.initList (independentPackage caller initial) c.input =
      cfg (some (moveLabel .start)) (clean initial) (data c.input [] [] [] [] [] []) (fun _ => [])
        from initList_eq caller initial c.input]
    exact (initClock_eq c.input).trans clock
  apply exact_peak_of_the_universal_actual_bound_and_an_attained_prefix caller _ _ _ rank
  · intro n bound reached executed
    have cells := machine_init_space caller initial c.input n (by omega) reached executed
    omega
  · refine ⟨0, Turing.initList (independentPackage caller initial) c.input, by omega, rfl, ?_⟩
    rw [show Turing.initList (independentPackage caller initial) c.input =
      cfg (some (moveLabel .start)) (clean initial) (data c.input [] [] [] [] [] []) (fun _ => [])
        from initList_eq caller initial c.input, stackCells_cfg]
    simpa [localCells, data, contextCells] using peak

theorem certificate_only_root_input_has_empty_source_and_an_eight_step_failure
    (caller : ExampleCaller) (initial : Bool) :
    FirstRun caller (Turing.initList (independentPackage caller initial) ([6,10] : Word)) 8
      (cfg (some (resultLabel rotationFailure)) (clean initial) (data [] [] [] [] [] [] [])
        (fun _ : Fin 2 => [])) ∧
      (Turing.initList (independentPackage caller initial) ([6,10] : Word)).stk (.inl .source) = [] ∧
      treeCode nilTree = [0] ∧
      (Turing.initList (independentPackage caller initial) ([6,10] : Word)).stk (.inl .source) ≠ treeCode nilTree := by
  have actual := (machine_init_first_result caller initial ([6,10] : Word)).2
  refine ⟨⟨actual.1, not_owned_result rotationFailure, actual.2⟩, ?_, rfl, ?_⟩
  · change ([] : Word) = []
    rfl
  · change ([] : Word) ≠ [0]
    intro impossible
    cases impossible

theorem installed_root_tree_success_is_a_different_actual_eleven_step_configuration
    (caller : ExampleCaller) (initial : Bool) :
    FirstRun caller
      (cfg (some (moveLabel .start)) (clean initial)
        (data [6,10] [] [] (treeCode rightTwo) [] [] []) independentContext)
      11
      (cfg (some (resultLabel rotationSuccess)) (clean initial)
        (data [] [] [] (treeCode leftTwo) [] [] []) independentContext) ∧
    Turing.initList (independentPackage caller initial) ([6,10] : Word) ≠
      cfg (some (moveLabel .start)) (clean initial)
        (data [6,10] [] [] (treeCode rightTwo) [] [] []) independentContext := by
  have actual : LocalRun caller 11
      (cfg (some (moveLabel .start)) (clean initial)
        (data [6,10] [] [] (treeCode rightTwo) [] [] []) independentContext)
      (cfg (some (resultLabel rotationSuccess)) (clean initial)
        (data [] [] [] (treeCode leftTwo) [] [] []) independentContext) :=
    root_left_pattern_localRun caller nilTree [0,0] [] [] (clean initial) independentContext
  refine ⟨⟨LocalRun.iterate caller actual, not_owned_result rotationSuccess,
    fun n before => LocalRun.owned_prefix caller actual n before⟩, ?_⟩
  intro equal
  have source := congrArg (fun state : ExampleCfg => state.stk (.inl .source)) equal
  change ([] : Word) = [1,0,1,0,0] at source
  cases source

section FurtherInstallationConnections
variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable [DecidableEq K] [DecidableEq K']
variable (caller : External Λ → Statement Γ Λ R)
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
variable (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
variable (installed : ∀ label, Owned (some label) →
  ambient (labels label) =
    FrontEndMachine.Transport.statement names symbols registers labels (program caller label))

include installed in
theorem a_complete_installation_preserves_every_actual_owned_prefix
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (FrontEndMachine.Transport.cfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map
        (FrontEndMachine.Transport.cfg names symbols registers labels) :=
  installed_owned_prefix caller names symbols registers labels ambient installed start n bound

def furtherInstallationInActualTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (FrontEndMachine.Transport.cfg names symbols registers labels start)
      (some (FrontEndMachine.Transport.cfg names symbols registers labels (finalCfg start)))
      (remainingSteps start) :=
  installed_owned_timed caller names symbols registers labels ambient installed start

theorem complete_installed_timing_keeps_the_exact_local_steps (start : Cfg Γ Λ R) :
    (furtherInstallationInActualTime caller names symbols registers labels ambient installed start).steps =
      remainingSteps start := rfl

def furtherPrefixInActualTime (start reached : Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ remainingSteps start) (actual : Runs caller start n reached) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (FrontEndMachine.Transport.cfg names symbols registers labels start)
      (some (FrontEndMachine.Transport.cfg names symbols registers labels reached)) n :=
  installed_owned_prefix_timed caller names symbols registers labels ambient installed
    start n bound reached actual

section Physical
variable [Fintype K] [Fintype K']

omit [DecidableEq K] [DecidableEq K'] in
theorem all_complete_stack_equivalences_preserve_the_actual_sum
    (start : Cfg Γ Λ R) :
    (∑ k, ((FrontEndMachine.Transport.cfg names symbols registers labels start).stk k).length) =
      stackCells start := installed_stack_cells names symbols registers labels start

include caller installed in
theorem owned_installation_space_needs_no_agreement_at_the_later_caller_labels
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (actual : (FrontEndMachine.Transport.next ambient)^[n]
      (some (FrontEndMachine.Transport.cfg names symbols registers labels start)) = some reached) :
    (∑ k, (reached.stk k).length) ≤ potential start :=
  installed_owned_prefix_space caller names symbols registers labels ambient installed
    start n bound reached actual

end Physical

/-- Full caller continuation transport has the explicitly stronger all-label premise. -/
theorem later_caller_iterations_require_complete_program_agreement
    (everyLabel : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (n : Nat) (start : Option (Cfg Γ Λ R)) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (start.map (FrontEndMachine.Transport.cfg names symbols registers labels)) =
      ((next caller)^[n] start).map (FrontEndMachine.Transport.cfg names symbols registers labels) :=
  installed_iterate caller names symbols registers labels ambient everyLabel n start

end FurtherInstallationConnections

theorem natural_number_callers_keep_finite_physical_stores_and_the_full_prefix_contract
    (caller : External Nat → Statement IndependentAlphabet Nat Bool)
    (start : Cfg IndependentAlphabet Nat Bool) (n : Nat) :
    Fintype.card (OwnedLabel Nat) = 26 ∧ Fintype.card (StackId (Fin 2)) = 9 ∧
      PrefixSpaceExpected caller start n :=
  ⟨card_ownedLabel, by simpa using (card_stackId (K := Fin 2)),
    every_dirty_prefix_has_the_same_rank_frame_register_and_physical_witness caller start n⟩

section FrontEndOneCallSpace
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]

theorem clean_added_branch_words_give_the_fixed_front_end_one_call_bound
    (physicalCaller : External Λ → Statement (frontEndProtectedAlphabet Γ) Λ
      (OpenDecoderMachine.Temporaries × R))
    (regs : FrontEndMachine.Registers (Option Branch × R))
    (source target : BinaryTree Unit) (fuel : List Bool) (cert : Word)
    (ctx : ∀ k, List (Γ k)) (n : Nat)
    (bound : n ≤ phaseSteps (movePhase .start) (frontEndSuccessData source cert [] []))
    (reached : Cfg (frontEndProtectedAlphabet Γ) Λ (OpenDecoderMachine.Temporaries × R))
    (actual : Runs physicalCaller
      (cfg (Λ := Λ) (some (moveLabel .start)) (frontEndRegisterEquiv (FrontEndMachine.reset regs))
        (frontEndSuccessData source cert [] []) (frontEndSuccessContext target fuel ctx)) n reached) :
    stackCells reached ≤ cert.length + 2 * (treeCode source).length +
      (treeCode target).length + fuel.length + ∑ k, (ctx k).length :=
  frontEnd_success_prefix_space physicalCaller regs source target fuel cert ctx n bound reached actual

end FrontEndOneCallSpace

section ComponentPrefixSpecializations
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem every_parser_phase_prefix_preserves_its_actual_tree_complement
    (q : MoveParserMachine.Phase) (D : LocalData) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ MoveParserMachine.phaseSteps q D.certificate D.moveReverse)
    (actual : Runs caller (cfg (some (moveLabel q)) regs D ctx) n reached) :
    reached.var = (if n = 0 then regs else resetMove regs) ∧ reached.var.2 = regs.2 ∧
      reached.stk (.inl .source) = D.source ∧ reached.stk (.inl .saved) = D.saved ∧
      reached.stk (.inl .scratch) = D.scratch ∧ reached.stk (.inl .pending) = D.pending ∧
      ∀ k, reached.stk (.inr k) = ctx k :=
  move_phase_prefix_frame caller q D regs ctx n reached bound actual

theorem every_position_phase_prefix_preserves_its_actual_certificate_complement
    (q : PositionedRotationMachine.Phase) (D : LocalData) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ PositionedRotationMachine.phaseSteps q (positionData D))
    (actual : Runs caller (cfg (some (positionLabel q)) regs D ctx) n reached) :
    reached.var = (if n = 0 then regs else reset regs) ∧ reached.var.2 = regs.2 ∧
      reached.stk (.inl .certificate) = D.certificate ∧
      reached.stk (.inl .moveReverse) = D.moveReverse ∧
      ∀ k, reached.stk (.inr k) = ctx k :=
  position_phase_prefix_frame caller q D regs ctx n reached bound actual

theorem clean_two_branch_parse_has_its_literal_internal_path_at_seven_and_paid_entry_at_eight :
    Runs caller (cfg (some (moveLabel .start)) regs
      (data [6,8,9,10] [] [] (treeCode nestedRight) [] [] []) ctx) 7
      (cfg (some (dispatchLabel (.success .left))) (resetMove regs)
        (data [] [] [.left,.right] (treeCode nestedRight) [] [] []) ctx) ∧
    Runs caller (cfg (some (moveLabel .start)) regs
      (data [6,8,9,10] [] [] (treeCode nestedRight) [] [] []) ctx) 8
      (cfg (some (positionLabel (.seek .left))) (reset regs)
        (data [] [] [.left,.right] (treeCode nestedRight) [] [] []) ctx) :=
  ⟨parse_success_boundary caller [6,8,9,10] ⟨.left,[.left,.right]⟩ [] []
      (treeCode nestedRight) [] [] [] regs ctx rfl,
    paid_position_entry caller [6,8,9,10] ⟨.left,[.left,.right]⟩ [] []
      (treeCode nestedRight) [] [] [] regs ctx rfl⟩

theorem the_internal_parser_success_is_owned_and_the_whole_success_is_external
    (d : RotationDirection) :
    Owned (some (dispatchLabel (Λ := Λ) (.success d))) ∧
      ¬ Owned (some (resultLabel (Λ := Λ) rotationSuccess)) :=
  ⟨True.intro, not_owned_result rotationSuccess⟩

end ComponentPrefixSpecializations

theorem every_fixed_halt_caller_has_the_paid_live_halt_and_outer_none_boundaries
    (flag : Bool) (c : RunFixture) (member : c ∈ fixedRuns) :
    FirstRun haltCaller (atPhase c.phase flag c.before) c.ticks (atResult c.result flag c.after) ∧
      Runs haltCaller (atPhase c.phase flag c.before) (c.ticks + 1)
        (cfg none (clean flag) c.after independentContext) ∧
      (next haltCaller)^[c.ticks + 2] (some (atPhase c.phase flag c.before)) = none := by
  have first := every_fixed_run_is_an_actual_first_live_result haltCaller (stale flag) independentContext c member
  have halt := (halt_is_one_paid_activation_before_outer_none c.result (clean flag) c.after independentContext).1
  have stopped := append_actual_step haltCaller (atPhase c.phase flag c.before)
    (atResult c.result flag c.after) c.ticks first.1
    (some (cfg none (clean flag) c.after independentContext)) halt
  refine ⟨first, stopped, ?_⟩
  exact append_actual_step haltCaller (atPhase c.phase flag c.before)
    (cfg none (clean flag) c.after independentContext) (c.ticks + 1) stopped none rfl

theorem initially_present_halt_has_identity_zero_prefix_and_immediate_outer_none
    (flag : Bool) (D : LocalData) :
    remainingSteps (cfg none (stale flag) D independentContext : ExampleCfg) = 0 ∧
      Runs haltCaller (cfg none (stale flag) D independentContext) 0
        (cfg none (stale flag) D independentContext) ∧
      next haltCaller (some (cfg none (stale flag) D independentContext)) = none := ⟨rfl, rfl, rfl⟩

theorem arbitrary_sentinel_callers_agree_through_eleven_and_differ_at_twelve
    (marker other : Tag) (distinct : marker ≠ other) (flag : Bool) :
    (∀ n, n ≤ 11 →
      (next (sentinelHaltCaller marker))^[n] (some (authorRootStart flag)) =
        (next (sentinelHaltCaller other))^[n] (some (authorRootStart flag))) ∧
    (next (sentinelHaltCaller marker))^[12] (some (authorRootStart flag)) ≠
      (next (sentinelHaltCaller other))^[12] (some (authorRootStart flag)) := by
  constructor
  · intro n bound
    apply prefix_caller_independent (sentinelHaltCaller marker) (sentinelHaltCaller other)
    have clock := (LocalRun.phaseEndpoint (sentinelHaltCaller marker)
      (q := MoveApplyMachine.movePhase .start)
      (root_left_segment_with_arbitrary_certificate_suffix
        (sentinelHaltCaller marker) (stale flag) authorContext [])).1
    change remainingSteps (authorRootStart flag) = 11 at clock
    rw [clock]
    exact bound
  · rw [(sentinel_caller_has_live_eleven_present_halt_twelve_and_outer_none_thirteen marker flag).2.1,
      (sentinel_caller_has_live_eleven_present_halt_twelve_and_outer_none_thirteen other flag).2.1]
    intro same
    have tags := congrArg (fun state : AuthorCfg => state.stk (.inr (0 : Fin 2))) (Option.some.inj same)
    exact distinct (List.cons.inj tags).1

section LiteralPeakSpecializations
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem literal_left_table_has_the_exact_initial_peak :
    HasExactPeak caller
      (cfg (some (moveLabel .start)) regs (data [6,10,15] [] [] [1,0,1,15] [] [] []) ctx)
      11 (7 + contextCells ctx) := by
  constructor
  · intro n bound
    let b := leftBoundaries[n]'(by change n < 12; omega)
    have member : b ∈ leftBoundaries := List.getElem_mem _
    have fields : b.tick = n ∧ b.cells ≤ 7 := by
      interval_cases n <;> exact ⟨rfl, of_decide_eq_true rfl⟩
    obtain ⟨tick, cells⟩ := fields
    have actual := every_left_literal_boundary_satisfies_the_complete_fixed_contract regs ctx caller b member
    refine ⟨b.cfg regs ctx, ?_, ?_⟩
    · simpa only [tick] using actual.1
    · rw [actual.2.2.2.2.2.1]
      omega
  · refine ⟨0, by omega, _, rfl, ?_⟩
    rw [stackCells_cfg]
    rfl

theorem literal_right_table_has_the_exact_initial_peak :
    HasExactPeak caller
      (cfg (some (moveLabel .start)) regs (data [7,10,15] [] [] [1,1,0,15] [] [] []) ctx)
      10 (7 + contextCells ctx) := by
  constructor
  · intro n bound
    let b := rightBoundaries[n]'(by change n < 11; omega)
    have member : b ∈ rightBoundaries := List.getElem_mem _
    have fields : b.tick = n ∧ b.cells ≤ 7 := by
      interval_cases n <;> exact ⟨rfl, of_decide_eq_true rfl⟩
    obtain ⟨tick, cells⟩ := fields
    have actual := every_right_literal_boundary_satisfies_the_complete_fixed_contract regs ctx caller b member
    refine ⟨b.cfg regs ctx, ?_, ?_⟩
    · simpa only [tick] using actual.1
    · rw [actual.2.2.2.2.2.1]
      omega
  · refine ⟨0, by omega, _, rfl, ?_⟩
    rw [stackCells_cfg]
    rfl

theorem literal_parser_failure_table_has_the_exact_initial_peak :
    HasExactPeak caller
      (cfg (some (moveLabel .start)) regs (failureData [6,8,9] []) ctx)
      8 (12 + contextCells ctx) := by
  constructor
  · intro n bound
    let b := parseFailureBoundaries[n]'(by change n < 9; omega)
    have member : b ∈ parseFailureBoundaries := List.getElem_mem _
    have fields : b.tick = n ∧ b.cells ≤ 12 := by
      interval_cases n <;> exact ⟨rfl, of_decide_eq_true rfl⟩
    obtain ⟨tick, cells⟩ := fields
    have actual := every_parser_failure_boundary_satisfies_the_complete_fixed_contract regs ctx caller b member
    refine ⟨b.cfg regs ctx, ?_, ?_⟩
    · simpa only [tick] using actual.1
    · rw [actual.2.2.2.2.2.1]
      omega
  · refine ⟨0, by omega, _, rfl, ?_⟩
    rw [stackCells_cfg]
    rfl

end LiteralPeakSpecializations

section ActualPackageRepresentedTiming
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : External Λ → Statement Γ Λ R) (initial : R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

def representedPackageInActualTime (mv : RotationMove) (rest : Word) (O : List Branch)
    (s : BinaryTree Unit) (F z : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (cfg (Λ := Λ) (some (moveLabel .start)) regs
        (data (moveCode mv ++ rest) [] O (treeCode s ++ z) F [] []) ctx)
      (some (cfg (Λ := Λ) (some (resultLabel (if (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1.isSome
        then rotationSuccess else rotationFailure))) (reset regs)
        (data rest [] (PositionedRotationMachine.remainingPath (mv.position ++ O) s)
          (F.reverse ++ treeCode ((applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1.getD s) ++ z)
          [] [] []) ctx))
      (2 * mv.position.length + 4 +
        PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length) :=
  machineRepresentedInTime caller initial mv rest O s F z regs ctx

def principalPackageInLinearActualTime (C : Word) (O : List Branch)
    (X F S : Word) (Hd : List Unit) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (cfg (Λ := Λ) (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx)
      (some (runResult (Λ := Λ) regs C O X F S Hd ctx))
      (3 * C.length + 3 * X.length + F.length + S.length + Hd.length + O.length + 3) :=
  machineRunInLinearTime caller initial C O X F S Hd regs ctx

theorem both_actual_package_budgets_retain_their_exact_execution_counts
    (mv : RotationMove) (rest C : Word) (O : List Branch)
    (s : BinaryTree Unit) (X F S z : Word) (Hd : List Unit) :
    (representedPackageInActualTime caller initial regs ctx mv rest O s F z).steps =
        2 * mv.position.length + 4 +
          PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length ∧
      (principalPackageInLinearActualTime caller initial regs ctx C O X F S Hd).steps =
        runSteps C O X F S Hd := ⟨rfl, rfl⟩

theorem actual_package_parser_failure_keeps_the_sharper_initial_cell_bound
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit)
    (failed : (parseMoveRun C).1 = none) (n : Nat) (bound : n ≤ runSteps C O X F S Hd)
    (reached : Cfg Γ Λ R)
    (actual : (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[n]
      (some (cfg (Λ := Λ) (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx)) = some reached) :
    stackCells reached ≤ C.length + O.length + X.length + F.length + S.length +
      Hd.length + contextCells ctx :=
  machine_principal_prefix_space_of_none caller initial C O X F S Hd regs ctx failed n bound reached actual

theorem actual_package_parsed_execution_keeps_the_maximum_of_both_stage_bounds
    (C rest : Word) (mv : RotationMove) (O : List Branch) (X F S : Word) (Hd : List Unit)
    (parsed : (parseMoveRun C).1 = some (mv, rest)) (n : Nat) (bound : n ≤ runSteps C O X F S Hd)
    (reached : Cfg Γ Λ R)
    (actual : (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[n]
      (some (cfg (Λ := Λ) (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx)) = some reached) :
    stackCells reached ≤ max
      (C.length + O.length + X.length + F.length + S.length + Hd.length + contextCells ctx)
      (rest.length + mv.position.length + O.length + 2 * X.length + F.length + S.length +
        Hd.length + contextCells ctx) :=
  machine_principal_prefix_space_of_some caller initial C mv rest O X F S Hd regs ctx parsed n bound reached actual

end ActualPackageRepresentedTiming

section InstalledRepresentedTiming
variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable [DecidableEq K] [DecidableEq K']
variable (caller : External Λ → Statement Γ Λ R)
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
variable (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
variable (installed : ∀ label, Owned (some label) → ambient (labels label) =
  FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

def representedFurtherInstallationInActualTime (mv : RotationMove) (rest : Word)
    (O : List Branch) (s : BinaryTree Unit) (F z : Word) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels
        (cfg (Λ := Λ) (some (moveLabel .start)) regs
          (data (moveCode mv ++ rest) [] O (treeCode s ++ z) F [] []) ctx))
      (some (installedCfg names symbols registers labels
        (cfg (Λ := Λ) (some (resultLabel (if (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1.isSome
          then rotationSuccess else rotationFailure))) (reset regs)
          (data rest [] (PositionedRotationMachine.remainingPath (mv.position ++ O) s)
            (F.reverse ++ treeCode ((applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1.getD s) ++ z)
            [] [] []) ctx)))
      (2 * mv.position.length + 4 +
        PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length) :=
  installed_representedInTime caller names symbols registers labels ambient installed
    mv rest O s F z regs ctx

theorem further_installed_represented_timing_keeps_the_source_and_saved_word_clock
    (mv : RotationMove) (rest : Word) (O : List Branch) (s : BinaryTree Unit) (F z : Word) :
    (representedFurtherInstallationInActualTime caller names symbols registers labels ambient installed
      regs ctx mv rest O s F z).steps =
      2 * mv.position.length + 4 +
        PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length := rfl

end InstalledRepresentedTiming

/- Exact source tariffs and parsed-prefix uniqueness stay separate from machine timing. -/
theorem source_application_cost_uses_the_actual_stopped_cursor_on_failure
    (mv : RotationMove) (O : List Branch) (s : BinaryTree Unit) :
    (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).2 =
      if (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1.isSome then
        3 * PositionedRotationMachine.descentCount (mv.position ++ O) s + 5
      else 2 * PositionedRotationMachine.descentCount (mv.position ++ O) s +
        if PositionedRotationMachine.stoppedPath (mv.position ++ O) s = [] then 3 else 2 :=
  source_application_cost_eq_stopped mv O s

theorem parsed_source_observation_keeps_the_actual_application_failure_tariff
    (C rest : Word) (mv : RotationMove) (O : List Branch) (s : BinaryTree Unit)
    (parsed : (parseMoveRun C).1 = some (mv, rest)) :
    sourceObservationCost C mv O s =
      3 * mv.position.length + 4 + (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).2 :=
  sourceObservationCost_of_parse C mv rest O s parsed

theorem a_certificate_has_one_parsed_move_and_one_unconsumed_certificate_suffix
    (C rest otherRest : Word) (mv other : RotationMove)
    (parsed : (parseMoveRun C).1 = some (mv, rest))
    (alsoParsed : (parseMoveRun C).1 = some (other, otherRest)) :
    mv = other ∧ rest = otherRest := parsed_prefix_unique C mv other rest otherRest parsed alsoParsed

theorem complete_first_success_has_a_unique_parse_and_both_unchanged_literal_suffixes
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (C rest : Word) (O : List Branch) (s t : BinaryTree Unit) (F z outSuffix : Word) (ticks : Nat)
    (first : FirstRun caller
      (cfg (some (moveLabel .start)) regs (data C [] O (treeCode s ++ z) F [] []) ctx) ticks
      (cfg (some (resultLabel rotationSuccess)) (reset regs)
        (data rest [] [] (F.reverse ++ treeCode t ++ outSuffix) [] [] []) ctx)) :
    ∃ mv, (parseMoveRun C).1 = some (mv, rest) ∧
      (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1 = some t ∧ z = outSuffix ∧
      ticks = 2 * mv.position.length + 4 +
        PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length ∧
      ∀ other otherRest, (parseMoveRun C).1 = some (other, otherRest) →
        other = mv ∧ otherRest = rest :=
  represented_raw_first_success_unique caller C rest O s t F z outSuffix regs ctx ticks first.1 first.2.2

end Examples.RotationCertificateMoveApplyMachine
