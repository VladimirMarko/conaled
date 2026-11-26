import Examples.RotationCertificateStreamMachine.Package

/-!
# RotationCertificateStreamMachine: Source
-/

namespace Examples.RotationCertificateStreamMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.StreamMachine

/-! ## Clean raw execution and represented source refinement -/

section CleanActualRuns
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem every_clean_raw_input_has_its_complete_actual_first_run
    (fuel : Bits) (certificate source target : Word) :
    FirstRun (step caller) (entry regs fuel certificate source target ctx)
      (runSteps fuel certificate source target) (runResult regs fuel certificate source target ctx) :=
  run_firstRun caller regs fuel certificate source target ctx

theorem clean_first_run_from_the_complete_evaluation
    (fuel : Bits) (certificate source target : Word) (result : Bool)
    (output : LocalData) (ticks : Nat)
    (evaluated : runEvaluation fuel certificate source target = ⟨result, output, ticks⟩) :
    FirstRun (step caller) (entry regs fuel certificate source target ctx) ticks
      (cfg (some (resultLabel result)) (resetAll regs) output ctx) := by
  change Resources.RotationCertificate.StreamMachine.FirstRun caller _ _ _
  have first := run_firstRun caller regs fuel certificate source target ctx
  simpa only [runSteps, runResult, evaluated, evaluationCfg] using first

theorem eof_uses_the_actual_raw_word_comparison_before_fuel
    (fuel : Bits) (source target : Word) :
    FirstRun (step caller) (entry regs fuel [] source target ctx)
      (TreeEqualityMachine.runSteps source target + 3)
      (cfg (some (resultLabel (decide (source = target)))) (resetAll regs)
        (cleanData fuel [] (source.drop (TreeEqualityMachine.runSteps source target))
          (target.drop (TreeEqualityMachine.runSteps source target))) ctx) :=
  clean_first_run_from_the_complete_evaluation caller regs ctx fuel [] source target _ _ _
    (runEvaluation_nil fuel source target)

theorem failed_fuel_stops_before_parsing_and_preserves_the_literal_certificate
    (fuel : Bits) (certificate source target : Word) (nonempty : certificate ≠ [])
    (failed : (Resources.BinaryCounter.decFixedRun fuel).1 = none) :
    FirstRun (step caller) (entry regs fuel certificate source target ctx)
      (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + 2)
      (cfg (some (resultLabel false)) (resetAll regs)
        (cleanData fuel certificate source target) ctx) :=
  clean_first_run_from_the_complete_evaluation caller regs ctx fuel certificate source target _ _ _
    (runEvaluation_no_fuel fuel certificate source target nonempty failed)

theorem failed_parsing_rolls_back_only_the_current_suffix_after_the_actual_decrement
    (fuel nextFuel : Bits) (certificate source target : Word) (nonempty : certificate ≠ [])
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (failed : (parseMoveRun certificate).1 = none) :
    FirstRun (step caller) (entry regs fuel certificate source target ctx)
      (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
        MoveParserMachine.fullSteps certificate + 4)
      (cfg (some (resultLabel false)) (resetAll regs)
        (cleanData nextFuel certificate source target) ctx) :=
  clean_first_run_from_the_complete_evaluation caller regs ctx fuel certificate source target _ _ _
    (runEvaluation_parse_failure fuel nextFuel certificate source target nonempty decremented failed)

theorem represented_rotation_failure_retains_the_actual_remaining_physical_path
    (fuel nextFuel : Bits) (certificate rest : Word) (move : RotationMove)
    (source target : BinaryTree Unit)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (failed : (applyMoveRun move source).1 = none) :
    FirstRun (step caller) (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
      (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
        MoveApplyMachine.representedSteps move [] source [] + 3)
      (cfg (some (resultLabel false)) (resetAll regs)
        { (cleanData nextFuel rest (treeCode source) (treeCode target)) with
          path := PositionedRotationMachine.remainingPath move.position source } ctx) :=
  clean_first_run_from_the_complete_evaluation caller regs ctx fuel certificate
    (treeCode source) (treeCode target) _ _ _
    (represented_failure_step fuel nextFuel certificate rest move source target decremented parsed failed)

theorem every_represented_boolean_is_exactly_the_existing_source_boolean
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) (result : Bool) :
    FirstResult (step caller) (entry regs fuel certificate (treeCode source) (treeCode target) ctx) result ↔
      (checkStreamRun fuel source target certificate).1 = result :=
  represented_firstResult_iff caller regs fuel certificate source target ctx result

theorem represented_acceptance_recognizes_the_literal_whole_certificate
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) :
    FirstResult (step caller) (entry regs fuel certificate (treeCode source) (treeCode target) ctx) true ↔
      ∃ moves, certificate = certCode moves ∧ Trees.Rotations.applyMoves? moves source = some target ∧
        moves.length ≤ Resources.BinaryCounter.value fuel :=
  represented_accepts_iff caller regs fuel certificate source target ctx

theorem any_represented_first_output_fixes_the_clock_and_every_returned_word
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit)
    (ticks : Nat) (finish : Cfg Γ Λ R)
    (first : FirstRun (step caller)
      (entry regs fuel certificate (treeCode source) (treeCode target) ctx) ticks finish) :
    ticks = runSteps fuel certificate (treeCode source) (treeCode target) ∧
      finish = cfg (some (resultLabel (checkStreamRun fuel source target certificate).1))
        (resetAll regs) (runEvaluation fuel certificate (treeCode source) (treeCode target)).data ctx :=
  represented_complete_first_output caller regs fuel certificate source target ctx ticks finish first

theorem represented_acceptance_reaches_a_live_label_with_the_actual_remaining_fuel
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit)
    (accepted : (checkStreamRun fuel source target certificate).1 = true) :
    ∃ finalFuel,
      FirstRun (step caller) (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
        (runSteps fuel certificate (treeCode source) (treeCode target))
        (cfg (some (resultLabel true)) (resetAll regs) (cleanData finalFuel [] [] []) ctx) ∧
      finalFuel.length = fuel.length :=
  represented_accepting_endpoint caller regs fuel certificate source target ctx accepted

def exactRawTiming (fuel : Bits) (certificate source target : Word) :
    StateTransition.EvalsToInTime (step caller) (entry regs fuel certificate source target ctx)
      (some (runResult regs fuel certificate source target ctx))
      (runSteps fuel certificate source target) :=
  runInTimeExact caller regs fuel certificate source target ctx

def boundedRawTiming (fuel : Bits) (certificate source target : Word) :
    StateTransition.EvalsToInTime (step caller) (entry regs fuel certificate source target ctx)
      (some (runResult regs fuel certificate source target ctx))
      ((2 * fuel.length + 3 * source.length + 7) * certificate.length + source.length + 4) :=
  runInPolynomialTime caller regs fuel certificate source target ctx

def exactRepresentedTiming (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
      (some (runResult regs fuel certificate (treeCode source) (treeCode target) ctx))
      (runSteps fuel certificate (treeCode source) (treeCode target)) :=
  representedInTimeExact caller regs fuel certificate source target ctx

def boundedRepresentedTiming (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
      (some (runResult regs fuel certificate (treeCode source) (treeCode target) ctx))
      ((2 * fuel.length + 6 * source.numNodes + 10) * certificate.length + 2 * source.numNodes + 5) :=
  representedInPolynomialTime caller regs fuel certificate source target ctx

theorem all_typed_clean_time_records_keep_the_actual_step_count
    (fuel : Bits) (certificate source target : Word) :
    (exactRawTiming caller regs ctx fuel certificate source target).steps =
        runSteps fuel certificate source target ∧
      (boundedRawTiming caller regs ctx fuel certificate source target).steps =
        runSteps fuel certificate source target := ⟨rfl, rfl⟩

theorem both_typed_represented_time_records_keep_machine_time
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) :
    (exactRepresentedTiming caller regs ctx fuel certificate source target).steps =
        runSteps fuel certificate (treeCode source) (treeCode target) ∧
      (boundedRepresentedTiming caller regs ctx fuel certificate source target).steps =
        runSteps fuel certificate (treeCode source) (treeCode target) := ⟨rfl, rfl⟩

end CleanActualRuns

/-! The source tariff equations below retain their own measured observations. -/

theorem source_eof_tariff (fuel : Bits) (source target : BinaryTree Unit) :
    sourceObservation fuel source target [] =
      ((eqTreeRun source target).1, (eqTreeRun source target).2 + 1) :=
  sourceObservation_nil fuel source target

theorem source_fuel_failure_tariff (fuel : Bits) (source target : BinaryTree Unit)
    (tag : Tag) (raw : Word) (failed : (Resources.BinaryCounter.decFixedRun fuel).1 = none) :
    sourceObservation fuel source target (tag :: raw) =
      (false, (Resources.BinaryCounter.decFixedRun fuel).2 + 2) :=
  sourceObservation_no_fuel fuel source target tag raw failed

theorem source_parse_failure_tariff (fuel nextFuel : Bits) (source target : BinaryTree Unit)
    (tag : Tag) (raw : Word)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (failed : (parseMoveRun (tag :: raw)).1 = none) :
    sourceObservation fuel source target (tag :: raw) =
      (false, (Resources.BinaryCounter.decFixedRun fuel).2 + (parseMoveRun (tag :: raw)).2 + 2) :=
  sourceObservation_parse_failure fuel nextFuel source target tag raw decremented failed

theorem source_rotation_failure_tariff (fuel nextFuel : Bits) (source target : BinaryTree Unit)
    (certificate rest : Word) (move : RotationMove)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (failed : (applyMoveRun move source).1 = none) :
    sourceObservation fuel source target certificate =
      (false, (Resources.BinaryCounter.decFixedRun fuel).2 + (parseMoveRun certificate).2 +
        (applyMoveRun move source).2 + 2) :=
  sourceObservation_move_failure fuel nextFuel source target certificate rest move decremented parsed failed

theorem source_success_continues_at_the_literal_suffix_and_actual_next_tree
    (fuel nextFuel : Bits) (source nextTree target : BinaryTree Unit)
    (certificate rest : Word) (move : RotationMove)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (executed : (applyMoveRun move source).1 = some nextTree) :
    sourceObservation fuel source target certificate =
      ((sourceObservation nextFuel nextTree target rest).1,
        (Resources.BinaryCounter.decFixedRun fuel).2 + (parseMoveRun certificate).2 +
          (applyMoveRun move source).2 + (sourceObservation nextFuel nextTree target rest).2 + 1) ∧
    (applyMoveRun move source).2 = 3 * move.position.length + 5 ∧
    nextTree.numNodes = source.numNodes :=
  ⟨sourceObservation_step fuel nextFuel source nextTree target certificate rest move decremented parsed executed,
    source_success_application_cost move source nextTree executed,
    applyMoveRun_numNodes move source nextTree executed⟩

theorem the_source_budget_remains_a_distinct_observation_bound
    (fuel : Bits) (source target : BinaryTree Unit) (certificate : Word) :
    (sourceObservation fuel source target certificate).2 ≤
      (3 * fuel.length + 3 * source.numNodes + 12) * certificate.length + 3 * source.numNodes + 6 :=
  sourceObservation_cost_le fuel source target certificate


/-! ## Universal sharp families preserve the independently fixed expectations -/

section UniversalSharpConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)

theorem every_left_malformed_family_has_its_exact_actual_peak
    (rest : Word) (n : Nat) (target : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LeftSharpExpected (step caller) rest n target regs ctx := by
  have actual := left_nodes_run caller rest n target regs ctx
  change LocalRun caller (3 * n + 13) (sharpStart .left rest n target regs ctx)
    (sharpFinish rest n target regs ctx) at actual
  refine ⟨⟨LocalRun.iterate caller actual, not_owned_result false,
    LocalRun.owned_prefix caller actual⟩, ?_, ?_, ?_, ?_⟩
  · exact LocalRun.iterate caller (left_nodes_drop caller rest n target regs ctx)
  · exact left_nodes_drop_rank caller rest n target regs ctx
  · have cells := left_nodes_drop_cells (Λ := Λ) rest n target (resetAll regs) ctx
    change physicalCells (sharpDrop (Λ := Λ) rest n n target regs ctx) =
      2 * n + rest.length + 1 + target.length + externalCells ctx at cells
    omega
  · have peak := left_nodes_peak caller rest n target regs ctx
    change ExactPeak (step caller) (sharpStart .left rest n target regs ctx) (3 * n + 13)
      (max (n + 2) (2 * n) + rest.length + 1 + target.length + externalCells ctx) at peak
    have reorder : rest.length + max (n + 2) (2 * n) + 1 + target.length + externalCells ctx =
        max (n + 2) (2 * n) + rest.length + 1 + target.length + externalCells ctx := by omega
    rw [reorder]
    exact peak

theorem every_right_malformed_family_has_its_exact_actual_peak
    (rest : Word) (m : Nat) (target : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    RightSharpExpected (step caller) rest m target regs ctx := by
  have actual := right_nodes_run caller rest m target regs ctx
  change LocalRun caller (3 * m + 16) (sharpStart .right rest (m + 2) target regs ctx)
    (sharpFinish rest (m + 2) target regs ctx) at actual
  refine ⟨⟨LocalRun.iterate caller actual, not_owned_result false,
    LocalRun.owned_prefix caller actual⟩, ?_, ?_, ?_, ?_⟩
  · exact LocalRun.iterate caller (right_nodes_drop caller rest m target regs ctx)
  · exact right_nodes_drop_rank caller rest m target regs ctx
  · have cells := right_nodes_drop_cells (Λ := Λ) rest m target (resetAll regs) ctx
    change physicalCells (sharpDrop (Λ := Λ) rest (m + 2) (m + 1) target regs ctx) =
      2 * m + 3 + rest.length + 1 + target.length + externalCells ctx at cells
    omega
  · have peak := right_nodes_peak caller rest m target regs ctx
    change ExactPeak (step caller) (sharpStart .right rest (m + 2) target regs ctx) (3 * m + 16)
      (max (m + 4) (2 * m + 3) + rest.length + 1 + target.length + externalCells ctx) at peak
    have reorder : rest.length + max (m + 4) (2 * m + 3) + 1 + target.length + externalCells ctx =
        max (m + 4) (2 * m + 3) + rest.length + 1 + target.length + externalCells ctx := by omega
    rw [reorder]
    exact peak

theorem the_left_zero_case_keeps_its_initial_attained_maximum
    (rest target : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstRun (step caller) (sharpStart .left rest 0 target regs ctx) 13
      (sharpFinish rest 0 target regs ctx) ∧
      ExactPeak (step caller) (sharpStart .left rest 0 target regs ctx) 13
        (rest.length + 3 + target.length + externalCells ctx) := by
  have actual := every_left_malformed_family_has_its_exact_actual_peak caller rest 0 target regs ctx
  exact ⟨actual.1, actual.2.2.2.2⟩

theorem the_right_zero_case_has_a_distinct_clock_and_peak
    (rest target : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstRun (step caller) (sharpStart .right rest 2 target regs ctx) 16
      (sharpFinish rest 2 target regs ctx) ∧
      ExactPeak (step caller) (sharpStart .right rest 2 target regs ctx) 16
        (rest.length + 5 + target.length + externalCells ctx) := by
  have actual := every_right_malformed_family_has_its_exact_actual_peak caller rest 0 target regs ctx
  exact ⟨actual.1, actual.2.2.2.2⟩

end UniversalSharpConnections

theorem all_eighteen_sharp_instances_keep_their_literal_clocks_and_peaks
    (caller : External Unit → Statement IndependentAlphabet Unit Bool)
    (regs : Registers Bool) (c : SharpFixture) (listed : c ∈ sharpCases) :
    c.Expected (step caller) regs := by
  simp only [sharpCases, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 0 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 1 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 2 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 3 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 4 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 5 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 6 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 7 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 8 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 0 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 1 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 2 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 3 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 4 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 5 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 6 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 7 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 8 [15] regs ordinaryContext


end Examples.RotationCertificateStreamMachine
