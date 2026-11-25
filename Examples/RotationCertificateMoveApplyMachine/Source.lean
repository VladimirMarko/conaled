import Examples.RotationCertificateMoveApplyMachine.Boundaries

/-!
# RotationCertificateMoveApplyMachine: Source
-/

namespace Examples.RotationCertificateMoveApplyMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.MoveApplyMachine

section RepresentedAndRawConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem every_clean_raw_parse_returns_the_actual_physical_suffix_and_cleanup
    (mv : RotationMove) (rest X : Word) (O : List Branch) :
    RawExpected caller regs ctx mv rest X O := by
  obtain ⟨r, Y, remaining, actual, length, suffix, failed, succeeded⟩ :=
    run_raw caller mv rest O X regs ctx
  have exactClock := (LocalRun.phaseEndpoint caller (q := MoveApplyMachine.movePhase .start) actual).1
  refine ⟨r, Y, remaining, ?_, length, ?_, failed, succeeded⟩
  · rw [show phaseSteps (movePhase .start) (data (moveCode mv ++ rest) [] O X [] [] []) =
      2 * mv.position.length + 4 +
        PositionedRotationMachine.runSteps mv.direction X (mv.position ++ O) from exactClock]
    exact local_run_gives_an_actual_first_return caller actual (not_owned_result (.inr r))
  · obtain ⟨consumed, same⟩ := suffix
    exact ⟨consumed, same.symm⟩

theorem represented_rotation_preserves_the_complete_saved_word_suffix_and_physical_path
    (mv : RotationMove) (rest : Word) (O : List Branch)
    (s : BinaryTree Unit) (F z : Word) :
    RepresentedExpected caller regs ctx mv rest O s F z := by
  have first := local_run_gives_an_actual_first_return caller
    (run_code_represented_localRun caller mv rest O s F z regs ctx)
    (not_owned_result (representedResult mv O s))
  constructor
  · change FirstRun caller
      (entry regs (moveCode mv ++ rest) O (treeCode s ++ z) F [] [] ctx)
      (representedSteps mv O s F)
      (cfg (some (resultLabel (representedResult mv O s))) (reset regs)
        (representedFinalData mv rest O s F z) ctx)
    exact first
  · exact representedSource_length mv O s F z

theorem all_thirteen_represented_rows_connect_both_clocks_and_complete_physical_endpoints
    (c : RepresentedFixture) (member : c ∈ representedFixtures) (rest F z : Word) :
    c.Expected caller regs ctx rest F z := by
  obtain ⟨sourceRun, clock, remaining, sourceParser, wholeClock⟩ :=
    represented_fixture_source_observations c member
  have actual := (represented_rotation_preserves_the_complete_saved_word_suffix_and_physical_path
    caller regs ctx c.parsed rest c.oldPath c.tree F z).1
  refine ⟨arbitrary_certificate_suffix_has_the_same_source_parse_cost c member rest,
    sourceRun, clock, remaining, ?_⟩
  simpa only [sourceRun, clock, remaining, wholeClock] using actual

theorem represented_first_success_uses_the_parsed_path_before_the_old_path
    (C : Word) (O : List Branch) (s : BinaryTree Unit) (F z : Word) :
    FirstResult caller
      (cfg (some (moveLabel .start)) regs (data C [] O (treeCode s ++ z) F [] []) ctx)
      rotationSuccess ↔
      ∃ mv rest t, (parseMoveRun C).1 = some (mv, rest) ∧
        (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1 = some t := by
  rw [independent_first_result_is_the_public_strict_first_result]
  exact represented_raw_first_success_iff caller C O s F z regs ctx

theorem complete_represented_first_success_recovers_the_actual_parse_output_suffix_and_clock
    (C rest : Word) (O : List Branch) (s t : BinaryTree Unit)
    (F z outSuffix : Word) (ticks : Nat)
    (first : FirstRun caller
      (cfg (some (moveLabel .start)) regs (data C [] O (treeCode s ++ z) F [] []) ctx)
      ticks
      (cfg (some (resultLabel rotationSuccess)) (reset regs)
        (data rest [] [] (F.reverse ++ treeCode t ++ outSuffix) [] [] []) ctx)) :
    ∃ mv, (parseMoveRun C).1 = some (mv, rest) ∧
      (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1 = some t ∧ z = outSuffix ∧
      ticks = 2 * mv.position.length + 4 +
        PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length :=
  represented_raw_first_success_complete caller C rest O s t F z outSuffix regs ctx
    ticks first.1 first.2.2

theorem exact_success_endpoint_iff_includes_a_success_label_and_both_literal_suffixes
    (mv : RotationMove) (rest outRest : Word) (O : List Branch)
    (s t : BinaryTree Unit) (F z outSuffix : Word) (ticks : Nat) :
    FirstRun caller
      (cfg (some (moveLabel .start)) regs
        (data (moveCode mv ++ rest) [] O (treeCode s ++ z) F [] []) ctx)
      ticks
      (cfg (some (resultLabel rotationSuccess)) (reset regs)
        (data outRest [] [] (F.reverse ++ treeCode t ++ outSuffix) [] [] []) ctx) ↔
      (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1 = some t ∧
        rest = outRest ∧ z = outSuffix ∧
        ticks = 2 * mv.position.length + 4 +
          PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length := by
  constructor
  · intro first
    exact (represented_success_localRun_iff caller mv rest outRest O s t F z outSuffix
      regs ctx ticks).mp (LocalRun.of_iterate caller first.1 first.2.2)
  · intro successful
    exact local_run_gives_an_actual_first_return caller
      ((represented_success_localRun_iff caller mv rest outRest O s t F z outSuffix
        regs ctx ticks).mpr successful) (not_owned_result rotationSuccess)

include caller in
theorem first_success_also_has_the_source_rotation_node_count_and_source_tariff
    (mv : RotationMove) (rest : Word) (O : List Branch) (s t : BinaryTree Unit)
    (F z : Word)
    (endpoint : runResult (Λ := Λ) regs (moveCode mv ++ rest) O (treeCode s ++ z) F [] [] ctx =
      cfg (some (resultLabel rotationSuccess)) (reset regs)
        (data rest [] [] (F.reverse ++ treeCode t ++ z) [] [] []) ctx) :
    Trees.Rotations.applyMove? ⟨mv.direction, mv.position ++ O⟩ s = some t ∧
      t.numNodes = s.numNodes ∧
      (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).2 =
        3 * (mv.position ++ O).length + 5 ∧
      (F.reverse ++ treeCode t ++ z).length = F.length + 2 * s.numNodes + 1 + z.length :=
  represented_success_semantics caller mv rest O s t F z regs ctx endpoint

theorem both_raw_root_success_characterizations_keep_arbitrary_registers_context_and_saved_words
    (rest X F : Word) : RootIffExpected caller regs ctx rest X F := by
  constructor
  · rw [independent_first_result_is_the_public_strict_first_result]
    simpa only [moveCode, directionTag, pathTags, List.map_nil, List.nil_append,
      List.append_assoc, List.cons_append, List.append_nil, nodeTag, rotateLeftTag, endMoveTag,
      rotationSuccess, MoveApplyMachine.success, entry, entryData, data] using
      root_left_first_success_iff caller X F rest regs ctx
  · rw [independent_first_result_is_the_public_strict_first_result]
    simpa only [moveCode, directionTag, pathTags, List.map_nil, List.nil_append,
      List.cons_append, List.append_nil, nodeTag, rotateRightTag, endMoveTag,
      rotationSuccess, MoveApplyMachine.success, entry, entryData, data] using
      root_right_first_success_iff caller X F rest regs ctx

theorem both_raw_root_patterns_return_the_literal_output_at_the_exact_first_clock
    (rest F z : Word) (A : BinaryTree Unit) :
    RootPatternsExpected caller regs ctx rest F z A := by
  constructor
  · have first := local_run_gives_an_actual_first_return caller
      (root_left_pattern_localRun caller A z F rest regs ctx)
      (not_owned_result MoveApplyMachine.success)
    simpa only [moveCode, directionTag, pathTags, List.map_nil, List.nil_append,
      List.append_assoc, List.cons_append, List.append_nil, nodeTag, rotateLeftTag, endMoveTag,
      rotationSuccess, MoveApplyMachine.success, entry, entryData, data] using first
  · have first := local_run_gives_an_actual_first_return caller
      (root_right_pattern_localRun caller A z F rest regs ctx)
      (not_owned_result MoveApplyMachine.success)
    simpa only [moveCode, directionTag, pathTags, List.map_nil, List.nil_append,
      List.append_assoc, List.cons_append, List.append_nil, nodeTag, rotateRightTag, endMoveTag,
      rotationSuccess, MoveApplyMachine.success, entry, entryData, data] using first

def representedInActualTime (mv : RotationMove) (rest : Word) (O : List Branch)
    (s : BinaryTree Unit) (F z : Word) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (moveLabel .start)) regs
        (data (moveCode mv ++ rest) [] O (treeCode s ++ z) F [] []) ctx)
      (some (cfg (some (resultLabel (if (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1.isSome
        then rotationSuccess else rotationFailure))) (reset regs)
        (data rest [] (PositionedRotationMachine.remainingPath (mv.position ++ O) s)
          (F.reverse ++ treeCode ((applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1.getD s) ++ z)
          [] [] []) ctx))
      (2 * mv.position.length + 4 +
        PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length) :=
  representedInTime caller mv rest O s F z regs ctx

theorem represented_typed_time_retains_the_actual_saved_word_cost
    (mv : RotationMove) (rest : Word) (O : List Branch) (s : BinaryTree Unit) (F z : Word) :
    (representedInActualTime caller regs ctx mv rest O s F z).steps =
      2 * mv.position.length + 4 +
        PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length := rfl

def principalInLinearActualTime (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx)
      (some (runResult regs C O X F S Hd ctx))
      (3 * C.length + 3 * X.length + F.length + S.length + Hd.length + O.length + 3) :=
  runInLinearTime caller C O X F S Hd regs ctx

def parsedInSharperLinearActualTime (C rest : Word) (mv : RotationMove)
    (O : List Branch) (X F S : Word) (Hd : List Unit)
    (parsed : (parseMoveRun C).1 = some (mv, rest)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx)
      (some (runResult regs C O X F S Hd ctx))
      (3 * X.length + F.length + S.length + Hd.length + 3 * mv.position.length + O.length + 9) :=
  parsedRunInLinearTime caller C mv rest O X F S Hd regs ctx parsed

theorem linear_bounds_keep_the_actual_untruncated_count
    (C rest : Word) (mv : RotationMove) (O : List Branch) (X F S : Word) (Hd : List Unit)
    (parsed : (parseMoveRun C).1 = some (mv, rest)) :
    (principalInLinearActualTime caller regs ctx C O X F S Hd).steps = runSteps C O X F S Hd ∧
      (parsedInSharperLinearActualTime caller regs ctx C rest mv O X F S Hd parsed).steps =
        runSteps C O X F S Hd := ⟨rfl, rfl⟩

section Physical
variable [Fintype K]

theorem every_principal_prefix_keeps_every_dirty_cell_in_its_bound
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) (n : Nat)
    (bound : n ≤ runSteps C O X F S Hd) (reached : Cfg Γ Λ R)
    (executed : Runs caller (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) n reached) :
    stackCells reached ≤ C.length + O.length + 2 * X.length + F.length + S.length +
      Hd.length + contextCells ctx := by
  have cells := prefix_stackCells_le caller C O X F S Hd regs ctx n bound reached executed
  unfold principalCells at cells
  omega

theorem parse_failure_has_the_stronger_initial_physical_sum_bound
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit)
    (failed : (parseMoveRun C).1 = none) (n : Nat)
    (bound : n ≤ runSteps C O X F S Hd) (reached : Cfg Γ Λ R)
    (executed : Runs caller (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) n reached) :
    stackCells reached ≤ C.length + O.length + X.length + F.length + S.length +
      Hd.length + contextCells ctx :=
  prefix_stackCells_le_of_none caller C O X F S Hd regs ctx failed n bound reached executed

theorem parsed_success_uses_the_larger_of_the_actual_parser_and_position_bounds
    (C rest : Word) (mv : RotationMove) (O : List Branch) (X F S : Word) (Hd : List Unit)
    (parsed : (parseMoveRun C).1 = some (mv, rest)) (n : Nat)
    (bound : n ≤ runSteps C O X F S Hd) (reached : Cfg Γ Λ R)
    (executed : Runs caller (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) n reached) :
    stackCells reached ≤ max
      (C.length + O.length + X.length + F.length + S.length + Hd.length + contextCells ctx)
      (rest.length + mv.position.length + O.length + 2 * X.length + F.length + S.length +
        Hd.length + contextCells ctx) :=
  prefix_stackCells_le_of_some caller C mv rest O X F S Hd regs ctx parsed n bound reached executed

omit [DecidableEq K] in
theorem the_sharper_position_bound_is_exactly_two_below_initial_potential
    (C rest : Word) (mv : RotationMove) (O : List Branch) (X F S : Word) (Hd : List Unit)
    (parsed : (parseMoveRun C).1 = some (mv, rest)) :
    rest.length + mv.position.length + O.length + 2 * X.length + F.length + S.length +
      Hd.length + contextCells ctx + 2 =
      potential (cfg (Λ := Λ) (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) := by
  have length := parseMoveRun_consumed_length C mv rest parsed
  rw [show potential (cfg (Λ := Λ) (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) =
    principalCells C O X F S Hd ctx + X.length from entry_potential (Λ := Λ) C O X F S Hd regs ctx]
  unfold principalCells
  omega

end Physical
end RepresentedAndRawConnections

theorem all_thirteen_rows_keep_the_author_and_independent_protected_words
    (author : AuthorCaller) (independent : ExampleCaller) (flag : Bool)
    (c : RepresentedFixture) (member : c ∈ representedFixtures) (rest F z : Word) :
    c.Expected author (stale flag) authorContext rest F z ∧
      c.Expected independent (stale flag) independentContext rest F z :=
  ⟨all_thirteen_represented_rows_connect_both_clocks_and_complete_physical_endpoints
      author (stale flag) authorContext c member rest F z,
    all_thirteen_represented_rows_connect_both_clocks_and_complete_physical_endpoints
      independent (stale flag) independentContext c member rest F z⟩

/- Actual caller continuations begin after the fixed first live result. -/
section RootSegments
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem root_left_segment_with_arbitrary_certificate_suffix (rest : Word) :
    LocalRun caller 11
      (cfg (some (moveLabel .start)) regs (data ([6,10] ++ rest) [] [] (treeCode rightTwo) [] [] []) ctx)
      (cfg (some (resultLabel rotationSuccess)) (reset regs)
        (data rest [] [] (treeCode leftTwo) [] [] []) ctx) := by
  have actual := root_left_pattern_localRun caller nilTree [0,0] [] rest regs ctx
  exact actual

theorem root_right_segment_with_arbitrary_certificate_suffix (rest : Word) :
    LocalRun caller 10
      (cfg (some (moveLabel .start)) regs (data ([7,10] ++ rest) [] [] (treeCode leftTwo) [] [] []) ctx)
      (cfg (some (resultLabel rotationSuccess)) (reset regs)
        (data rest [] [] (treeCode rightTwo) [] [] []) ctx) := by
  have actual := root_right_pattern_localRun caller nilTree [0,0] [] rest regs ctx
  exact actual

theorem root_left_first_live_result_is_exactly_eleven (rest : Word) :
    FirstRun caller
      (cfg (some (moveLabel .start)) regs (data ([6,10] ++ rest) [] [] (treeCode rightTwo) [] [] []) ctx)
      11
      (cfg (some (resultLabel rotationSuccess)) (reset regs)
        (data rest [] [] (treeCode leftTwo) [] [] []) ctx) :=
  local_run_gives_an_actual_first_return caller
    (root_left_segment_with_arbitrary_certificate_suffix caller regs ctx rest)
    (not_owned_result rotationSuccess)

end RootSegments

def authorRootStart (flag : Bool) : AuthorCfg :=
  cfg (some (moveLabel .start)) (stale flag) (data [6,10] [] [] (treeCode rightTwo) [] [] []) authorContext

def authorRootLive (flag : Bool) : AuthorCfg :=
  cfg (some (resultLabel rotationSuccess)) (clean flag) (data [] [] [] (treeCode leftTwo) [] [] []) authorContext

def authorRootHalt (marker : Tag) (flag : Bool) : AuthorCfg :=
  cfg none (clean flag) (data [] [] [] (treeCode leftTwo) [] [] [])
    (authorWords (marker :: [15,2,7,10,3]) [(),()])

theorem sentinel_caller_has_live_eleven_present_halt_twelve_and_outer_none_thirteen
    (marker : Tag) (flag : Bool) :
    FirstRun (sentinelHaltCaller marker) (authorRootStart flag) 11 (authorRootLive flag) ∧
      Runs (sentinelHaltCaller marker) (authorRootStart flag) 12 (authorRootHalt marker flag) ∧
      (next (sentinelHaltCaller marker))^[13] (some (authorRootStart flag)) = none := by
  have first := root_left_first_live_result_is_exactly_eleven
    (sentinelHaltCaller marker) (stale flag) authorContext []
  have pushed := sentinel_push_and_halt_are_one_actual_activation marker rotationSuccess
    (clean flag) (data [] [] [] (treeCode leftTwo) [] [] []) [15,2,7,10,3] [(),()]
  have atTwelve := append_actual_step (sentinelHaltCaller marker) (authorRootStart flag)
    (authorRootLive flag) 11 first.1 (some (authorRootHalt marker flag)) pushed
  refine ⟨first, atTwelve, ?_⟩
  exact append_actual_step (sentinelHaltCaller marker) (authorRootStart flag)
    (authorRootHalt marker flag) 12 atTwelve none rfl

def sentinelCallerInActualTime (marker : Tag) (flag : Bool) :
    StateTransition.EvalsToInTime (step (sentinelHaltCaller marker))
      (authorRootStart flag) (some (authorRootHalt marker flag)) 12 :=
  appendTimed (sentinelHaltCaller marker) (authorRootStart flag) (authorRootLive flag)
    (some (authorRootHalt marker flag)) 11 1
    (localRunInActualTime (sentinelHaltCaller marker)
      (root_left_segment_with_arbitrary_certificate_suffix
        (sentinelHaltCaller marker) (stale flag) authorContext []))
    (oneActualStepTime (sentinelHaltCaller marker) (authorRootLive flag)
      (some (authorRootHalt marker flag))
      (sentinel_push_and_halt_are_one_actual_activation marker rotationSuccess
        (clean flag) (data [] [] [] (treeCode leftTwo) [] [] []) [15,2,7,10,3] [(),()]))

theorem sentinel_timing_contains_both_actual_segments (marker : Tag) (flag : Bool) :
    (sentinelCallerInActualTime marker flag).steps = 12 := rfl

def emptyAllocationStart (flag : Bool) : ExampleCfg :=
  cfg (some (moveLabel .start)) (stale flag) (data [] [] [] [] [] [] []) independentContext

def emptyAllocationLive (flag : Bool) : ExampleCfg :=
  cfg (some (resultLabel parseFailure)) (clean flag) (data [] [] [] [] [] [] []) independentContext

def emptyAllocationCaller (flag : Bool) : ExampleCfg :=
  cfg (some (callerLabel ())) ((clean flag).1, !flag) (data [] [] [] [] [] [] [])
    (independentWords [true,true,false,true] [11,15])

theorem empty_allocation_first_result_is_two_then_the_caller_escapes_the_initial_potential
    (flag : Bool) :
    FirstRun allocatingCaller (emptyAllocationStart flag) 2 (emptyAllocationLive flag) ∧
      Runs allocatingCaller (emptyAllocationStart flag) 3 (emptyAllocationCaller flag) ∧
      potential (emptyAllocationStart flag) = 5 ∧
      stackCells (emptyAllocationCaller flag) = 6 ∧
      potential (emptyAllocationStart flag) < stackCells (emptyAllocationCaller flag) := by
  have first : FirstRun allocatingCaller (emptyAllocationStart flag) 2 (emptyAllocationLive flag) :=
    local_run_gives_an_actual_first_return allocatingCaller
      (run_of_none_localRun allocatingCaller [] [] [] [] [] [] (stale flag) independentContext rfl)
      (not_owned_result parseFailure)
  have pushed := allocating_caller_changes_the_actual_protected_data_and_caller_register
    parseFailure (clean flag) (data [] [] [] [] [] [] []) [true,false,true] [11,15]
  have actual := append_actual_step allocatingCaller (emptyAllocationStart flag)
    (emptyAllocationLive flag) 2 first.1 (some (emptyAllocationCaller flag)) pushed
  have initial : potential (emptyAllocationStart flag) = 5 := by
    change potential (cfg (some (phaseLabel (movePhase .start))) (stale flag)
      (data [] [] [] [] [] [] []) independentContext) = _
    rw [potential_phase_cfg, the_two_actual_protected_contexts_have_seven_and_five_cells.2]
    rfl
  have later : stackCells (emptyAllocationCaller flag) = 6 := by
    rw [emptyAllocationCaller, stackCells_cfg]
    simp only [localCells, data, contextCells, Fin.sum_univ_two]
    rfl
  exact ⟨first, actual, initial, later, by omega⟩

def misleadingStart (flag : Bool) : ExampleCfg :=
  cfg (some (moveLabel .start)) (stale flag) (failureData [6,8,9] []) independentContext

def misleadingLive (flag : Bool) : ExampleCfg :=
  cfg (some (resultLabel parseFailure)) (clean flag) (failureData [6,8,9] []) independentContext

def misleadingLater (flag : Bool) : ExampleCfg :=
  cfg (some (resultLabel rotationSuccess)) (clean flag) (failureData [6,8,9] []) independentContext

theorem a_later_success_label_does_not_change_the_first_parse_failure (flag : Bool) :
    FirstRun misleadingCaller (misleadingStart flag) 8 (misleadingLive flag) ∧
      Runs misleadingCaller (misleadingStart flag) 9 (misleadingLater flag) ∧
      ¬ FirstResult misleadingCaller (misleadingStart flag) rotationSuccess := by
  have first : FirstRun misleadingCaller (misleadingStart flag) 8 (misleadingLive flag) :=
    local_run_gives_an_actual_first_return misleadingCaller
      (run_of_none_localRun misleadingCaller [6,8,9] [.right,.left] [1,15] [12,3] [14]
        [(),()] (stale flag) independentContext rfl) (not_owned_result parseFailure)
  refine ⟨first, ?_, ?_⟩
  · exact append_actual_step misleadingCaller (misleadingStart flag) (misleadingLive flag)
      8 first.1 (some (misleadingLater flag))
      (misleading_success_is_a_later_paid_caller_step (clean flag)
        (failureData [6,8,9] []) independentContext)
  · rintro ⟨n, reached, purported, label⟩
    have same := firstRun_unique misleadingCaller (misleadingStart flag) reached
      (misleadingLive flag) n 8 purported first
    rw [same.2] at label
    cases label

def reentryStart (flag : Bool) : ExampleCfg :=
  cfg (some (moveLabel .start)) (stale flag)
    (data [6,10,7,10] [] [] (treeCode rightTwo) [] [] []) independentContext

def reentryMiddle (flag : Bool) : ExampleCfg :=
  cfg (some (resultLabel rotationSuccess)) (clean flag)
    (data [7,10] [] [] (treeCode leftTwo) [] [] []) independentContext

def reentryJoined (flag : Bool) : ExampleCfg :=
  cfg (some (moveLabel .start)) (clean flag)
    (data [7,10] [] [] (treeCode leftTwo) [] [] []) independentContext

def reentryFinish (flag : Bool) : ExampleCfg :=
  cfg (some (resultLabel rotationSuccess)) (clean flag)
    (data [] [] [] (treeCode rightTwo) [] [] []) independentContext

theorem actual_reentry_is_eleven_then_one_then_ten_and_not_one_first_return (flag : Bool) :
    FirstRun reentryCaller (reentryStart flag) 11 (reentryMiddle flag) ∧
      Runs reentryCaller (reentryStart flag) 12 (reentryJoined flag) ∧
      Runs reentryCaller (reentryStart flag) 22 (reentryFinish flag) ∧
      ¬ FirstRun reentryCaller (reentryStart flag) 22 (reentryFinish flag) := by
  have first := root_left_first_live_result_is_exactly_eleven
    reentryCaller (stale flag) independentContext [7,10]
  have joined := append_actual_step reentryCaller (reentryStart flag) (reentryMiddle flag)
    11 first.1 (some (reentryJoined flag))
    (reentry_jump_preserves_every_actual_store (clean flag)
      (data [7,10] [] [] (treeCode leftTwo) [] [] []) independentContext)
  have inverse := LocalRun.iterate reentryCaller
    (root_right_segment_with_arbitrary_certificate_suffix reentryCaller (clean flag) independentContext [])
  have completed := runs_trans reentryCaller (reentryStart flag) (reentryJoined flag)
    (reentryFinish flag) 12 10 joined inverse
  refine ⟨first, joined, completed, ?_⟩
  intro purported
  have impossible := (firstRun_unique reentryCaller (reentryStart flag) (reentryMiddle flag)
    (reentryFinish flag) 11 22 first purported).1
  omega

def reentryFirstAndJumpInActualTime (flag : Bool) :
    StateTransition.EvalsToInTime (step reentryCaller)
      (reentryStart flag) (some (reentryJoined flag)) 12 :=
  appendTimed reentryCaller (reentryStart flag) (reentryMiddle flag) (some (reentryJoined flag)) 11 1
    (localRunInActualTime reentryCaller
      (root_left_segment_with_arbitrary_certificate_suffix reentryCaller (stale flag) independentContext [7,10]))
    (oneActualStepTime reentryCaller (reentryMiddle flag) (some (reentryJoined flag))
      (reentry_jump_preserves_every_actual_store (clean flag)
        (data [7,10] [] [] (treeCode leftTwo) [] [] []) independentContext))

def reentryInActualTime (flag : Bool) :
    StateTransition.EvalsToInTime (step reentryCaller)
      (reentryStart flag) (some (reentryFinish flag)) 22 :=
  appendTimed reentryCaller (reentryStart flag) (reentryJoined flag) (some (reentryFinish flag)) 12 10
    (reentryFirstAndJumpInActualTime flag)
    (localRunInActualTime reentryCaller
      (root_right_segment_with_arbitrary_certificate_suffix reentryCaller (clean flag) independentContext []))

theorem reentry_timed_data_keeps_the_paid_caller_jump (flag : Bool) :
    (reentryInActualTime flag).steps = 22 := rfl

section SharpFamilyConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem exact_peak_of_the_universal_actual_bound_and_an_attained_prefix
    (start : Cfg Γ Λ R) (ticks peak : Nat) (clock : remainingSteps start = ticks)
    (upper : ∀ j, j ≤ ticks → ∀ reached, Runs caller start j reached → stackCells reached ≤ peak)
    (attained : ∃ j reached, j ≤ ticks ∧ Runs caller start j reached ∧ stackCells reached = peak) :
    HasExactPeak caller start ticks peak := by
  constructor
  · intro j bound
    obtain ⟨reached, actual, _, _, _⟩ := owned_prefix caller start j (by omega)
    exact ⟨reached, actual, upper j bound reached actual⟩
  · obtain ⟨j, reached, bound, actual, cells⟩ := attained
    exact ⟨j, bound, reached, actual, cells⟩

theorem all_left_node_families_have_the_fixed_run_drop_rank_and_exact_peak
    (n : Nat) (rest : Word) : LeftNodesExpected caller regs ctx n rest := by
  have peak := left_nodes_peak caller rest n regs ctx
  refine ⟨local_run_gives_an_actual_first_return caller
    (left_nodes_run caller rest n regs ctx) (not_owned_result rotationFailure),
    LocalRun.iterate caller (left_nodes_drop caller rest n regs ctx),
    left_nodes_drop_rank caller rest n regs ctx, ?_, ?_⟩
  · simpa only [data, Nat.add_comm rest.length] using
      left_nodes_drop_cells (Λ := Λ) rest n (reset regs) ctx
  · exact exact_peak_of_the_universal_actual_bound_and_an_attained_prefix caller _ _ _
      (left_nodes_exact_clock caller rest n regs ctx) peak.1 peak.2

theorem all_right_node_families_have_the_fixed_run_drop_rank_and_exact_peak
    (m : Nat) (rest : Word) : RightNodesExpected caller regs ctx m rest := by
  have peak := right_nodes_peak caller rest m regs ctx
  refine ⟨local_run_gives_an_actual_first_return caller
    (right_nodes_run caller rest m regs ctx) (not_owned_result rotationFailure),
    LocalRun.iterate caller (right_nodes_drop caller rest m regs ctx),
    right_nodes_drop_rank caller rest m regs ctx, ?_, ?_⟩
  · have cells := right_nodes_drop_cells (Λ := Λ) rest m (reset regs) ctx
    change stackCells (cfg (some (positionLabel .dropPending)) (reset regs)
      (data rest [] [] (List.replicate (m + 2) nodeTag) [] [] (List.replicate (m + 1) ())) ctx) = _
    unfold data
    omega
  · exact exact_peak_of_the_universal_actual_bound_and_an_attained_prefix caller _ _ _
      (right_nodes_exact_clock caller rest m regs ctx) peak.1 peak.2

theorem every_unterminated_parser_family_restores_all_dirty_tree_and_path_stores
    (k : Nat) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    ParserNodesExpected caller regs ctx k O X F S Hd := by
  have peak := parser_eof_peak caller k O X F S Hd regs ctx
  constructor
  · exact local_run_gives_an_actual_first_return caller
      (parser_eof_run caller k O X F S Hd regs ctx) (not_owned_result parseFailure)
  · apply exact_peak_of_the_universal_actual_bound_and_an_attained_prefix caller _ _ _
      (show remainingSteps (entry (Λ := Λ) regs (rotateLeftTag :: List.replicate k pathLeftTag)
        O X F S Hd ctx) = 2 * k + 4 from
        parser_eof_exact_clock caller k O X F S Hd regs ctx)
    · simpa only [Runs, entry, entryData, data, rotateLeftTag, List.cons_append,
        List.nil_append, List.length_cons, List.length_replicate] using peak.1
    · simpa only [Runs, entry, entryData, data, rotateLeftTag, List.cons_append,
        List.nil_append, List.length_cons, List.length_replicate] using peak.2

end SharpFamilyConnections

theorem zero_one_two_left_and_zero_right_keep_the_small_input_peak_exceptions
    (caller : ExampleCaller) (flag : Bool) :
    LeftNodesExpected caller (stale flag) independentContext 0 [] ∧
      LeftNodesExpected caller (stale flag) independentContext 1 [] ∧
      LeftNodesExpected caller (stale flag) independentContext 2 [] ∧
      RightNodesExpected caller (stale flag) independentContext 0 [] ∧
      max (0 + 2) (2 * 0) + 5 = 7 ∧
      max (1 + 2) (2 * 1) + 5 = 8 ∧
      max (2 + 2) (2 * 2) + 5 = 9 ∧
      max (0 + 4) (2 * 0 + 3) + 5 = 9 :=
  ⟨all_left_node_families_have_the_fixed_run_drop_rank_and_exact_peak caller (stale flag) independentContext 0 [],
    all_left_node_families_have_the_fixed_run_drop_rank_and_exact_peak caller (stale flag) independentContext 1 [],
    all_left_node_families_have_the_fixed_run_drop_rank_and_exact_peak caller (stale flag) independentContext 2 [],
    all_right_node_families_have_the_fixed_run_drop_rank_and_exact_peak caller (stale flag) independentContext 0 [],
    rfl, rfl, rfl, rfl⟩

theorem every_sharp_family_also_keeps_the_author_context
    (caller : AuthorCaller) (flag : Bool) (n m k : Nat) (rest : Word) :
    LeftNodesExpected caller (stale flag) authorContext n rest ∧
      RightNodesExpected caller (stale flag) authorContext m rest ∧
      ParserNodesExpected caller (stale flag) authorContext k [.right,.left]
        [1,15] [12,3] [14] [(),()] :=
  ⟨all_left_node_families_have_the_fixed_run_drop_rank_and_exact_peak caller (stale flag) authorContext n rest,
    all_right_node_families_have_the_fixed_run_drop_rank_and_exact_peak caller (stale flag) authorContext m rest,
    every_unterminated_parser_family_restores_all_dirty_tree_and_path_stores
      caller (stale flag) authorContext k [.right,.left] [1,15] [12,3] [14] [(),()]⟩

section PhysicalSeparators
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem undo_empty_adds_one_real_cell_while_spending_one_unit_of_debt
    (d : RotationDirection) (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    let before := cfg (some (moveLabel (.undo d))) regs (data C [] O X F S Hd) ctx
    let after := cfg (some (dispatchLabel .failure)) (resetMove regs)
      (data (directionTag d :: C) [] O X F S Hd) ctx
    step caller before = some after ∧ stackCells after = stackCells before + 1 ∧
      debt before.l = 1 ∧ debt after.l = 0 ∧ potential after = potential before := by
  refine ⟨move_undo_empty_actual caller d C O X F S Hd regs ctx, ?_, rfl, rfl, ?_⟩
  · rw [stackCells_cfg, stackCells_cfg]
    simp only [localCells, data, List.length_nil, List.length_cons]
    omega
  · change potential (cfg (Λ := Λ) (some (phaseLabel (MoveApplyMachine.dispatchPhase .failure)))
      (resetMove regs) (data (directionTag d :: C) [] O X F S Hd) ctx) =
      potential (cfg (Λ := Λ) (some (phaseLabel (MoveApplyMachine.movePhase (.undo d))))
        regs (data C [] O X F S Hd) ctx)
    rw [potential_phase_cfg, potential_phase_cfg]
    simp only [phaseDebt, phaseCredit, MoveApplyMachine.movePhase,
      MoveApplyMachine.dispatchPhase, MoveParserMachine.phaseDebt, localCells, data,
      List.length_nil, List.length_cons]
    omega

theorem position_scanner_can_add_a_pending_cell_using_source_credit
    (rest : Word) :
    let before := cfg (some (positionLabel (.scanScratch .left))) regs
      (data rest [] [] [1] [] [] [()]) ctx
    let after := cfg (some (positionLabel (.scanScratch .left))) (reset regs)
      (data rest [] [] [] [] [1] [(),()]) ctx
    step caller before = some after ∧ stackCells after = stackCells before + 1 ∧
      credit before = 1 ∧ credit after = 0 ∧ potential after = potential before := by
  refine ⟨?_, ?_, rfl, rfl, ?_⟩
  · exact position_advance_step caller (.scanScratch .left)
      (data rest [] [] [1] [] [] [()]) regs ctx
  · rw [stackCells_cfg, stackCells_cfg]
    simp only [localCells, data, List.length_nil, List.length_cons]
    omega
  · change potential (cfg (Λ := Λ) (some (phaseLabel (MoveApplyMachine.positionPhase (.scanScratch .left))))
      (reset regs) (data rest [] [] [] [] [1] [(),()]) ctx) =
      potential (cfg (Λ := Λ) (some (phaseLabel (MoveApplyMachine.positionPhase (.scanScratch .left))))
        regs (data rest [] [] [1] [] [] [()]) ctx)
    rw [potential_phase_cfg, potential_phase_cfg]
    simp only [phaseDebt, phaseCredit, MoveApplyMachine.positionPhase,
      PositionedRotationMachine.phaseDebt, PositionedRotationMachine.phaseCredit,
      positionData, localCells, data, List.length_nil, List.length_cons]

end PhysicalSeparators

/- The actual bundled finite machine and its genuine one-input initializer. -/
def independentPackage (caller : ExampleCaller) (initial : Bool) : Turing.FinTM2 :=
  machine caller initial

def authorPackage (caller : AuthorCaller) (initial : Bool) : Turing.FinTM2 :=
  machine caller initial

def twoLabelPackage
    (caller : External (Fin 2) → Statement IndependentAlphabet (Fin 2) Bool)
    (initial : Bool) : Turing.FinTM2 := machine caller initial

theorem actual_unit_and_two_label_packages_have_nine_stacks_and_two_hundred_four_registers
    (caller : ExampleCaller)
    (twoCaller : External (Fin 2) → Statement IndependentAlphabet (Fin 2) Bool) (initial : Bool) :
    @Fintype.card (independentPackage caller initial).K (independentPackage caller initial).kFin = 9 ∧
      @Fintype.card (independentPackage caller initial).Λ (independentPackage caller initial).ΛFin = 30 ∧
      @Fintype.card (independentPackage caller initial).σ (independentPackage caller initial).σFin = 204 ∧
      @Fintype.card (twoLabelPackage twoCaller initial).K (twoLabelPackage twoCaller initial).kFin = 9 ∧
      @Fintype.card (twoLabelPackage twoCaller initial).Λ (twoLabelPackage twoCaller initial).ΛFin = 31 ∧
      @Fintype.card (twoLabelPackage twoCaller initial).σ (twoLabelPackage twoCaller initial).σFin = 204 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      @Fintype.card (independentPackage caller initial).K (independentPackage caller initial).kFin =
          Fintype.card (StackId (Fin 2)) :=
        @Fintype.card_congr (independentPackage caller initial).K (StackId (Fin 2))
          (independentPackage caller initial).kFin inferInstance (Equiv.refl _)
      _ = 9 := by simpa using card_stackId (K := Fin 2)
  · calc
      @Fintype.card (independentPackage caller initial).Λ (independentPackage caller initial).ΛFin =
          Fintype.card (Label Unit) :=
        @Fintype.card_congr (independentPackage caller initial).Λ (Label Unit)
          (independentPackage caller initial).ΛFin inferInstance (Equiv.refl _)
      _ = 30 := by simpa using card_label (Λ := Unit)
  · calc
      @Fintype.card (independentPackage caller initial).σ (independentPackage caller initial).σFin =
          Fintype.card (Registers Bool) :=
        @Fintype.card_congr (independentPackage caller initial).σ (Registers Bool)
          (independentPackage caller initial).σFin inferInstance (Equiv.refl _)
      _ = 204 := by simpa using card_registers (R := Bool)
  · calc
      @Fintype.card (twoLabelPackage twoCaller initial).K (twoLabelPackage twoCaller initial).kFin =
          Fintype.card (StackId (Fin 2)) :=
        @Fintype.card_congr (twoLabelPackage twoCaller initial).K (StackId (Fin 2))
          (twoLabelPackage twoCaller initial).kFin inferInstance (Equiv.refl _)
      _ = 9 := by simpa using card_stackId (K := Fin 2)
  · calc
      @Fintype.card (twoLabelPackage twoCaller initial).Λ (twoLabelPackage twoCaller initial).ΛFin =
          Fintype.card (Label (Fin 2)) :=
        @Fintype.card_congr (twoLabelPackage twoCaller initial).Λ (Label (Fin 2))
          (twoLabelPackage twoCaller initial).ΛFin inferInstance (Equiv.refl _)
      _ = 31 := by simpa using card_label (Λ := Fin 2)
  · calc
      @Fintype.card (twoLabelPackage twoCaller initial).σ (twoLabelPackage twoCaller initial).σFin =
          Fintype.card (Registers Bool) :=
        @Fintype.card_congr (twoLabelPackage twoCaller initial).σ (Registers Bool)
          (twoLabelPackage twoCaller initial).σFin inferInstance (Equiv.refl _)
      _ = 204 := by simpa using card_registers (R := Bool)

theorem every_alphabet_in_each_actual_package_is_finite
    (caller : ExampleCaller) (author : AuthorCaller)
    (twoCaller : External (Fin 2) → Statement IndependentAlphabet (Fin 2) Bool) (initial : Bool) :
    (∀ k : (independentPackage caller initial).K,
      Nonempty (Fintype ((independentPackage caller initial).Γ k))) ∧
    (∀ k : (authorPackage author initial).K,
      Nonempty (Fintype ((authorPackage author initial).Γ k))) ∧
    (∀ k : (twoLabelPackage twoCaller initial).K,
      Nonempty (Fintype ((twoLabelPackage twoCaller initial).Γ k))) :=
  ⟨fun k => ⟨machineAlphabetFintype caller initial k⟩,
    fun k => ⟨machineAlphabetFintype author initial k⟩,
    fun k => ⟨machineAlphabetFintype twoCaller initial k⟩⟩

theorem package_input_output_and_initial_control_are_actual_fields
    (caller : ExampleCaller) (initial : Bool) :
    (independentPackage caller initial).k₀ = .inl .certificate ∧
      (independentPackage caller initial).k₁ = .inl .source ∧
      (independentPackage caller initial).main = moveLabel .start ∧
      (independentPackage caller initial).initialState = clean initial := ⟨rfl, rfl, rfl, rfl⟩


end Examples.RotationCertificateMoveApplyMachine
