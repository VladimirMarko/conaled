import Examples.RotationCertificatePositionedRotationMachine.Execution

/-!
# RotationCertificatePositionedRotationMachine: Source
-/

namespace Examples.RotationCertificatePositionedRotationMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.RotationCertificate.PositionedRotationMachine

section RepresentedExecution

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- The actual source operation determines the first live endpoint, with literal old data. -/
theorem represented_first_return_retains_every_saved_word_and_suffix
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit) (F z : Word) :
    FirstRun caller
      (cfg (some (phaseLabel (.seek d))) regs (data (treeCode s ++ z) F [] [] p) ctx)
      (representedClock d p s + F.length)
      (cfg (some (resultLabel (if (applyMoveRun ⟨d,p⟩ s).1.isSome then .success else .failure)))
        (reset regs)
        (data (F.reverse ++ treeCode ((applyMoveRun ⟨d,p⟩ s).1.getD s) ++ z)
          [] [] [] (remainingPath p s)) ctx) := by
  exact firstRun_of_localRun caller (run_code_localRun caller d p s F z regs ctx)
    (by simp [Owned, cfg, resultLabel])

def representedWithSavedInTime (d : RotationDirection) (p : List Branch)
    (s : BinaryTree Unit) (F z : Word) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (.seek d))) regs (data (treeCode s ++ z) F [] [] p) ctx)
      (some (cfg
        (some (resultLabel (if (applyMoveRun ⟨d,p⟩ s).1.isSome then .success else .failure)))
        (reset regs)
        (data (F.reverse ++ treeCode ((applyMoveRun ⟨d,p⟩ s).1.getD s) ++ z)
          [] [] [] (remainingPath p s)) ctx))
      (representedClock d p s + F.length) :=
  localRunInTime caller (run_code_localRun caller d p s F z regs ctx)

theorem represented_timing_charges_old_saved_cells_exactly
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit) (F z : Word) :
    (representedWithSavedInTime caller regs ctx d p s F z).steps =
      representedClock d p s + F.length := rfl

theorem represented_success_has_empty_physical_path
    (d : RotationDirection) (p : List Branch) (s t : BinaryTree Unit)
    (returned : (applyMoveRun ⟨d,p⟩ s).1 = some t) (F z : Word) :
    FirstRun caller
      (cfg (some (phaseLabel (.seek d))) regs (data (treeCode s ++ z) F [] [] p) ctx)
      (representedClock d p s + F.length)
      (cfg (some (resultLabel .success)) (reset regs)
        (data (F.reverse ++ treeCode t ++ z) [] [] [] []) ctx) := by
  have actual := represented_first_return_retains_every_saved_word_and_suffix
    caller regs ctx d p s F z
  simpa only [returned, Option.isSome_some, ite_true, Option.getD_some,
    remainingPath_nil_of_source_success d p s t returned] using actual

theorem represented_failure_restores_the_literal_code_and_keeps_the_actual_tail
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (failed : (applyMoveRun ⟨d,p⟩ s).1 = none) (F z : Word) :
    FirstRun caller
      (cfg (some (phaseLabel (.seek d))) regs (data (treeCode s ++ z) F [] [] p) ctx)
      (representedClock d p s + F.length)
      (cfg (some (resultLabel .failure)) (reset regs)
        (data (F.reverse ++ treeCode s ++ z) [] [] [] (remainingPath p s)) ctx) := by
  simpa only [failed, Option.isSome_none, Bool.false_eq_true, ite_false, Option.getD_none] using
    represented_first_return_retains_every_saved_word_and_suffix caller regs ctx d p s F z

/-- Common-prefix cancellation and actual code-prefix injectivity identify the returned tree. -/
theorem represented_first_success_iff_the_actual_source_result
    (d : RotationDirection) (p : List Branch) (s t : BinaryTree Unit) (F z : Word) :
    (∃ n, FirstRun caller
      (cfg (some (phaseLabel (.seek d))) regs (data (treeCode s ++ z) F [] [] p) ctx) n
      (cfg (some (resultLabel .success)) (reset regs)
        (data (F.reverse ++ treeCode t ++ z) [] [] [] []) ctx)) ↔
      (applyMoveRun ⟨d,p⟩ s).1 = some t := by
  constructor
  · rintro ⟨n, first⟩
    have specified := represented_first_return_retains_every_saved_word_and_suffix
      caller regs ctx d p s F z
    have same := (firstRun_unique caller first specified).2
    have label := congrArg (fun c : Cfg Γ Λ R => c.l) same
    have source := congrArg (fun c : Cfg Γ Λ R => c.stk (.inl .source)) same
    cases actual : (applyMoveRun ⟨d,p⟩ s).1 with
    | none => simp [actual, cfg, resultLabel] at label
    | some u =>
        have codes : treeCode t ++ z = treeCode u ++ z :=
          List.append_cancel_left (as := F.reverse)
            (by simpa [actual, cfg, data, List.append_assoc] using source)
        have equal := (parseTreeRun_prefix_injective t u z z codes).1
        simp only [equal]
  · intro actual
    exact ⟨representedClock d p s + F.length,
      represented_success_has_empty_physical_path caller regs ctx d p s t actual F z⟩

end RepresentedExecution

theorem every_represented_fixture_is_an_actual_first_return
    (caller : ExampleCaller) (flag : Bool) (c : RepresentedFixture)
    (member : c ∈ representedFixtures) (F z : Word) : c.Expected caller flag F z := by
  have source := every_represented_fixture_has_its_source_result c member
  obtain ⟨clock, path⟩ := every_represented_fixture_has_its_fixed_clock_and_remaining_path c member
  refine ⟨source, clock, path, ?_⟩
  simpa only [atPhase, atResult, source, clock, path, reset, stale, clean] using
    represented_first_return_retains_every_saved_word_and_suffix caller (stale flag)
      ordinaryContext c.move.direction c.move.position c.tree F z

theorem all_represented_rows_keep_the_nonpalindromic_suffix
    (caller : ExampleCaller) (flag : Bool) (c : RepresentedFixture)
    (member : c ∈ representedFixtures) (F : Word) :
    c.Expected caller flag F [15,2,7] :=
  every_represented_fixture_is_an_actual_first_return caller flag c member F [15,2,7]

def representedFixtureInTime (caller : ExampleCaller) (flag : Bool)
    (c : RepresentedFixture) (member : c ∈ representedFixtures) (F z : Word) :
    StateTransition.EvalsToInTime (step caller)
      (atPhase (.seek c.move.direction) flag
        (data (treeCode c.tree ++ z) F [] [] c.move.position))
      (some (atResult (if c.value.isSome then .success else .failure) flag
        (data (F.reverse ++ treeCode (c.value.getD c.tree) ++ z) [] [] [] c.remaining)))
      (c.ticks + F.length) where
  steps := c.ticks + F.length
  evals_in_steps :=
    (every_represented_fixture_is_an_actual_first_return caller flag c member F z).2.2.2.1
  steps_le_m := Nat.le_refl _

theorem represented_fixture_time_uses_machine_ticks_and_saved_length
    (caller : ExampleCaller) (flag : Bool) (c : RepresentedFixture)
    (member : c ∈ representedFixtures) (F z : Word) :
    (representedFixtureInTime caller flag c member F z).steps = c.ticks + F.length := rfl

theorem the_context_prefix_is_the_actual_encoded_prefix
    (frames : List PositionFrame) (focus : BinaryTree Unit) :
    treeCode (plugFrames frames focus) =
      contextPrefix frames ++ treeCode focus ++ contextSuffix frames :=
  treeCode_plugFrames frames focus

theorem source_and_machine_clocks_have_separate_cursor_formulas
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit) :
    (applyMoveRun ⟨d,p⟩ s).2 =
      (if (applyMoveRun ⟨d,p⟩ s).1.isSome then 3 * descentCount p s + 5
       else 2 * descentCount p s + if stoppedPath p s = [] then 3 else 2) ∧
      representedClock d p s = 2 * navigationLength p s +
        (if stoppedPath p s = [] then representedClock d [] (stoppedTree p s) else 3) ∧
      remainingPath p s =
        (if stoppedPath p s = [] then [] else (stoppedPath p s).tail) :=
  ⟨source_cost_eq_stopped d p s, representedClock_eq_stopped d p s,
    remainingPath_eq_stopped p s⟩

def inverseStart (flag : Bool) : ExampleCfg :=
  cleanEntry .left flag [1,1,0,1,0,0,0] [.left]

def inverseReturned (flag : Bool) : ExampleCfg :=
  atResult .success flag (data [1,1,1,0,0,0,0] [] [] [] [])

def inverseReentry (reinstall flag : Bool) : ExampleCfg :=
  cfg (some (phaseLabel (.seek .right))) (clean flag)
    (data [1,1,1,0,0,0,0] [] [] [] (if reinstall then [.left] else [])) ordinaryContext

def inverseFinished (reinstall flag : Bool) : ExampleCfg :=
  atResult .success flag
    (data (if reinstall then [1,1,0,1,0,0,0] else [1,1,0,0,1,0,0]) [] [] [] [])

theorem inverse_first_segment (reinstall flag : Bool) :
    LocalRun (inverseCaller reinstall) 9 (inverseStart flag) (inverseReturned flag) :=
  run_code_localRun (inverseCaller reinstall) .left [.left] leftContext [] []
    (stale flag) ordinaryContext

theorem inverse_paid_reentry (reinstall flag : Bool) :
    step (inverseCaller reinstall) (inverseReturned flag) = some (inverseReentry reinstall flag) := by
  cases reinstall with
  | false =>
      exact inverse_reentry_without_push (clean flag)
        (data [1,1,1,0,0,0,0] [] [] [] []) ordinaryContext
  | true =>
      exact inverse_reentry_with_physical_push (clean flag)
        (data [1,1,1,0,0,0,0] [] [] [] []) ordinaryContext

theorem inverse_second_segment (reinstall flag : Bool) :
    LocalRun (inverseCaller reinstall) (if reinstall then 8 else 10)
      (inverseReentry reinstall flag) (inverseFinished reinstall flag) := by
  cases reinstall with
  | false =>
      exact run_code_localRun (inverseCaller false) .right [] afterLeftContext [] []
        (clean flag) ordinaryContext
  | true =>
      exact run_code_localRun (inverseCaller true) .right [.left] afterLeftContext [] []
        (clean flag) ordinaryContext

def inverseFirstInTime (reinstall flag : Bool) :
    StateTransition.EvalsToInTime (step (inverseCaller reinstall))
      (inverseStart flag) (some (inverseReturned flag)) 9 :=
  localRunInTime (inverseCaller reinstall) (inverse_first_segment reinstall flag)

def inverseReentryInTime (reinstall flag : Bool) :
    StateTransition.EvalsToInTime (step (inverseCaller reinstall))
      (inverseReturned flag) (some (inverseReentry reinstall flag)) 1 :=
  oneActualStepTime (inverseCaller reinstall) _ _ (inverse_paid_reentry reinstall flag)

def inverseSecondInTime (reinstall flag : Bool) :
    StateTransition.EvalsToInTime (step (inverseCaller reinstall))
      (inverseReentry reinstall flag) (some (inverseFinished reinstall flag))
      (if reinstall then 8 else 10) :=
  localRunInTime (inverseCaller reinstall) (inverse_second_segment reinstall flag)

/-- Two genuine segments are joined by a paid caller activation on the same finite program. -/
def composedInverseInTime (reinstall flag : Bool) :
    StateTransition.EvalsToInTime (step (inverseCaller reinstall))
      (inverseStart flag) (some (inverseFinished reinstall flag))
      ((if reinstall then 8 else 10) + 1 + 9) :=
  appendTimed (inverseCaller reinstall) (inverseStart flag) (inverseReturned flag)
    (some (inverseFinished reinstall flag)) 9 ((if reinstall then 8 else 10) + 1)
    (inverseFirstInTime reinstall flag)
    (appendTimed (inverseCaller reinstall) (inverseReturned flag)
      (inverseReentry reinstall flag) (some (inverseFinished reinstall flag))
      1 (if reinstall then 8 else 10)
      (inverseReentryInTime reinstall flag) (inverseSecondInTime reinstall flag))

theorem inverse_composition_retains_every_exact_paid_step (flag : Bool) :
    (inverseFirstInTime false flag).steps = 9 ∧
      (inverseReentryInTime false flag).steps = 1 ∧
      (inverseSecondInTime false flag).steps = 10 ∧
      (composedInverseInTime false flag).steps = 20 ∧
      (inverseFirstInTime true flag).steps = 9 ∧
      (inverseReentryInTime true flag).steps = 1 ∧
      (inverseSecondInTime true flag).steps = 8 ∧
      (composedInverseInTime true flag).steps = 18 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem a_consumed_path_changes_the_actual_inverse_endpoint (flag : Bool) :
    FirstRun (inverseCaller false) (inverseStart flag) 9 (inverseReturned flag) ∧
      (next (inverseCaller false))^[20] (some (inverseStart flag)) =
        some (atResult .success flag (data [1,1,0,0,1,0,0] [] [] [] [])) ∧
      (next (inverseCaller true))^[18] (some (inverseStart flag)) =
        some (atResult .success flag (data [1,1,0,1,0,0,0] [] [] [] [])) ∧
      (inverseReturned flag).stk (.inl .path) = [] ∧
      (inverseReentry true flag).stk (.inl .path) = [.left] ∧
      (inverseFinished false flag).stk (.inl .source) ≠
        (inverseStart flag).stk (.inl .source) := by
  refine ⟨firstRun_of_localRun (inverseCaller false) (inverse_first_segment false flag)
    (by simp [inverseReturned, atResult, cfg, resultLabel, Owned]),
    (composedInverseInTime false flag).evals_in_steps,
    (composedInverseInTime true flag).evals_in_steps, rfl, rfl, ?_⟩
  change ([1,1,0,0,1,0,0] : Word) ≠ [1,1,0,1,0,0,0]
  decide

def allocationReturned (flag : Bool) : ExampleCfg :=
  atResult .failure flag (data [] [] [] [] [])

def allocationOnce (flag : Bool) : ExampleCfg :=
  cfg (some (resultLabel .failure)) (clean flag) (data [] [] [] [] [])
    (protectedWords [15,2,7,10,3] [(),(),()])

def allocationTwice (flag : Bool) : ExampleCfg :=
  cfg (some (resultLabel .failure)) (clean flag) (data [] [] [] [] [])
    (protectedWords [15,2,7,10,3] [(),(),(),()])

def allocationReturnInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step allocatingCaller)
      (cleanEntry .left flag [] []) (some (allocationReturned flag)) 4 :=
  localRunInTime allocatingCaller
    (empty_root_physical_segment allocatingCaller (stale flag) ordinaryContext .left)

def allocationOnceInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step allocatingCaller)
      (cleanEntry .left flag [] []) (some (allocationOnce flag)) 5 :=
  appendTimed allocatingCaller _ (allocationReturned flag) _ 4 1
    (allocationReturnInTime flag)
    (oneActualStepTime allocatingCaller _ _
      (allocation_is_an_actual_protected_unit_push .failure (clean flag)
        (data [] [] [] [] []) [15,2,7,10,3] [(),()]))

def allocationTwiceInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step allocatingCaller)
      (cleanEntry .left flag [] []) (some (allocationTwice flag)) 6 :=
  appendTimed allocatingCaller _ (allocationOnce flag) _ 5 1
    (allocationOnceInTime flag)
    (oneActualStepTime allocatingCaller _ _
      (allocation_is_an_actual_protected_unit_push .failure (clean flag)
        (data [] [] [] [] []) [15,2,7,10,3] [(),(),()]))

theorem allocation_escapes_only_after_the_original_space_bound_ends (flag : Bool) :
    FirstRun allocatingCaller (cleanEntry .left flag [] []) 4 (allocationReturned flag) ∧
      stackCells (allocationReturned flag) = 7 ∧
      stackCells (allocationOnce flag) = 8 ∧
      stackCells (allocationTwice flag) = 9 ∧
      7 < stackCells (allocationOnce flag) ∧ 7 < stackCells (allocationTwice flag) ∧
      (allocationReturnInTime flag).steps = 4 ∧
      (allocationOnceInTime flag).steps = 5 ∧ (allocationTwiceInTime flag).steps = 6 := by
  have cells0 : stackCells (allocationReturned flag) = 7 := by
    simp [allocationReturned, atResult, stackCells_cfg, localCells, data,
      ordinaryContext, protected_words_have_the_actual_two_stack_cell_sum]
  have cells1 : stackCells (allocationOnce flag) = 8 := by
    simp [allocationOnce, stackCells_cfg, localCells, data,
      protected_words_have_the_actual_two_stack_cell_sum]
  have cells2 : stackCells (allocationTwice flag) = 9 := by
    simp [allocationTwice, stackCells_cfg, localCells, data,
      protected_words_have_the_actual_two_stack_cell_sum]
  exact ⟨firstRun_of_localRun allocatingCaller
      (empty_root_physical_segment allocatingCaller (stale flag) ordinaryContext .left)
      (by simp [allocationReturned, atResult, cfg, resultLabel, Owned]),
    cells0, cells1, cells2, by omega, by omega, rfl, rfl, rfl⟩

def misleadingLaterFailureInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step misleadingCaller)
      (cleanEntry .left flag [1,0,1,0,0] [])
      (some (atResult .failure flag (data [1,1,0,0,0] [] [] [] []))) 8 :=
  appendTimed misleadingCaller _
    (atResult .success flag (data [1,1,0,0,0] [] [] [] [])) _ 7 1
    (minimalLeftInTime misleadingCaller flag)
    (oneActualStepTime misleadingCaller _ _
      (a_caller_can_forge_the_opposite_result (clean flag)
        (data [1,1,0,0,0] [] [] [] []) ordinaryContext).1)

def misleadingLaterSuccessInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step misleadingCaller)
      (cleanEntry .left flag [] [])
      (some (atResult .success flag (data [] [] [] [] []))) 5 :=
  appendTimed misleadingCaller _ (atResult .failure flag (data [] [] [] [] [])) _ 4 1
    (localRunInTime misleadingCaller
      (empty_root_physical_segment misleadingCaller (stale flag) ordinaryContext .left))
    (oneActualStepTime misleadingCaller _ _
      (a_caller_can_forge_the_opposite_result (clean flag)
        (data [] [] [] [] []) ordinaryContext).2)

def externalLive (flag : Bool) : ExampleCfg :=
  cfg (some (callerLabel ())) (clean flag) (data [] [] [] [] []) ordinaryContext

def externalHalt (flag : Bool) : ExampleCfg :=
  cfg none (clean flag) (data [] [] [] [] [])
    (protectedWords [13,15,2,7,10,3] [(),()])

def externalGotoInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step externalCaller)
      (cleanEntry .left flag [] []) (some (externalLive flag)) 5 :=
  appendTimed externalCaller _ (atResult .failure flag (data [] [] [] [] [])) _ 4 1
    (localRunInTime externalCaller
      (empty_root_physical_segment externalCaller (stale flag) ordinaryContext .left))
    (oneActualStepTime externalCaller _ _
      (separate_external_label_is_reached_first .failure (clean flag)
        (data [] [] [] [] []) ordinaryContext))

def externalHaltInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step externalCaller)
      (cleanEntry .left flag [] []) (some (externalHalt flag)) 6 :=
  appendTimed externalCaller _ (externalLive flag) _ 5 1
    (externalGotoInTime flag)
    (oneActualStepTime externalCaller _ _
      (external_label_executes_its_own_push_and_halt (clean flag)
        (data [] [] [] [] []) [15,2,7,10,3] [(),()]))

def externalOuterNoneInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step externalCaller)
      (cleanEntry .left flag [] []) none 7 :=
  appendTimed externalCaller _ (externalHalt flag) none 6 1
    (externalHaltInTime flag) (oneActualStepTime externalCaller _ none rfl)

theorem misleading_and_external_timing_retains_the_actual_activations (flag : Bool) :
    (misleadingLaterFailureInTime flag).steps = 8 ∧
      (misleadingLaterSuccessInTime flag).steps = 5 ∧
      (externalGotoInTime flag).steps = 5 ∧
      (externalHaltInTime flag).steps = 6 ∧
      (externalOuterNoneInTime flag).steps = 7 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem firstSuccess_iff_the_canonical_live_label
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (q : Phase)
    (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    FirstSuccess caller (cfg (some (phaseLabel q)) regs D ctx) ↔
      (phaseResult (Λ := Λ) q regs D ctx).l = some (resultLabel .success) := by
  constructor
  · rintro ⟨n, reached, first, label⟩
    have same := (firstRun_unique caller first (phase_first_return caller q D regs ctx)).2
    simpa only [same] using label
  · intro label
    exact ⟨phaseSteps q D, phaseResult q regs D ctx,
      phase_first_return caller q D regs ctx, label⟩

theorem arbitrary_raw_root_first_success_characterizations
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (w F : Word) :
    (FirstSuccess caller
      (cfg (some (phaseLabel (.seek .left))) regs (data w F [] [] []) ctx) ↔
      ∃ A : BinaryTree Unit, ∃ z : Word, w = [1] ++ treeCode A ++ [1] ++ z) ∧
      (FirstSuccess caller
        (cfg (some (phaseLabel (.seek .right))) regs (data w F [] [] []) ctx) ↔
        ∃ A : BinaryTree Unit, ∃ z : Word, w = [1,1] ++ treeCode A ++ z) := by
  constructor
  · exact (firstSuccess_iff_the_canonical_live_label caller (.seek .left) regs
      (data w F [] [] []) ctx).trans (by
      simpa only [List.singleton_append, List.cons_append, List.nil_append,
        List.append_assoc, data, nodeTag] using root_left_phaseResult_success_iff caller w F regs ctx)
  · exact (firstSuccess_iff_the_canonical_live_label caller (.seek .right) regs
      (data w F [] [] []) ctx).trans (by
      simpa only [List.singleton_append, List.cons_append, List.nil_append,
        List.append_assoc, data, nodeTag] using root_right_phaseResult_success_iff caller w F regs ctx)

/-- The two root iff clauses concern the first actual handoff under arbitrary caller bodies. -/
theorem both_raw_root_success_characterizations (caller : ExampleCaller)
    (flag : Bool) (w : Word) : RootSuccessIffExpected caller flag w := by
  exact arbitrary_raw_root_first_success_characterizations caller (stale flag) ordinaryContext w []

theorem both_malformed_root_successes_are_actual_unrecognized_first_returns
    (caller : ExampleCaller) (flag : Bool) :
    FirstRun caller (cleanEntry .left flag [1,0,1,15] []) 7
      (atResult .success flag (data [1,1,0,15] [] [] [] [])) ∧
      FirstRun caller (cleanEntry .right flag [1,1,0,15] []) 6
        (atResult .success flag (data [1,0,1,15] [] [] [] [])) ∧
      (parseTreeRun [1,0,1,15]).1 = none ∧ (parseTreeRun [1,1,0,15]).1 = none := by
  exact ⟨firstRun_of_localRun caller
      (root_left_pattern_localRun caller nilTree [15] [] (stale flag) ordinaryContext)
      (by simp [atResult, cfg, resultLabel, Owned]),
    firstRun_of_localRun caller
      (root_right_pattern_localRun caller nilTree [15] [] (stale flag) ordinaryContext)
      (by simp [atResult, cfg, resultLabel, Owned]), rfl, rfl⟩

theorem old_pending_changes_the_valid_tree_operation (caller : ExampleCaller) (flag : Bool) :
    FirstRun caller (cleanEntry .left flag [1,0,1,0,0] []) 7
      (atResult .success flag (data [1,1,0,0,0] [] [] [] [])) ∧
      FirstRun caller (atPhase (.seek .left) flag (data [1,0,1,0,0] [] [] [()] [])) 14
        (atResult .failure flag (data [1,0,1,0,0] [] [] [] [])) := by
  refine ⟨minimal_left_first_return caller flag, ?_⟩
  exact every_raw_fixture_is_an_actual_first_return caller flag
    ⟨.seek .left, data [1,0,1,0,0] [] [] [()] [], .failure,
      data [1,0,1,0,0] [] [] [] [], 14⟩ (by simp [rawFixtures])

section SharpMalformedFamilies

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- All n, including zero, reach the literal size-maximizing drop state before failure. -/
theorem left_all_nodes_have_the_sharp_actual_clock_and_space (n : Nat) :
    FirstRun caller
      (cfg (some (phaseLabel (.seek .left))) regs (data (List.replicate n 1) [] [] [] []) ctx)
      (3 * n + 4)
      (cfg (some (resultLabel .failure)) (reset regs) (data (List.replicate n 1) [] [] [] []) ctx) ∧
      Runs caller
        (cfg (some (phaseLabel (.seek .left))) regs (data (List.replicate n 1) [] [] [] []) ctx)
        (2 * n + 2)
        (cfg (some (phaseLabel .dropPending)) (reset regs)
          (data (List.replicate n 1) [] [] (List.replicate n ()) []) ctx) ∧
      remainingSteps (cfg (some (phaseLabel .dropPending)) (reset regs)
        (data (List.replicate n 1) [] [] (List.replicate n ()) []) ctx : Cfg Γ Λ R) = n + 2 ∧
      stackCells (cfg (some (phaseLabel .dropPending)) (reset regs)
        (data (List.replicate n 1) [] [] (List.replicate n ()) []) ctx : Cfg Γ Λ R) =
          2 * n + contextCells ctx :=
  ⟨firstRun_of_localRun caller (left_nodes_run caller n regs ctx)
      (by simp [cfg, resultLabel, Owned]),
    LocalRun.iterate caller (left_nodes_drop caller n regs ctx),
    left_nodes_drop_rank caller n (reset regs) ctx,
    left_nodes_drop_cells n (reset regs) ctx⟩

theorem right_all_nodes_keep_the_one_cell_gap (m : Nat) :
    FirstRun caller
      (cfg (some (phaseLabel (.seek .right))) regs
        (data (List.replicate (m + 2) 1) [] [] [] []) ctx)
      (3 * m + 7)
      (cfg (some (resultLabel .failure)) (reset regs)
        (data (List.replicate (m + 2) 1) [] [] [] []) ctx) ∧
      Runs caller
        (cfg (some (phaseLabel (.seek .right))) regs
          (data (List.replicate (m + 2) 1) [] [] [] []) ctx)
        (2 * m + 4)
        (cfg (some (phaseLabel .dropPending)) (reset regs)
          (data (List.replicate (m + 2) 1) [] [] (List.replicate (m + 1) ()) []) ctx) ∧
      remainingSteps (cfg (some (phaseLabel .dropPending)) (reset regs)
        (data (List.replicate (m + 2) 1) [] [] (List.replicate (m + 1) ()) []) ctx : Cfg Γ Λ R) =
          m + 3 ∧
      stackCells (cfg (some (phaseLabel .dropPending)) (reset regs)
        (data (List.replicate (m + 2) 1) [] [] (List.replicate (m + 1) ()) []) ctx : Cfg Γ Λ R) =
          2 * m + 3 + contextCells ctx :=
  ⟨firstRun_of_localRun caller (right_nodes_run caller m regs ctx)
      (by simp [cfg, resultLabel, Owned]),
    LocalRun.iterate caller (right_nodes_drop caller m regs ctx),
    right_nodes_drop_rank caller m (reset regs) ctx,
    right_nodes_drop_cells m (reset regs) ctx⟩

omit [Fintype K] in
theorem right_empty_and_singleton_are_the_separate_four_step_routes :
    FirstRun caller
      (cfg (some (phaseLabel (.seek .right))) regs (data [] [] [] [] []) ctx) 4
      (cfg (some (resultLabel .failure)) (reset regs) (data [] [] [] [] []) ctx) ∧
      FirstRun caller
        (cfg (some (phaseLabel (.seek .right))) regs (data [1] [] [] [] []) ctx) 4
        (cfg (some (resultLabel .failure)) (reset regs) (data [1] [] [] [] []) ctx) :=
  ⟨firstRun_of_localRun caller (root_nonnode_localRun caller .right [] [] True.intro regs ctx)
      (by simp [cfg, resultLabel, Owned]),
    firstRun_of_localRun caller (root_right_second_nonnode_localRun caller [] [] True.intro regs ctx)
      (by simp [cfg, resultLabel, Owned])⟩

omit [Fintype K] in
theorem an_overlong_position_consumes_only_its_first_failing_head
    (d : RotationDirection) (n k : Nat) (positive : 0 < k) :
    FirstRun caller
      (cfg (some (phaseLabel (.seek d))) regs
        (data (List.replicate n 1) [] [] [] (List.replicate (n + k) .left)) ctx)
      (2 * n + 3)
      (cfg (some (resultLabel .failure)) (reset regs)
        (data (List.replicate n 1) [] [] [] (List.replicate (k - 1) .left)) ctx) :=
  firstRun_of_localRun caller (left_path_overrun caller d n k positive regs ctx)
    (by simp [cfg, resultLabel, Owned])

omit [Fintype K] in
theorem exhausting_the_position_before_eof_takes_the_distinct_root_route
    (d : RotationDirection) (n : Nat) :
    FirstRun caller
      (cfg (some (phaseLabel (.seek d))) regs
        (data (List.replicate n 1) [] [] [] (List.replicate n .left)) ctx)
      (2 * n + 4)
      (cfg (some (resultLabel .failure)) (reset regs) (data (List.replicate n 1) [] [] [] []) ctx) :=
  firstRun_of_localRun caller (left_path_exhausted caller d n regs ctx)
    (by simp [cfg, resultLabel, Owned])

def leftAllNodesInTime (n : Nat) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (.seek .left))) regs (data (List.replicate n 1) [] [] [] []) ctx)
      (some (cfg (some (resultLabel .failure)) (reset regs)
        (data (List.replicate n 1) [] [] [] []) ctx)) (3 * n + 4) :=
  localRunInTime caller (left_nodes_run caller n regs ctx)

def rightAllNodesInTime (m : Nat) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (.seek .right))) regs (data (List.replicate (m + 2) 1) [] [] [] []) ctx)
      (some (cfg (some (resultLabel .failure)) (reset regs)
        (data (List.replicate (m + 2) 1) [] [] [] []) ctx)) (3 * m + 7) :=
  localRunInTime caller (right_nodes_run caller m regs ctx)

def overlongPathInTime (d : RotationDirection) (n k : Nat) (positive : 0 < k) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (.seek d))) regs
        (data (List.replicate n 1) [] [] [] (List.replicate (n + k) .left)) ctx)
      (some (cfg (some (resultLabel .failure)) (reset regs)
        (data (List.replicate n 1) [] [] [] (List.replicate (k - 1) .left)) ctx)) (2 * n + 3) :=
  localRunInTime caller (left_path_overrun caller d n k positive regs ctx)

def exhaustedPathInTime (d : RotationDirection) (n : Nat) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (.seek d))) regs
        (data (List.replicate n 1) [] [] [] (List.replicate n .left)) ctx)
      (some (cfg (some (resultLabel .failure)) (reset regs)
        (data (List.replicate n 1) [] [] [] []) ctx)) (2 * n + 4) :=
  localRunInTime caller (left_path_exhausted caller d n regs ctx)

omit [Fintype K] in
theorem sharp_family_timing_retains_the_exact_machine_counts
    (d : RotationDirection) (n m k : Nat) (positive : 0 < k) :
    (leftAllNodesInTime caller regs ctx n).steps = 3 * n + 4 ∧
      (rightAllNodesInTime caller regs ctx m).steps = 3 * m + 7 ∧
      (overlongPathInTime caller regs ctx d n k positive).steps = 2 * n + 3 ∧
      (exhaustedPathInTime caller regs ctx d n).steps = 2 * n + 4 := ⟨rfl, rfl, rfl, rfl⟩

end SharpMalformedFamilies

section AllRawContracts

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem every_raw_word_has_a_clean_first_endpoint_with_its_actual_path_suffix
    (d : RotationDirection) (raw : Word) (path : List Branch) :
    ∃ r output rest,
      FirstRun caller (entry d regs raw path ctx) (runSteps d raw path)
        (cfg (some (resultLabel r)) (reset regs) (data output [] [] [] rest) ctx) ∧
      output.length = raw.length ∧ (∃ consumed, path = consumed ++ rest) ∧
      (r = .failure → output = raw) ∧ (r = .success → rest = []) := by
  obtain ⟨r, output, rest, segment, length, suffix, failure, success⟩ :=
    run_raw caller d raw path regs ctx
  exact ⟨r, output, rest, firstRun_of_localRun caller segment
    (by simp [cfg, resultLabel, Owned]), length, suffix, failure, success⟩

/-- Failure restores the original literal input at the unique first handoff. -/
theorem any_raw_first_failure_restores_every_original_source_cell
    (d : RotationDirection) (raw : Word) (path : List Branch)
    (n : Nat) (finish : Cfg Γ Λ R)
    (first : FirstRun caller (entry d regs raw path ctx) n finish)
    (failed : finish.l = some (resultLabel .failure)) :
    n = runSteps d raw path ∧ finish.stk (.inl .source) = raw ∧
      finish.stk (.inl .saved) = [] ∧ finish.stk (.inl .scratch) = [] ∧
      finish.stk (.inl .pending) = [] ∧
      (∃ consumed, path = consumed ++ finish.stk (.inl .path)) ∧
      finish.var = reset regs ∧ ∀ k, finish.stk (.inr k) = ctx k := by
  obtain ⟨count, same⟩ := firstRun_unique caller first
    (phase_first_return caller (.seek d) { source := raw, path := path } regs ctx)
  subst finish
  obtain ⟨saved, scratch, pending⟩ := run_raw_clean caller d raw path regs ctx
  exact ⟨count, run_raw_failure caller d raw path regs ctx failed,
    saved, scratch, pending, run_raw_path_suffix caller d raw path regs ctx,
    rfl, fun _ => rfl⟩

theorem any_raw_first_success_preserves_length_and_consumes_the_position
    (d : RotationDirection) (raw : Word) (path : List Branch)
    (n : Nat) (finish : Cfg Γ Λ R)
    (first : FirstRun caller (entry d regs raw path ctx) n finish)
    (succeeded : finish.l = some (resultLabel .success)) :
    n = runSteps d raw path ∧ (finish.stk (.inl .source)).length = raw.length ∧
      finish.stk (.inl .saved) = [] ∧ finish.stk (.inl .scratch) = [] ∧
      finish.stk (.inl .pending) = [] ∧ finish.stk (.inl .path) = [] ∧
      finish.var = reset regs ∧ ∀ k, finish.stk (.inr k) = ctx k := by
  obtain ⟨count, same⟩ := firstRun_unique caller first
    (phase_first_return caller (.seek d) { source := raw, path := path } regs ctx)
  subst finish
  obtain ⟨saved, scratch, pending⟩ := run_raw_clean caller d raw path regs ctx
  exact ⟨count, run_raw_length caller d raw path regs ctx,
    saved, scratch, pending, run_raw_success caller d raw path regs ctx succeeded,
    rfl, fun _ => rfl⟩

theorem every_actual_dirty_successor_has_the_natural_countdown_drop
    (q : Phase) (D : LocalData) :
    step caller (cfg (some (phaseLabel q)) regs D ctx) =
      some (cfg (some (controlLabel (advance q D).1)) (reset regs) (advance q D).2 ctx) ∧
      countdown (advance q D).1 (advance q D).2 + 1 ≤ countdown (.inl q) D :=
  ⟨advance_step caller q D regs ctx, advance_countdown q D⟩

theorem the_natural_countdown_is_distinct_from_the_exact_remaining_rank :
    step caller (cfg (some (phaseLabel (.start .left))) regs (data [] [] [] [] []) ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) (data [] [] [] [] []) ctx) ∧
      countdown (.inl (.start .left)) (data [] [] [] [] []) = 4 ∧
      countdown (.inl .dropPending) (data [] [] [] [] []) = 2 ∧
      remainingSteps (cfg (some (phaseLabel (.start .left))) regs
        (data [] [] [] [] []) ctx : Cfg Γ Λ R) = 3 := by
  refine ⟨start_left_step_nil caller (data [] [] [] [] []) regs ctx, rfl, rfl, ?_⟩
  have segment := LocalRun.trans caller
    (phase_step_localRun caller (start_left_step_nil caller (data [] [] [] [] []) regs ctx))
    (dropPending_localRun caller (data [] [] [] [] []) (reset regs) ctx)
  simpa only [remainingSteps, cfg, phaseLabel, resultLabel, dataOfCfg,
    data, List.length_nil, Nat.add_zero] using LocalRun.remaining caller segment

end AllRawContracts

def genericBoundaryCfg {K Λ R : Type} {Γ : K → Type}
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (b : Boundary) : Cfg Γ Λ R :=
  cfg (some (controlLabel b.2.1)) (if b.1 = 0 then regs else reset regs) b.2.2.1 ctx

section GenericBoundaryContracts

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- Every literal left boundary also holds for arbitrary stale fields and protected words. -/
theorem left_literal_boundaries_keep_arbitrary_registers_and_protected_data
    (b : Boundary) (member : b ∈ leftBoundaries) :
    Runs caller
      (cfg (some (phaseLabel (.seek .left))) regs (data [1,0,1,0,0] [] [] [] []) ctx)
      b.1 (genericBoundaryCfg regs ctx b) ∧
      stackCells (genericBoundaryCfg regs ctx b : Cfg Γ Λ R) = b.2.2.2 + contextCells ctx ∧
      (genericBoundaryCfg regs ctx b : Cfg Γ Λ R).var =
        (if b.1 = 0 then regs else reset regs) := by
  simp only [leftBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, rfl⟩
    · simp [Runs, genericBoundaryCfg, Function.iterate_succ_apply, next_some,
        advance_step, advance, controlLabel, nodeTag, emptyTag, data, reset_reset,
        markerWord, modeResult]
    · simp only [genericBoundaryCfg, stackCells_cfg]
      simp [localCells, data]

theorem right_literal_boundaries_keep_arbitrary_registers_and_protected_data
    (b : Boundary) (member : b ∈ rightBoundaries) :
    Runs caller
      (cfg (some (phaseLabel (.seek .right))) regs (data [1,1,0,0,0] [] [] [] []) ctx)
      b.1 (genericBoundaryCfg regs ctx b) ∧
      stackCells (genericBoundaryCfg regs ctx b : Cfg Γ Λ R) = b.2.2.2 + contextCells ctx ∧
      (genericBoundaryCfg regs ctx b : Cfg Γ Λ R).var =
        (if b.1 = 0 then regs else reset regs) := by
  simp only [rightBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, rfl⟩
    · simp [Runs, genericBoundaryCfg, Function.iterate_succ_apply, next_some,
        advance_step, advance, controlLabel, nodeTag, emptyTag, data, reset_reset,
        markerWord, modeResult]
    · simp only [genericBoundaryCfg, stackCells_cfg]
      simp [localCells, data]

end GenericBoundaryContracts

theorem actual_source_success_is_decided_at_the_stopped_cursor
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit) :
    (applyMoveRun ⟨d,p⟩ s).1.isSome =
      (if stoppedPath p s = [] then (rotateRun d (stoppedTree p s)).1.isSome else false) := by
  induction p generalizing s with
  | nil => simp only [source_root, stoppedPath, stoppedTree, ite_true]
  | cons b p ih =>
      cases s with
      | nil => simp only [source_nil_cons, stoppedPath, List.cons_ne_nil, ite_false, Option.isSome_none]
      | node a l r =>
          cases a
          cases b with
          | left =>
              have child := ih l
              cases actual : (applyMoveRun ⟨d,p⟩ l).1 <;>
                by_cases ended : stoppedPath p l = [] <;>
                simpa [source_left, actual, stoppedPath, stoppedTree, ended] using child
          | right =>
              have child := ih r
              cases actual : (applyMoveRun ⟨d,p⟩ r).1 <;>
                by_cases ended : stoppedPath p r = [] <;>
                simpa [source_right, actual, stoppedPath, stoppedTree, ended] using child

theorem cursor_left_success_has_the_fixed_source_machine_pair
    (p : List Branch) (s A B C : BinaryTree Unit)
    (ended : stoppedPath p s = [])
    (focus : stoppedTree p s = .node () A (.node () B C)) :
    ((applyMoveRun ⟨.left,p⟩ s).2, representedClock .left p s) =
      (3 * descentCount p s + 5, 2 * navigationLength p s + 2 * (treeCode A).length + 5) := by
  rw [source_cost_eq_stopped, representedClock_eq_stopped]
  simp [actual_source_success_is_decided_at_the_stopped_cursor, ended, focus,
    representedClock, Nat.add_assoc]

theorem cursor_right_success_has_the_fixed_source_machine_pair
    (p : List Branch) (s A B C : BinaryTree Unit)
    (ended : stoppedPath p s = [])
    (focus : stoppedTree p s = .node () (.node () A B) C) :
    ((applyMoveRun ⟨.right,p⟩ s).2, representedClock .right p s) =
      (3 * descentCount p s + 5, 2 * navigationLength p s + 2 * (treeCode A).length + 4) := by
  rw [source_cost_eq_stopped, representedClock_eq_stopped]
  simp [actual_source_success_is_decided_at_the_stopped_cursor, ended, focus,
    representedClock, Nat.add_assoc]

theorem cursor_missing_nil_has_the_fixed_source_machine_pair
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (missing : stoppedPath p s ≠ []) :
    ((applyMoveRun ⟨d,p⟩ s).2, representedClock d p s) =
      (2 * descentCount p s + 2, 2 * navigationLength p s + 3) := by
  rw [source_cost_eq_stopped, representedClock_eq_stopped]
  simp [actual_source_success_is_decided_at_the_stopped_cursor, missing]

theorem cursor_exhausted_nil_has_the_fixed_source_machine_pair
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (ended : stoppedPath p s = []) (focus : stoppedTree p s = .nil) :
    ((applyMoveRun ⟨d,p⟩ s).2, representedClock d p s) =
      (2 * descentCount p s + 3, 2 * navigationLength p s + 4) := by
  rw [source_cost_eq_stopped, representedClock_eq_stopped]
  simp [actual_source_success_is_decided_at_the_stopped_cursor, ended, focus, representedClock]

theorem cursor_right_nil_child_has_the_fixed_source_machine_pair
    (p : List Branch) (s C : BinaryTree Unit)
    (ended : stoppedPath p s = []) (focus : stoppedTree p s = .node () .nil C) :
    ((applyMoveRun ⟨.right,p⟩ s).2, representedClock .right p s) =
      (2 * descentCount p s + 3, 2 * navigationLength p s + 4) := by
  rw [source_cost_eq_stopped, representedClock_eq_stopped]
  simp [actual_source_success_is_decided_at_the_stopped_cursor, ended, focus,
    representedClock, rotateRun]

theorem cursor_left_nil_child_has_the_fixed_source_machine_pair
    (p : List Branch) (s A : BinaryTree Unit)
    (ended : stoppedPath p s = []) (focus : stoppedTree p s = .node () A .nil) :
    ((applyMoveRun ⟨.left,p⟩ s).2, representedClock .left p s) =
      (2 * descentCount p s + 3, 2 * navigationLength p s + 2 * (treeCode A).length + 6) := by
  rw [source_cost_eq_stopped, representedClock_eq_stopped]
  simp [actual_source_success_is_decided_at_the_stopped_cursor, ended, focus,
    representedClock, rotateRun, Nat.add_assoc]

section ActualCursorPrefix

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem represented_cursor_is_reached_before_its_final_path_observation
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit) (F z : Word) :
    Runs caller
      (cfg (some (phaseLabel (.seek d))) regs (data (treeCode s ++ z) F [] [] p) ctx)
      (navigationLength p s)
      (cfg (some (phaseLabel (.seek d)))
        (if navigationLength p s = 0 then regs else reset regs)
        (data (treeCode (stoppedTree p s) ++ contextSuffix (navigationFrames p s) ++ z)
          ((contextPrefix (navigationFrames p s)).reverse ++ F) [] [] (stoppedPath p s)) ctx) := by
  simpa only [Runs, data, afterScanRegisters, navigationLength_eq_prefix,
    List.length_eq_zero_iff] using
    seek_cursor_iterate caller d p s F z regs ctx

def representedCursorInTime (d : RotationDirection) (p : List Branch)
    (s : BinaryTree Unit) (F z : Word) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (.seek d))) regs (data (treeCode s ++ z) F [] [] p) ctx)
      (some (cfg (some (phaseLabel (.seek d)))
        (if navigationLength p s = 0 then regs else reset regs)
        (data (treeCode (stoppedTree p s) ++ contextSuffix (navigationFrames p s) ++ z)
          ((contextPrefix (navigationFrames p s)).reverse ++ F) [] [] (stoppedPath p s)) ctx))
      (navigationLength p s) where
  steps := navigationLength p s
  evals_in_steps := represented_cursor_is_reached_before_its_final_path_observation
    caller regs ctx d p s F z
  steps_le_m := Nat.le_refl _

end ActualCursorPrefix

end Examples.RotationCertificatePositionedRotationMachine
