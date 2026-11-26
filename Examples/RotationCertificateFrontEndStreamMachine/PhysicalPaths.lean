import Examples.RotationCertificateFrontEndStreamMachine.DirtyExecution

/-!
# RotationCertificateFrontEndStreamMachine: PhysicalPaths
-/

namespace Examples.RotationCertificateFrontEndStreamMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.FrontEndStreamMachine

/-! ## Actual physical paths after dirty FrontEnd handoff -/

section LiteralDirtyPhysicalPaths

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

omit caller [DecidableEq K] in
theorem a_stream_phase_view_reinserts_all_the_front_end_complement_words
    (q : StreamMachine.Phase) (D : LocalData) (E : StreamMachine.LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    streamCfg (Λ := Λ) (StreamMachine.cfg (some (StreamMachine.phaseLabel q))
      (StreamMachine.frontEndRegisterEquiv regs) E (streamContext D ctx)) =
    cfg (some (phaseLabel (streamPhase q))) regs (withStream D E) ctx := by
  simpa only [streamView, streamData_withStream, streamContext_withStream,
    Option.map_some, streamLabelEquiv_phase] using
      streamCfg_view (Λ := Λ) (some (StreamMachine.phaseLabel q)) regs (withStream D E) ctx

theorem a_literal_stream_prefix_is_an_actual_common_carrier_prefix
    (points : Nat → Examples.RotationCertificateStreamMachine.TracePoint)
    (ticks n : Nat) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R)
    (initial : (points 0).reached (Λ := StreamCallerLabel Λ)
        (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx) =
      StreamMachine.cfg (some (StreamMachine.phaseLabel StreamMachine.inspectPhase))
        (StreamMachine.frontEndRegisterEquiv regs) (streamData D) (streamContext D ctx))
    (adjacent : ∀ j, j < ticks →
      StreamMachine.step localCaller ((points j).reached
        (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx)) =
      some ((points (j + 1)).reached
        (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx)))
    (owned : ∀ j, j < ticks → (points j).control.isLeft = true) (bound : n ≤ ticks) :
    LocalRun caller n
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase))) regs D ctx)
      (streamCfg ((points n).reached
        (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx))) := by
  have executed := Examples.RotationCertificateStreamMachine.finite_trace_actual_prefix
    localCaller (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx)
    points ticks adjacent n bound
  have earlier : ∀ j, j < n → ∃ reached,
      (StreamMachine.next localCaller)^[j]
        (some ((points 0).reached (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx))) =
      some reached ∧ StreamMachine.Owned reached.l := by
    intro j strict
    refine ⟨(points j).reached (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx),
      Examples.RotationCertificateStreamMachine.finite_trace_actual_prefix localCaller
        (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx)
        points ticks adjacent j (by omega), ?_⟩
    exact Examples.RotationCertificateStreamMachine.trace_point_with_phase_control_is_owned
      (points j) (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx) (owned j (by omega))
  have actual := stream_localRun caller localCaller
    (StreamMachine.LocalRun.of_iterate localCaller executed earlier)
  rw [initial, common_stream_start_is_the_complete_view] at actual
  exact actual

def dirtyD01PhysicalPathData : LocalData :=
  withStream dirtyD01.stream.before (Examples.RotationCertificateStreamMachine.traceR10 9).stores

def dirtyD02PhysicalPathData : LocalData :=
  withStream dirtyD02.stream.before (StreamCertificates.traceSegmentD02 12).stores

def dirtyD02ConsumedFailingHeadData : LocalData :=
  withStream dirtyD02.stream.before (StreamCertificates.traceSegmentD02 14).stores

theorem dirtyD01_actual_physical_path_is_reverse_old_reverse_followed_by_old_path
    (value : R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (dirtyD01.toClosedFixture.start value ctx) 209
      (cfg (some (phaseLabel (streamPhase (StreamMachine.applyPhase
        (MoveApplyMachine.positionPhase (.seek .left)))))) (clean value) dirtyD01PhysicalPathData ctx) ∧
    dirtyD01PhysicalPathData.path = [.right, .left] ∧
    dirtyD01PhysicalPathData.moveReverse = [] ∧
    dirtyD01PhysicalPathData.sourceTree = [1, 0, 1, 0, 0] := by
  let localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R := fun _ => .halt
  have source := a_literal_stream_prefix_is_an_actual_common_carrier_prefix caller
    Examples.RotationCertificateStreamMachine.traceR10 20 9 dirtyD01.stream.before
    (clean value) ctx localCaller rfl
    (Examples.RotationCertificateStreamMachine.traceR10_steps localCaller
      (StreamMachine.frontEndRegisterEquiv (clean value)) (streamContext dirtyD01.stream.before ctx))
    Examples.RotationCertificateStreamMachine.traceR10_owned (by decide)
  have endpoint : streamCfg (Λ := Λ) ((Examples.RotationCertificateStreamMachine.traceR10 9).reached
      (StreamMachine.frontEndRegisterEquiv (clean value)) (streamContext dirtyD01.stream.before ctx)) =
    cfg (some (phaseLabel (streamPhase (StreamMachine.applyPhase
      (MoveApplyMachine.positionPhase (.seek .left)))))) (clean value) dirtyD01PhysicalPathData ctx :=
    a_stream_phase_view_reinserts_all_the_front_end_complement_words (Λ := Λ)
      (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.seek .left)))
      dirtyD01.stream.before (Examples.RotationCertificateStreamMachine.traceR10 9).stores
      (clean value) ctx
  rw [endpoint] at source
  have first := dirtyD01_frontend_actual_local_run caller value ctx
  have joined := phase_step_localRun caller (dispatch_step caller dirtyD01.frontEndAfter
    (FrontEndMachine.reset (dirtyD01.fields.withUser value)) ctx)
  exact ⟨(LocalRun.trans caller (LocalRun.trans caller first joined) source).iterate caller, rfl, rfl, rfl⟩

theorem dirtyD02_actual_physical_path_keeps_both_old_branch_words_in_order
    (value : R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (dirtyD02.toClosedFixture.start value ctx) 270
      (cfg (some (phaseLabel (streamPhase (StreamMachine.applyPhase
        (MoveApplyMachine.positionPhase (.seek .left)))))) (clean value) dirtyD02PhysicalPathData ctx) ∧
    dirtyD02PhysicalPathData.path = [.left, .right, .right, .left, .right] ∧
    dirtyD02PhysicalPathData.moveReverse = [] ∧
    dirtyD02PhysicalPathData.sourceTree = [1, 0, 1, 0, 1, 0, 0] := by
  let localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R := fun _ => .halt
  have source := a_literal_stream_prefix_is_an_actual_common_carrier_prefix caller
    StreamCertificates.traceSegmentD02 18 12 dirtyD02.stream.before (clean value) ctx localCaller rfl
    (StreamCertificates.traceSegmentD02_steps localCaller
      (StreamMachine.frontEndRegisterEquiv (clean value)) (streamContext dirtyD02.stream.before ctx))
    StreamCertificates.traceSegmentD02_owned (by decide)
  have endpoint : streamCfg (Λ := Λ) ((StreamCertificates.traceSegmentD02 12).reached
      (StreamMachine.frontEndRegisterEquiv (clean value)) (streamContext dirtyD02.stream.before ctx)) =
    cfg (some (phaseLabel (streamPhase (StreamMachine.applyPhase
      (MoveApplyMachine.positionPhase (.seek .left)))))) (clean value) dirtyD02PhysicalPathData ctx :=
    a_stream_phase_view_reinserts_all_the_front_end_complement_words (Λ := Λ)
      (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.seek .left)))
      dirtyD02.stream.before (StreamCertificates.traceSegmentD02 12).stores (clean value) ctx
  rw [endpoint] at source
  have first := dirtyD02_frontend_actual_local_run caller value ctx
  have joined := phase_step_localRun caller (dispatch_step caller dirtyD02.frontEndAfter
    (FrontEndMachine.reset (dirtyD02.fields.withUser value)) ctx)
  exact ⟨(LocalRun.trans caller (LocalRun.trans caller first joined) source).iterate caller, rfl, rfl, rfl⟩

theorem dirtyD02_actual_failure_has_already_consumed_the_failing_path_head
    (value : R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (dirtyD02.toClosedFixture.start value ctx) 272
      (cfg (some (phaseLabel (streamPhase (StreamMachine.applyPhase
        (MoveApplyMachine.positionPhase .dropPending))))) (clean value) dirtyD02ConsumedFailingHeadData ctx) ∧
    dirtyD02ConsumedFailingHeadData.path = [.right, .left, .right] ∧
    dirtyD02ConsumedFailingHeadData.sourceTree = [0, 1, 0, 1, 0, 0] ∧
    dirtyD02ConsumedFailingHeadData.treeReverse = [1] := by
  let localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R := fun _ => .halt
  have source := a_literal_stream_prefix_is_an_actual_common_carrier_prefix caller
    StreamCertificates.traceSegmentD02 18 14 dirtyD02.stream.before (clean value) ctx localCaller rfl
    (StreamCertificates.traceSegmentD02_steps localCaller
      (StreamMachine.frontEndRegisterEquiv (clean value)) (streamContext dirtyD02.stream.before ctx))
    StreamCertificates.traceSegmentD02_owned (by decide)
  have endpoint : streamCfg (Λ := Λ) ((StreamCertificates.traceSegmentD02 14).reached
      (StreamMachine.frontEndRegisterEquiv (clean value)) (streamContext dirtyD02.stream.before ctx)) =
    cfg (some (phaseLabel (streamPhase (StreamMachine.applyPhase
      (MoveApplyMachine.positionPhase .dropPending))))) (clean value) dirtyD02ConsumedFailingHeadData ctx :=
    a_stream_phase_view_reinserts_all_the_front_end_complement_words (Λ := Λ)
      (StreamMachine.applyPhase (MoveApplyMachine.positionPhase .dropPending))
      dirtyD02.stream.before (StreamCertificates.traceSegmentD02 14).stores (clean value) ctx
  rw [endpoint] at source
  have first := dirtyD02_frontend_actual_local_run caller value ctx
  have joined := phase_step_localRun caller (dispatch_step caller dirtyD02.frontEndAfter
    (FrontEndMachine.reset (dirtyD02.fields.withUser value)) ctx)
  exact ⟨(LocalRun.trans caller (LocalRun.trans caller first joined) source).iterate caller, rfl, rfl, rfl⟩

end LiteralDirtyPhysicalPaths

/-! ## Every positive closed fixture has its fixed complete endpoint and attained peak -/

theorem all_81_positive_closed_cases_have_their_actual_first_halt_and_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : Λ → Statement Γ Λ R) (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ fixture ∈ allClosedCases, fixture.Expected (step caller) value ctx := by
  intro fixture member
  simp only [allClosedCases, rawCases, partialClearCases, emitCases, joinCases, dirtyFrontEndCases,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have checked := emptyRawFixture_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := truncatedPrefixFixture_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawF03_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawF04_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawF05_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawF06_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawF07_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawF08_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawI01_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawI02_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawI03_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawI04_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawI05_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawI06_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawI07_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawC01_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawC02_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawC03_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV01_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV02_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV03_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV04_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV05_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV06_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV07_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV08_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV09_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV10_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV11_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV12_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV13_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV14_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV15_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV16_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV17_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := rawV18_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · exact cleanupC00_expected caller value ctx
  · exact cleanupC00E_expected caller value ctx
  · exact cleanupC01_expected caller value ctx
  · exact cleanupC01E_expected caller value ctx
  · exact cleanupC02_expected caller value ctx
  · exact cleanupC02E_expected caller value ctx
  · exact cleanupC03_expected caller value ctx
  · exact cleanupC03E_expected caller value ctx
  · exact cleanupC04_expected caller value ctx
  · exact cleanupC04E_expected caller value ctx
  · exact cleanupC05_expected caller value ctx
  · exact cleanupC05E_expected caller value ctx
  · exact cleanupC06_expected caller value ctx
  · exact cleanupC06E_expected caller value ctx
  · exact cleanupC07_expected caller value ctx
  · exact cleanupC07E_expected caller value ctx
  · exact cleanupC08_expected caller value ctx
  · exact cleanupC08E_expected caller value ctx
  · exact cleanupC09_expected caller value ctx
  · exact cleanupC09E_expected caller value ctx
  · exact cleanupC10_expected caller value ctx
  · exact cleanupC10E_expected caller value ctx
  · exact cleanupC11_expected caller value ctx
  · exact cleanupC11E_expected caller value ctx
  · exact cleanupC12_expected caller value ctx
  · exact cleanupC12E_expected caller value ctx
  · exact cleanupC13_expected caller value ctx
  · exact cleanupC13E_expected caller value ctx
  · exact cleanupC14_expected caller value ctx
  · exact cleanupC14E_expected caller value ctx
  · exact cleanupC15_expected caller value ctx
  · exact cleanupC15E_expected caller value ctx
  · exact emitE00_expected caller value ctx
  · exact emitE01_expected caller value ctx
  · exact emitE02_expected caller value ctx
  · exact emitE03_expected caller value ctx
  · exact joinJ00_expected caller value ctx
  · exact joinJ01_expected caller value ctx
  · exact joinJ02_expected caller value ctx
  · exact joinJ03_expected caller value ctx
  · exact dirtyD00_expected caller value ctx
  · exact dirtyD01_expected caller value ctx
  · exact dirtyD02_expected caller value ctx
  · exact dirtyD03_expected caller value ctx
  · exact emptyCleanupFixture_expected caller value ctx

theorem the_fixed_84_records_keep_81_positive_runs_separate_from_the_three_liveness_domains :
    allClosedCases.length = 81 ∧ livenessCases.length = 3 ∧
    allClosedCases.length + livenessCases.length = 84 := ⟨rfl, rfl, rfl⟩

/-! ## Dirty component contracts retain every old reverse, output, pending and fuel word -/

namespace DirtyComponentConnections

open Resources.RotationCertificate.FrontEndStreamMachine.DirtyFrontEnd

theorem every_one_of_the_five_tree_phases_has_its_actual_complete_dirty_endpoint
    {D K Λ R : Type} {Γ : K → Type} [DecidableEq D] [DecidableEq K]
    (caller : TreeParserMachine.External D Λ → TreeParserMachine.Statement D Γ Λ R)
    (destination : D) (phase : TreeParserMachine.Phase) (data : TreeState D)
    (regs : TreeParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (TreeParserMachine.next caller)^[(treePhaseFinish destination phase data).steps]
      (some (treeCfg (some (TreeParserMachine.phaseLabel destination phase)) regs data ctx)) =
      some (treeCfg (some (TreeParserMachine.resultLabel destination
        (treePhaseFinish destination phase data).result)) (TreeParserMachine.reset regs)
        (treePhaseFinish destination phase data).data ctx) ∧
    0 < (treePhaseFinish destination phase data).steps ∧
    ∀ n, n < (treePhaseFinish destination phase data).steps → ∃ reached,
      (TreeParserMachine.next caller)^[n]
        (some (treeCfg (some (TreeParserMachine.phaseLabel destination phase)) regs data ctx)) =
      some reached ∧ TreeParserMachine.Owned reached.l :=
  ⟨treePhaseFinish_iterate caller destination phase data regs ctx,
    treePhaseFinish_steps_pos destination phase data,
    treePhaseFinish_owned_prefix caller destination phase data regs ctx⟩

theorem all_25_input_domains_have_the_actual_dirty_endpoint_and_strict_ownership
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : InputParserMachine.External Λ → InputParserMachine.Statement Γ Λ R)
    (phase : InputParserMachine.OwnedLabels) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (InputParserMachine.next caller)^[(inputPhaseFinish phase data).steps]
      (some (inputCfg (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)) =
      some (inputCfg (some (InputParserMachine.resultLabel (inputPhaseFinish phase data).result))
        (InputParserMachine.reset regs) (inputPhaseFinish phase data).data ctx) ∧
    ∀ n, n < (inputPhaseFinish phase data).steps → ∃ reached,
      (InputParserMachine.next caller)^[n]
        (some (inputCfg (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)) =
      some reached ∧ InputParserMachine.FullOwned reached.l :=
  ⟨inputPhaseFinish_iterate caller phase data regs ctx,
    inputPhaseFinish_owned_prefix caller phase data regs ctx⟩

theorem an_actual_dirty_input_first_boundary_fixes_its_count_and_entire_configuration
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : InputParserMachine.External Λ → InputParserMachine.Statement Γ Λ R)
    (phase : InputParserMachine.OwnedLabels) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : InputParserMachine.Cfg Γ Λ R)
    (executed : (InputParserMachine.next caller)^[n]
      (some (inputCfg (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)) = some reached)
    (outside : ¬ InputParserMachine.FullOwned reached.l)
    (earlier : ∀ j, j < n → ∃ actual,
      (InputParserMachine.next caller)^[j]
        (some (inputCfg (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)) = some actual ∧
      InputParserMachine.FullOwned actual.l) :
    n = (inputPhaseFinish phase data).steps ∧
      reached = inputCfg (some (InputParserMachine.resultLabel (inputPhaseFinish phase data).result))
        (InputParserMachine.reset regs) (inputPhaseFinish phase data).data ctx :=
  inputPhaseFinish_first_return_unique caller phase data regs ctx n reached executed outside earlier

section CompleteFrontEnd

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : FrontEndMachine.External Λ → FrontEndMachine.Statement Γ Λ R)

theorem all_36_front_end_domains_have_the_actual_complete_dirty_first_boundary
    (phase : FrontEndMachine.OwnedLabels) (data : FrontEndMachine.LocalData)
    (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (FrontEndMachine.next caller)^[frontEndPhaseSteps phase data]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)) =
      some (frontEndPhaseResult phase regs data ctx) ∧
    ¬ FrontEndMachine.Owned (frontEndPhaseResult (Λ := Λ) phase regs data ctx).l ∧
    0 < frontEndPhaseSteps phase data ∧
    ∀ n, n < frontEndPhaseSteps phase data → ∃ reached,
      (FrontEndMachine.next caller)^[n]
        (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)) =
      some reached ∧ FrontEndMachine.Owned reached.l :=
  ⟨front_end_phase_iterate caller phase data regs ctx,
    frontEndFinishCfg_not_owned (frontEndPhaseFinish phase data) regs ctx,
    frontEndPhaseSteps_pos phase data,
    front_end_phase_owned_prefix caller phase data regs ctx⟩

theorem the_front_end_canonical_boundary_is_exact_for_every_initial_configuration
    (start : FrontEndMachine.Cfg Γ Λ R) :
    (FrontEndMachine.next caller)^[frontEndRemainingSteps start] (some start) =
      some (frontEndFinalCfg start) ∧
    ¬ FrontEndMachine.Owned (frontEndFinalCfg start).l ∧
    ∀ n, n < frontEndRemainingSteps start → ∃ reached,
      (FrontEndMachine.next caller)^[n] (some start) = some reached ∧ FrontEndMachine.Owned reached.l :=
  ⟨front_end_cfg_iterate caller start, frontEndFinalCfg_not_owned start,
    (front_end_cfg_trace caller start).owned_prefix⟩

theorem the_front_end_first_boundary_converse_requires_actual_earlier_ownership
    (start reached : FrontEndMachine.Cfg Γ Λ R) (n : Nat)
    (executed : (FrontEndMachine.next caller)^[n] (some start) = some reached)
    (outside : ¬ FrontEndMachine.Owned reached.l)
    (earlier : ∀ j, j < n → ∃ actual,
      (FrontEndMachine.next caller)^[j] (some start) = some actual ∧ FrontEndMachine.Owned actual.l) :
    n = frontEndRemainingSteps start ∧ reached = frontEndFinalCfg start :=
  front_end_first_return_unique caller start reached n executed outside earlier

theorem an_actual_front_end_step_decreases_rank_and_preserves_the_entire_canonical_endpoint
    (before after : FrontEndMachine.Cfg Γ Λ R) (owned : FrontEndMachine.Owned before.l)
    (executed : FrontEndMachine.step caller before = some after) :
    frontEndRemainingSteps before = frontEndRemainingSteps after + 1 ∧
      frontEndFinalCfg before = frontEndFinalCfg after :=
  front_end_local_step_remaining caller owned executed

omit caller [DecidableEq K] in
theorem an_external_front_end_label_has_zero_rank_and_identity_boundary
    (start : FrontEndMachine.Cfg Γ Λ R) (outside : ¬ FrontEndMachine.Owned start.l) :
    frontEndRemainingSteps start = 0 ∧ frontEndFinalCfg start = start :=
  front_end_nonowned_identity start outside

theorem clean_front_end_entry_agrees_with_the_existing_public_runtime_and_endpoint
    (regs : FrontEndMachine.Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    frontEndRemainingSteps (FrontEndMachine.entry (Λ := Λ) regs raw ctx) = FrontEndMachine.runSteps raw ∧
    frontEndFinalCfg (FrontEndMachine.entry (Λ := Λ) regs raw ctx) =
      FrontEndMachine.resultCfg regs ctx (FrontEndMachine.sourceOutcome raw) :=
  front_end_clean_alignment (Λ := Λ) (fun _ => .halt) regs raw ctx

def frontEndPhaseExactTime (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (FrontEndMachine.step caller)
      (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)
      (some (frontEndPhaseResult phase regs data ctx)) (frontEndPhaseSteps phase data) :=
  frontEndPhaseInTime caller phase data regs ctx

def frontEndConfigurationExactTime (start : FrontEndMachine.Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (FrontEndMachine.step caller) start
      (some (frontEndFinalCfg start)) (frontEndRemainingSteps start) :=
  frontEndCfgInTime caller start

theorem front_end_type_valued_records_store_the_actual_exact_counts
    (phase : FrontEndMachine.OwnedLabels) (data : FrontEndMachine.LocalData)
    (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k))
    (start : FrontEndMachine.Cfg Γ Λ R) :
    (frontEndPhaseExactTime caller phase data regs ctx).steps = frontEndPhaseSteps phase data ∧
    (frontEndConfigurationExactTime caller start).steps = frontEndRemainingSteps start := ⟨rfl, rfl⟩

variable [Fintype K]

theorem an_actual_dirty_front_end_step_does_not_increase_its_full_physical_potential
    (before after : FrontEndMachine.Cfg Γ Λ R) (owned : FrontEndMachine.Owned before.l)
    (executed : FrontEndMachine.step caller before = some after) :
    frontEndPotential after ≤ frontEndPotential before :=
  front_end_local_step_potential caller owned executed

theorem one_front_end_prefix_witness_carries_rank_masks_frame_credit_and_the_final_endpoint
    (start : FrontEndMachine.Cfg Γ Λ R) (n : Nat) (bound : n ≤ frontEndRemainingSteps start) :
    ∃ reached, (FrontEndMachine.next caller)^[n] (some start) = some reached ∧
      frontEndRemainingSteps reached = frontEndRemainingSteps start - n ∧
      Relation.ReflTransGen (FrontEndLocalStep caller) start reached ∧
      (n < frontEndRemainingSteps start ↔ FrontEndMachine.Owned reached.l) ∧
      (n = 0 → reached = start) ∧
      reached.var = frontEndRegistersAt start n ∧
      reached.var.2.2 = start.var.2.2 ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
      frontEndPotential reached ≤ frontEndPotential start ∧
      FrontEndMachine.stackCells reached ≤ frontEndPotential start ∧
      frontEndFinalCfg reached = frontEndFinalCfg start ∧
      (n = frontEndRemainingSteps start → reached = frontEndFinalCfg start) :=
  front_end_owned_prefix caller start n bound

theorem a_dirty_front_end_phase_has_one_witness_for_its_literal_mask_schedule_and_space
    (phase : FrontEndMachine.OwnedLabels) (data : FrontEndMachine.LocalData)
    (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ frontEndPhaseSteps phase data) :
    ∃ reached : FrontEndMachine.Cfg Γ Λ R,
      (FrontEndMachine.next caller)^[n]
        (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)) =
      some reached ∧ reached.var = frontEndPhaseRegisters phase data regs n ∧
      reached.var.2.2 = regs.2.2 ∧ (∀ k, reached.stk (.inr k) = ctx k) ∧
      FrontEndMachine.stackCells reached ≤ FrontEndMachine.localCells data +
        frontEndPhaseCredit phase data + FrontEndMachine.contextCells ctx ∧
      (n < frontEndPhaseSteps phase data ↔ FrontEndMachine.Owned reached.l) ∧
      (n = 0 → reached = FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx) ∧
      (n = frontEndPhaseSteps phase data → reached = frontEndPhaseResult phase regs data ctx) :=
  front_end_phase_shared_prefix caller phase data regs ctx n bound

end CompleteFrontEnd
end DirtyComponentConnections


end Examples.RotationCertificateFrontEndStreamMachine
