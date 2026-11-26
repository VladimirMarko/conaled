import Examples.RotationCertificateFrontEndStreamMachine.Package

/-!
# RotationCertificateFrontEndStreamMachine: DirtyExecution
-/

namespace Examples.RotationCertificateFrontEndStreamMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.FrontEndStreamMachine

/-! ## Dirty FrontEnd and dispatch fixtures, composed through actual stages -/

def branchRawData (raw : Bits) (reverse path : List Branch) : LocalData :=
  { framedRaw := raw, moveReverse := reverse, path := path }

def branchOutcomeData (outcome : FrontEndMachine.Outcome) (reverse path : List Branch) : LocalData :=
  { frontEndOutcomeData outcome with moveReverse := reverse, path := path }

section DirtyFrontEndConnections

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

omit caller [DecidableEq K] in
theorem the_front_end_entry_view_preserves_arbitrary_old_branch_words
    (raw : Bits) (reverse path : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    frontEndCfg (FrontEndMachine.entry (Λ := FrontEndCallerLabel Λ) regs raw
      (frontEndContext (branchRawData raw reverse path) ctx)) =
      cfg (some (phaseLabel rawEntryPhase)) regs (branchRawData raw reverse path) ctx :=
  frontEndCfg_view (some (FrontEndMachine.framerLabel .scanPrefix)) regs
    (branchRawData raw reverse path) ctx

omit caller [DecidableEq K] in
theorem the_front_end_result_view_preserves_arbitrary_old_branch_words
    (outcome : FrontEndMachine.Outcome) (raw : Bits) (reverse path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    frontEndCfg (FrontEndMachine.resultCfg (Λ := FrontEndCallerLabel Λ) regs
      (frontEndContext (branchRawData raw reverse path) ctx) outcome) =
      cfg (some (phaseLabel (frontEndOutcomePhase outcome)))
        (frontEndOutcomeRegisters outcome regs) (branchOutcomeData outcome reverse path) ctx := by
  cases outcome with
  | frameFailure =>
      exact frontEndCfg_view (some FrontEndMachine.rejectLabel) (FrontEndMachine.resetFramer regs)
        (branchOutcomeData .frameFailure reverse path) ctx
  | inputDecodeFailure cert =>
      exact frontEndCfg_view (some FrontEndMachine.rejectLabel) (FrontEndMachine.afterInputDecoder regs)
        (branchOutcomeData (.inputDecodeFailure cert) reverse path) ctx
  | inputParseFailure input cert =>
      exact frontEndCfg_view (some FrontEndMachine.rejectLabel) (FrontEndMachine.reset regs)
        (branchOutcomeData (.inputParseFailure input cert) reverse path) ctx
  | certificateDecodeFailure source target fuel =>
      exact frontEndCfg_view (some FrontEndMachine.rejectLabel) (FrontEndMachine.reset regs)
        (branchOutcomeData (.certificateDecodeFailure source target fuel) reverse path) ctx
  | success source target fuel cert =>
      exact frontEndCfg_view (some FrontEndMachine.dispatchLabel) (FrontEndMachine.reset regs)
        (branchOutcomeData (.success source target fuel cert) reverse path) ctx

theorem actual_front_end_processing_does_not_clean_the_old_branch_words
    (raw : Bits) (reverse path : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (FrontEndMachine.runSteps raw)
      (cfg (some (phaseLabel rawEntryPhase)) regs (branchRawData raw reverse path) ctx)
      (cfg (some (phaseLabel (frontEndOutcomePhase (FrontEndMachine.sourceOutcome raw))))
        (frontEndOutcomeRegisters (FrontEndMachine.sourceOutcome raw) regs)
        (branchOutcomeData (FrontEndMachine.sourceOutcome raw) reverse path) ctx) := by
  have source := FrontEndMachine.run_source_trace
    (Γ := StreamMachine.FrontEndAddedAlphabet Γ) (Λ := FrontEndCallerLabel Λ)
    (fun _ => .halt) regs raw (frontEndContext (branchRawData raw reverse path) ctx)
  have actual := front_end_trace_localRun caller (fun _ => .halt) source
  rw [the_front_end_entry_view_preserves_arbitrary_old_branch_words,
    the_front_end_result_view_preserves_arbitrary_old_branch_words] at actual
  exact actual

theorem dirtyD00_frontend_actual_local_run (value : R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller dirtyD00.frontEndTicks (dirtyD00.toClosedFixture.start value ctx)
      (cfg (some (phaseLabel dispatchPhase))
        (FrontEndMachine.afterInputDecoder (dirtyD00.fields.withUser value)) dirtyD00.frontEndAfter ctx) := by
  convert front_end_phase_localRun caller (.inr (.inr (.inr .emit))) dirtyD00.before
    (dirtyD00.fields.withUser value) ctx using 1 <;> rfl

theorem dirtyD01_frontend_actual_local_run (value : R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller dirtyD01.frontEndTicks (dirtyD01.toClosedFixture.start value ctx)
      (cfg (some (phaseLabel dispatchPhase))
        (FrontEndMachine.reset (dirtyD01.fields.withUser value)) dirtyD01.frontEndAfter ctx) := by
  convert actual_front_end_processing_does_not_clean_the_old_branch_words caller
    dirtyD01.before.framedRaw dirtyD01.before.moveReverse dirtyD01.before.path
    (dirtyD01.fields.withUser value) ctx using 1 <;> rfl

theorem dirtyD02_frontend_actual_local_run (value : R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller dirtyD02.frontEndTicks (dirtyD02.toClosedFixture.start value ctx)
      (cfg (some (phaseLabel dispatchPhase))
        (FrontEndMachine.reset (dirtyD02.fields.withUser value)) dirtyD02.frontEndAfter ctx) := by
  convert actual_front_end_processing_does_not_clean_the_old_branch_words caller
    dirtyD02.before.framedRaw dirtyD02.before.moveReverse dirtyD02.before.path
    (dirtyD02.fields.withUser value) ctx using 1 <;> rfl

theorem dirtyD03_frontend_actual_local_run (value : R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller dirtyD03.frontEndTicks (dirtyD03.toClosedFixture.start value ctx)
      (cfg (some (phaseLabel dispatchPhase))
        (FrontEndMachine.reset (dirtyD03.fields.withUser value)) dirtyD03.frontEndAfter ctx) := by
  convert actual_front_end_processing_does_not_clean_the_old_branch_words caller
    dirtyD03.before.framedRaw dirtyD03.before.moveReverse dirtyD03.before.path
    (dirtyD03.fields.withUser value) ctx using 1 <;> rfl

theorem dispatch_stream_and_cleanup_preserve_the_actual_full_endpoint
    (D output : LocalData) (bit : Bool) (ticks : Nat) (regs : Registers R)
    (ctx : ∀ k, List (Γ k))
    (streamed : LocalRun caller ticks
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase))) (fullReset regs) D ctx)
      (cfg (some (phaseLabel (resultPhase bit))) (fullReset regs) output ctx)) :
    LocalRun caller (1 + ticks + 1 + cleanupSteps 0 output)
      (cfg (some (phaseLabel dispatchPhase)) regs D ctx)
      (cfg none (fullReset regs) (cleanupData 0 bit output) ctx) := by
  have head := phase_step_localRun caller (dispatch_step caller D regs ctx)
  have before := LocalRun.trans caller head streamed
  have answerJoin := phase_step_localRun caller (result_step caller bit output (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 output (answerRegisters bit (fullReset regs)) ctx
  have complete := LocalRun.trans caller (LocalRun.trans caller before answerJoin) tail
  simpa only [fullReset_answerRegisters, fullReset_fullReset, answer_answerRegisters] using complete

theorem joinJ03_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    joinJ03.toClosedFixture.RunExpected (step caller) value ctx := by
  have actual := dispatch_stream_and_cleanup_preserve_the_actual_full_endpoint caller
    joinJ03.before joinJ03.before true 4 (joinJ03.fields.withUser value) ctx
    (joinJ03_stream_actual_local_run caller (joinJ03.fields.withUser value) ctx)
  exact first_halt_of_actual_local_run caller actual rfl

theorem dirtyD00_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    dirtyD00.toClosedFixture.RunExpected (step caller) value ctx := by
  have first := dirtyD00_frontend_actual_local_run caller value ctx
  have tail := dispatch_stream_and_cleanup_preserve_the_actual_full_endpoint caller
    dirtyD00.stream.before dirtyD00.stream.after dirtyD00.stream.result dirtyD00.stream.ticks
    (FrontEndMachine.afterInputDecoder (dirtyD00.fields.withUser value)) ctx
    (dirtyD00_stream_actual_local_run caller (dirtyD00.fields.withUser value) ctx)
  exact first_halt_of_actual_local_run caller (LocalRun.trans caller first tail) rfl

theorem dirtyD01_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    dirtyD01.toClosedFixture.RunExpected (step caller) value ctx := by
  have first := dirtyD01_frontend_actual_local_run caller value ctx
  have tail := dispatch_stream_and_cleanup_preserve_the_actual_full_endpoint caller
    dirtyD01.stream.before dirtyD01.stream.after dirtyD01.stream.result dirtyD01.stream.ticks
    (FrontEndMachine.reset (dirtyD01.fields.withUser value)) ctx
    (dirtyD01_stream_actual_local_run caller (dirtyD01.fields.withUser value) ctx)
  exact first_halt_of_actual_local_run caller (LocalRun.trans caller first tail) rfl

theorem dirtyD02_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    dirtyD02.toClosedFixture.RunExpected (step caller) value ctx := by
  have first := dirtyD02_frontend_actual_local_run caller value ctx
  have tail := dispatch_stream_and_cleanup_preserve_the_actual_full_endpoint caller
    dirtyD02.stream.before dirtyD02.stream.after dirtyD02.stream.result dirtyD02.stream.ticks
    (FrontEndMachine.reset (dirtyD02.fields.withUser value)) ctx
    (dirtyD02_stream_actual_local_run caller (dirtyD02.fields.withUser value) ctx)
  exact first_halt_of_actual_local_run caller (LocalRun.trans caller first tail) rfl

theorem dirtyD03_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    dirtyD03.toClosedFixture.RunExpected (step caller) value ctx := by
  have first := dirtyD03_frontend_actual_local_run caller value ctx
  have tail := dispatch_stream_and_cleanup_preserve_the_actual_full_endpoint caller
    dirtyD03.stream.before dirtyD03.stream.after dirtyD03.stream.result dirtyD03.stream.ticks
    (FrontEndMachine.reset (dirtyD03.fields.withUser value)) ctx
    (dirtyD03_stream_actual_local_run caller (dirtyD03.fields.withUser value) ctx)
  exact first_halt_of_actual_local_run caller (LocalRun.trans caller first tail) rfl

end DirtyFrontEndConnections

section DirtyFrontEndPhysicalPeaks

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : Λ → Statement Γ Λ R)

theorem front_end_with_old_branch_words_has_its_attained_initial_mass_as_peak
    (raw : Bits) (reverse path : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller)
      (cfg (some (phaseLabel rawEntryPhase)) regs (branchRawData raw reverse path) ctx)
      (FrontEndMachine.runSteps raw)
      (raw.length + reverse.length + path.length + externalCells ctx) := by
  let localCaller : FrontEndMachine.External (FrontEndCallerLabel Λ) → FrontEndStatement Γ Λ R := fun _ => .halt
  let localContext := frontEndContext (branchRawData raw reverse path) ctx
  let start := FrontEndMachine.entry (Λ := FrontEndCallerLabel Λ) regs raw localContext
  have trace := FrontEndMachine.run_source_trace localCaller regs raw localContext
  constructor
  · intro n bound reached executed
    obtain ⟨middle, run, _⟩ := FrontEndMachine.run_prefix localCaller regs raw localContext n bound
    have mapped := front_end_prefix_transport caller localCaller n start
      (fun j smaller => trace.owned_prefix j (Nat.lt_of_lt_of_le smaller bound))
    rw [run, the_front_end_entry_view_preserves_arbitrary_old_branch_words] at mapped
    have same : reached = frontEndCfg middle := Option.some.inj (executed.symm.trans mapped)
    subst reached
    change stackCells (frontEndCfg middle) ≤ _
    rw [stackCells_frontEndCfg]
    have bounded := FrontEndMachine.prefix_stackCells_le localCaller regs raw localContext n bound middle run
    rw [frontEndContext_cells] at bounded
    change FrontEndMachine.stackCells middle ≤ raw.length + (reverse.length + path.length + externalCells ctx) at bounded
    omega
  · refine ⟨0, cfg (some (phaseLabel rawEntryPhase)) regs (branchRawData raw reverse path) ctx,
      Nat.zero_le _, rfl, ?_⟩
    rw [actual_physical_cells_of_cfg]
    simp only [branchRawData, localCells, List.length_nil, Nat.add_zero]

theorem dirtyD00_frontend_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (dirtyD00.toClosedFixture.start value ctx)
      dirtyD00.frontEndTicks (22 + externalCells ctx) := by
  constructor
  · intro n bound reached executed
    have bounded := front_end_component_prefix_cells caller (.inr (.inr (.inr .emit)))
      dirtyD00.before (dirtyD00.fields.withUser value) ctx n bound reached executed
    exact bounded
  · refine ⟨0, dirtyD00.toClosedFixture.start value ctx, by decide, rfl, ?_⟩
    rw [ClosedFixture.start, actual_physical_cells_of_cfg]
    rfl

theorem dispatch_with_an_actual_stream_peak_has_the_composed_exact_peak
    (D output : LocalData) (bit : Bool) (ticks peak : Nat) (regs : Registers R)
    (ctx : ∀ k, List (Γ k))
    (streamed : LocalRun caller ticks
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase))) (fullReset regs) D ctx)
      (cfg (some (phaseLabel (resultPhase bit))) (fullReset regs) output ctx))
    (streamPeak : ExactPeak (step caller)
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase))) (fullReset regs) D ctx)
      ticks (peak + externalCells ctx)) :
    ExactPeak (step caller) (cfg (some (phaseLabel dispatchPhase)) regs D ctx)
      (1 + (ticks + (1 + cleanupSteps 0 output)))
      (max (localCells D + externalCells ctx)
        (max (peak + externalCells ctx) (max (localCells output) 1 + externalCells ctx))) := by
  have first := one_step_with_unchanged_words_has_its_initial_mass_as_peak caller
    (dispatch_step caller D regs ctx) (by rw [actual_physical_cells_of_cfg, actual_physical_cells_of_cfg])
  have last := boolean_join_has_the_exact_cleanup_peak caller bit output (fullReset regs) ctx
  have suffix := exact_peaks_compose caller (streamed.iterate caller) streamPeak last
  have dispatchRun : Runs (step caller)
      (cfg (some (phaseLabel dispatchPhase)) regs D ctx) 1
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase))) (fullReset regs) D ctx) := by
    simpa only [Runs, Function.iterate_one, Option.bind_some] using dispatch_step caller D regs ctx
  have whole := exact_peaks_compose caller dispatchRun first suffix
  rw [actual_physical_cells_of_cfg] at whole
  exact whole

theorem joinJ03_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (joinJ03.toClosedFixture.start value ctx) joinJ03.ticks
      (joinJ03.peak + externalCells ctx) := by
  have whole := dispatch_with_an_actual_stream_peak_has_the_composed_exact_peak caller
    joinJ03.before joinJ03.before true 4 15 (joinJ03.fields.withUser value) ctx
    (joinJ03_stream_actual_local_run caller (joinJ03.fields.withUser value) ctx)
    (joinJ03_stream_actual_exact_peak caller (joinJ03.fields.withUser value) ctx)
  change ExactPeak (step caller)
    (cfg (some (phaseLabel dispatchPhase)) (joinJ03.fields.withUser value) joinJ03.before ctx)
    38 (15 + externalCells ctx)
  simpa only [cleanupSteps_zero, show localCells joinJ03.before = 15 from rfl, Nat.max_self,
    show max 15 1 = 15 from rfl] using whole

theorem joinJ03_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    joinJ03.toClosedFixture.Expected (step caller) value ctx :=
  ⟨joinJ03_actual_first_halt caller value ctx, joinJ03_actual_exact_peak caller value ctx⟩

end DirtyFrontEndPhysicalPeaks

/-! The dirty literal peaks use their actual component bounds and attained witnesses. -/

section LiteralDirtyPeaks
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : Λ → Statement Γ Λ R)

theorem dirtyD00_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (dirtyD00.toClosedFixture.start value ctx) dirtyD00.ticks
      (dirtyD00.peak + externalCells ctx) := by
  have first := dirtyD00_frontend_actual_local_run caller value ctx
  have firstPeak := dirtyD00_frontend_actual_exact_peak caller value ctx
  have tail := dispatch_with_an_actual_stream_peak_has_the_composed_exact_peak caller
    dirtyD00.stream.before dirtyD00.stream.after dirtyD00.stream.result dirtyD00.stream.ticks 22
    (FrontEndMachine.afterInputDecoder (dirtyD00.fields.withUser value)) ctx
    (dirtyD00_stream_actual_local_run caller (dirtyD00.fields.withUser value) ctx)
    (dirtyD00_stream_actual_exact_peak caller (dirtyD00.fields.withUser value) ctx)
  have whole := exact_peaks_compose caller (first.iterate caller) firstPeak tail
  have peakEquation : max (22 + externalCells ctx)
      (max (localCells dirtyD00.stream.before + externalCells ctx)
        (max (22 + externalCells ctx) (max (localCells dirtyD00.stream.after) 1 + externalCells ctx))) =
      dirtyD00.peak + externalCells ctx := by
    change max (22 + externalCells ctx)
      (max (22 + externalCells ctx) (max (22 + externalCells ctx) (max 8 1 + externalCells ctx))) =
      22 + externalCells ctx
    omega
  rw [peakEquation] at whole
  exact whole

theorem dirtyD00_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    dirtyD00.toClosedFixture.Expected (step caller) value ctx :=
  ⟨dirtyD00_actual_first_halt caller value ctx, dirtyD00_actual_exact_peak caller value ctx⟩

theorem dirtyD01_frontend_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (dirtyD01.toClosedFixture.start value ctx)
      dirtyD01.frontEndTicks (123 + externalCells ctx) :=
  front_end_with_old_branch_words_has_its_attained_initial_mass_as_peak caller
    dirtyD01.before.framedRaw dirtyD01.before.moveReverse dirtyD01.before.path
    (dirtyD01.fields.withUser value) ctx

theorem dirtyD01_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (dirtyD01.toClosedFixture.start value ctx) dirtyD01.ticks
      (dirtyD01.peak + externalCells ctx) := by
  have first := dirtyD01_frontend_actual_local_run caller value ctx
  have firstPeak := dirtyD01_frontend_actual_exact_peak caller value ctx
  have tail := dispatch_with_an_actual_stream_peak_has_the_composed_exact_peak caller
    dirtyD01.stream.before dirtyD01.stream.after dirtyD01.stream.result dirtyD01.stream.ticks 15
    (FrontEndMachine.reset (dirtyD01.fields.withUser value)) ctx
    (dirtyD01_stream_actual_local_run caller (dirtyD01.fields.withUser value) ctx)
    (dirtyD01_stream_actual_exact_peak caller (dirtyD01.fields.withUser value) ctx)
  have whole := exact_peaks_compose caller (first.iterate caller) firstPeak tail
  have peakEquation : max (123 + externalCells ctx)
      (max (localCells dirtyD01.stream.before + externalCells ctx)
        (max (15 + externalCells ctx) (max (localCells dirtyD01.stream.after) 1 + externalCells ctx))) =
      dirtyD01.peak + externalCells ctx := by
    change max (123 + externalCells ctx)
      (max (15 + externalCells ctx) (max (15 + externalCells ctx) (max 11 1 + externalCells ctx))) =
      123 + externalCells ctx
    omega
  rw [peakEquation] at whole
  exact whole

theorem dirtyD01_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    dirtyD01.toClosedFixture.Expected (step caller) value ctx :=
  ⟨dirtyD01_actual_first_halt caller value ctx, dirtyD01_actual_exact_peak caller value ctx⟩

theorem dirtyD02_frontend_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (dirtyD02.toClosedFixture.start value ctx)
      dirtyD02.frontEndTicks (161 + externalCells ctx) := by
  have peak := front_end_with_old_branch_words_has_its_attained_initial_mass_as_peak caller
    dirtyD02.before.framedRaw dirtyD02.before.moveReverse dirtyD02.before.path
    (dirtyD02.fields.withUser value) ctx
  have rawLength : dirtyD02.before.framedRaw.length = 157 := by
    change rawV13.raw.length = 157
    norm_num [rawV13]
  have reverseLength : dirtyD02.before.moveReverse.length = 2 := rfl
  have pathLength : dirtyD02.before.path.length = 2 := rfl
  have mass : dirtyD02.before.framedRaw.length + dirtyD02.before.moveReverse.length +
      dirtyD02.before.path.length = 161 := by
    rw [rawLength, reverseLength, pathLength]
  rw [mass] at peak
  exact peak

theorem dirtyD02_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (dirtyD02.toClosedFixture.start value ctx) dirtyD02.ticks
      (dirtyD02.peak + externalCells ctx) := by
  have first := dirtyD02_frontend_actual_local_run caller value ctx
  have firstPeak := dirtyD02_frontend_actual_exact_peak caller value ctx
  have tail := dispatch_with_an_actual_stream_peak_has_the_composed_exact_peak caller
    dirtyD02.stream.before dirtyD02.stream.after dirtyD02.stream.result dirtyD02.stream.ticks 22
    (FrontEndMachine.reset (dirtyD02.fields.withUser value)) ctx
    (dirtyD02_stream_actual_local_run caller (dirtyD02.fields.withUser value) ctx)
    (dirtyD02_stream_actual_exact_peak caller (dirtyD02.fields.withUser value) ctx)
  have whole := exact_peaks_compose caller (first.iterate caller) firstPeak tail
  have peakEquation : max (161 + externalCells ctx)
      (max (localCells dirtyD02.stream.before + externalCells ctx)
        (max (22 + externalCells ctx) (max (localCells dirtyD02.stream.after) 1 + externalCells ctx))) =
      dirtyD02.peak + externalCells ctx := by
    change max (161 + externalCells ctx)
      (max (22 + externalCells ctx) (max (22 + externalCells ctx) (max 18 1 + externalCells ctx))) =
      161 + externalCells ctx
    omega
  rw [peakEquation] at whole
  exact whole

theorem dirtyD02_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    dirtyD02.toClosedFixture.Expected (step caller) value ctx :=
  ⟨dirtyD02_actual_first_halt caller value ctx, dirtyD02_actual_exact_peak caller value ctx⟩

theorem dirtyD03_frontend_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (dirtyD03.toClosedFixture.start value ctx)
      dirtyD03.frontEndTicks (121 + externalCells ctx) :=
  front_end_with_old_branch_words_has_its_attained_initial_mass_as_peak caller
    dirtyD03.before.framedRaw dirtyD03.before.moveReverse dirtyD03.before.path
    (dirtyD03.fields.withUser value) ctx

theorem dirtyD03_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (dirtyD03.toClosedFixture.start value ctx) dirtyD03.ticks
      (dirtyD03.peak + externalCells ctx) := by
  have first := dirtyD03_frontend_actual_local_run caller value ctx
  have firstPeak := dirtyD03_frontend_actual_exact_peak caller value ctx
  have tail := dispatch_with_an_actual_stream_peak_has_the_composed_exact_peak caller
    dirtyD03.stream.before dirtyD03.stream.after dirtyD03.stream.result dirtyD03.stream.ticks 13
    (FrontEndMachine.reset (dirtyD03.fields.withUser value)) ctx
    (dirtyD03_stream_actual_local_run caller (dirtyD03.fields.withUser value) ctx)
    (dirtyD03_stream_actual_exact_peak caller (dirtyD03.fields.withUser value) ctx)
  have whole := exact_peaks_compose caller (first.iterate caller) firstPeak tail
  have peakEquation : max (121 + externalCells ctx)
      (max (localCells dirtyD03.stream.before + externalCells ctx)
        (max (13 + externalCells ctx) (max (localCells dirtyD03.stream.after) 1 + externalCells ctx))) =
      dirtyD03.peak + externalCells ctx := by
    change max (121 + externalCells ctx)
      (max (13 + externalCells ctx) (max (13 + externalCells ctx) (max 1 1 + externalCells ctx))) =
      121 + externalCells ctx
    omega
  rw [peakEquation] at whole
  exact whole

theorem dirtyD03_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    dirtyD03.toClosedFixture.Expected (step caller) value ctx :=
  ⟨dirtyD03_actual_first_halt caller value ctx, dirtyD03_actual_exact_peak caller value ctx⟩

end LiteralDirtyPeaks

section LiteralDirtyIntermediateStates
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

theorem dirtyD00_actual_intermediate_states (value : R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (dirtyD00.toClosedFixture.start value ctx) dirtyD00.frontEndTicks
      (cfg (some (phaseLabel dispatchPhase)) (FrontEndMachine.afterInputDecoder (dirtyD00.fields.withUser value))
        dirtyD00.frontEndAfter ctx) ∧
    Runs (step caller) (dirtyD00.toClosedFixture.start value ctx) (dirtyD00.frontEndTicks + 1)
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
        (clean value) dirtyD00.stream.before ctx) ∧
    Runs (step caller) (dirtyD00.toClosedFixture.start value ctx)
      (dirtyD00.frontEndTicks + 1 + dirtyD00.stream.ticks)
      (cfg (some (phaseLabel (resultPhase dirtyD00.stream.result)))
        (clean value) dirtyD00.stream.after ctx) ∧
    Runs (step caller) (dirtyD00.toClosedFixture.start value ctx)
      (dirtyD00.frontEndTicks + 1 + dirtyD00.stream.ticks + 1)
      (cfg (some (clearLabel 0)) (answerRegisters dirtyD00.stream.result (clean value))
        dirtyD00.stream.after ctx) := by
  have first := dirtyD00_frontend_actual_local_run caller value ctx
  have join := phase_step_localRun caller (dispatch_step caller dirtyD00.frontEndAfter
    (FrontEndMachine.afterInputDecoder (dirtyD00.fields.withUser value)) ctx)
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before
    (dirtyD00_stream_actual_local_run caller (dirtyD00.fields.withUser value) ctx)
  have tail := LocalRun.trans caller streamed (phase_step_localRun caller
    (result_step caller dirtyD00.stream.result dirtyD00.stream.after (clean value) ctx))
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, tail.iterate caller⟩

theorem dirtyD01_actual_intermediate_states (value : R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (dirtyD01.toClosedFixture.start value ctx) dirtyD01.frontEndTicks
      (cfg (some (phaseLabel dispatchPhase)) (FrontEndMachine.reset (dirtyD01.fields.withUser value))
        dirtyD01.frontEndAfter ctx) ∧
    Runs (step caller) (dirtyD01.toClosedFixture.start value ctx) (dirtyD01.frontEndTicks + 1)
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
        (clean value) dirtyD01.stream.before ctx) ∧
    Runs (step caller) (dirtyD01.toClosedFixture.start value ctx)
      (dirtyD01.frontEndTicks + 1 + dirtyD01.stream.ticks)
      (cfg (some (phaseLabel (resultPhase dirtyD01.stream.result)))
        (clean value) dirtyD01.stream.after ctx) ∧
    Runs (step caller) (dirtyD01.toClosedFixture.start value ctx)
      (dirtyD01.frontEndTicks + 1 + dirtyD01.stream.ticks + 1)
      (cfg (some (clearLabel 0)) (answerRegisters dirtyD01.stream.result (clean value))
        dirtyD01.stream.after ctx) := by
  have first := dirtyD01_frontend_actual_local_run caller value ctx
  have join := phase_step_localRun caller (dispatch_step caller dirtyD01.frontEndAfter
    (FrontEndMachine.reset (dirtyD01.fields.withUser value)) ctx)
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before
    (dirtyD01_stream_actual_local_run caller (dirtyD01.fields.withUser value) ctx)
  have tail := LocalRun.trans caller streamed (phase_step_localRun caller
    (result_step caller dirtyD01.stream.result dirtyD01.stream.after (clean value) ctx))
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, tail.iterate caller⟩

theorem dirtyD02_actual_intermediate_states (value : R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (dirtyD02.toClosedFixture.start value ctx) dirtyD02.frontEndTicks
      (cfg (some (phaseLabel dispatchPhase)) (FrontEndMachine.reset (dirtyD02.fields.withUser value))
        dirtyD02.frontEndAfter ctx) ∧
    Runs (step caller) (dirtyD02.toClosedFixture.start value ctx) (dirtyD02.frontEndTicks + 1)
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
        (clean value) dirtyD02.stream.before ctx) ∧
    Runs (step caller) (dirtyD02.toClosedFixture.start value ctx)
      (dirtyD02.frontEndTicks + 1 + dirtyD02.stream.ticks)
      (cfg (some (phaseLabel (resultPhase dirtyD02.stream.result)))
        (clean value) dirtyD02.stream.after ctx) ∧
    Runs (step caller) (dirtyD02.toClosedFixture.start value ctx)
      (dirtyD02.frontEndTicks + 1 + dirtyD02.stream.ticks + 1)
      (cfg (some (clearLabel 0)) (answerRegisters dirtyD02.stream.result (clean value))
        dirtyD02.stream.after ctx) := by
  have first := dirtyD02_frontend_actual_local_run caller value ctx
  have join := phase_step_localRun caller (dispatch_step caller dirtyD02.frontEndAfter
    (FrontEndMachine.reset (dirtyD02.fields.withUser value)) ctx)
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before
    (dirtyD02_stream_actual_local_run caller (dirtyD02.fields.withUser value) ctx)
  have tail := LocalRun.trans caller streamed (phase_step_localRun caller
    (result_step caller dirtyD02.stream.result dirtyD02.stream.after (clean value) ctx))
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, tail.iterate caller⟩

theorem dirtyD03_actual_intermediate_states (value : R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (dirtyD03.toClosedFixture.start value ctx) dirtyD03.frontEndTicks
      (cfg (some (phaseLabel dispatchPhase)) (FrontEndMachine.reset (dirtyD03.fields.withUser value))
        dirtyD03.frontEndAfter ctx) ∧
    Runs (step caller) (dirtyD03.toClosedFixture.start value ctx) (dirtyD03.frontEndTicks + 1)
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
        (clean value) dirtyD03.stream.before ctx) ∧
    Runs (step caller) (dirtyD03.toClosedFixture.start value ctx)
      (dirtyD03.frontEndTicks + 1 + dirtyD03.stream.ticks)
      (cfg (some (phaseLabel (resultPhase dirtyD03.stream.result)))
        (clean value) dirtyD03.stream.after ctx) ∧
    Runs (step caller) (dirtyD03.toClosedFixture.start value ctx)
      (dirtyD03.frontEndTicks + 1 + dirtyD03.stream.ticks + 1)
      (cfg (some (clearLabel 0)) (answerRegisters dirtyD03.stream.result (clean value))
        dirtyD03.stream.after ctx) := by
  have first := dirtyD03_frontend_actual_local_run caller value ctx
  have join := phase_step_localRun caller (dispatch_step caller dirtyD03.frontEndAfter
    (FrontEndMachine.reset (dirtyD03.fields.withUser value)) ctx)
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before
    (dirtyD03_stream_actual_local_run caller (dirtyD03.fields.withUser value) ctx)
  have tail := LocalRun.trans caller streamed (phase_step_localRun caller
    (result_step caller dirtyD03.stream.result dirtyD03.stream.after (clean value) ctx))
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, tail.iterate caller⟩

end LiteralDirtyIntermediateStates

/-! ## Live halt, outer none, and an actually allocating external caller -/

def allocatingExternal : Nat → Statement IndependentAlphabet Nat Bool :=
  fun _ => .push (.inr (.inr (0 : Fin 2))) (fun _ => true) .halt

def haltingExternal : Nat → Statement IndependentAlphabet Nat Bool := fun _ => .halt

def reenteringExternal : Nat → Statement IndependentAlphabet Nat Bool :=
  fun _ => .goto (fun _ => clearLabel 0)

def allocationStart (value : Bool) : InfiniteLabelCfg :=
  cfg (some (callerLabel 42)) (stale value) cleanupC00.before ordinaryContext

def allocationFinish (value : Bool) : InfiniteLabelCfg :=
  cfg none (stale value) cleanupC00.before
    (independentWords [true, true, false, true] [11, 15])

theorem the_literal_live_halt_preserves_every_dirty_field_at_zero
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : Λ → Statement Γ Λ R) (value : R) (ctx : ∀ k, List (Γ k)) :
    FirstHalt (step caller) (cfg none (staleFields.withUser value) cleanupC00.before ctx) 0
      (cfg none (staleFields.withUser value) cleanupC00.before ctx) ∧
    ExactPeak (step caller) (cfg none (staleFields.withUser value) cleanupC00.before ctx) 0
      (32 + externalCells ctx) ∧
    next caller (some (cfg none (staleFields.withUser value) cleanupC00.before ctx)) = none := by
  have first := live_halt_has_zero_first_halt_and_keeps_all_dirty_fields caller
    cleanupC00.before (staleFields.withUser value) ctx
  have cells : physicalCells (cfg (Λ := Λ) none (staleFields.withUser value) cleanupC00.before ctx) =
      32 + externalCells ctx := by rw [actual_physical_cells_of_cfg]; rfl
  refine ⟨first.1, ⟨?_, ?_⟩, first.2⟩
  · intro n bound reached executed
    have zero : n = 0 := by omega
    subst n
    have same := Option.some.inj executed
    subst reached
    exact Nat.le_of_eq cells
  · exact ⟨0, cfg none (staleFields.withUser value) cleanupC00.before ctx, by omega, rfl, cells⟩

theorem the_literal_outer_none_has_zero_optional_rank_and_stays_none
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : Λ → Statement Γ Λ R) (n : Nat) :
    stateRemainingSteps (Γ := Γ) (Λ := Λ) (R := R) none = 0 ∧
    (next caller)^[n] none = none := ⟨rfl, outer_none_stays_none caller n⟩

theorem the_literal_external_allocator_executes_its_real_push_without_resetting_the_registers
    (value : Bool) : step allocatingExternal (allocationStart value) = some (allocationFinish value) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => fin_cases k <;> rfl

theorem the_external_first_boundary_is_zero_even_though_the_caller_later_allocates
    (value : Bool) :
    FirstBoundary (step allocatingExternal) (allocationStart value) 0 (allocationStart value) ∧
    remainingSteps (allocationStart value) = 0 ∧ finalCfg (allocationStart value) = allocationStart value ∧
    Runs (step allocatingExternal) (allocationStart value) 1 (allocationFinish value) ∧
    physicalCells (allocationStart value) = 37 ∧ physicalCells (allocationFinish value) = 38 ∧
    ¬ physicalCells (allocationFinish value) ≤ physicalCells (allocationStart value) ∧
    next allocatingExternal (some (allocationFinish value)) = none := by
  have before : physicalCells (allocationStart value) = 37 := by
    rw [allocationStart, actual_physical_cells_of_cfg]
    rfl
  have after : physicalCells (allocationFinish value) = 38 := by
    rw [allocationFinish, actual_physical_cells_of_cfg]
    rfl
  refine ⟨external_first_boundary_is_zero_identity allocatingExternal 42 cleanupC00.before
    (stale value) ordinaryContext, rfl, rfl,
    the_literal_external_allocator_executes_its_real_push_without_resetting_the_registers value,
    before, after, ?_, rfl⟩
  rw [before, after]
  omega

theorem a_later_external_halt_does_not_satisfy_owned_first_halt
    (value : Bool) : ¬ FirstHalt (step allocatingExternal)
      (allocationStart value) 1 (allocationFinish value) := by
  intro alleged
  obtain ⟨reached, executed, owned⟩ := alleged.2.2 0 (by decide)
  have same := Option.some.inj executed
  subst reached
  exact not_owned_caller 42 owned

theorem the_three_concrete_external_bodies_are_irrelevant_from_every_owned_start
    (start : InfiniteLabelCfg) (owned : Owned start.l) (n : Nat) :
    (next allocatingExternal)^[n] (some start) = (next haltingExternal)^[n] (some start) ∧
    (next reenteringExternal)^[n] (some start) = (next haltingExternal)^[n] (some start) :=
  ⟨owned_iterate_caller_independent allocatingExternal haltingExternal start owned n,
    owned_iterate_caller_independent reenteringExternal haltingExternal start owned n⟩


end Examples.RotationCertificateFrontEndStreamMachine
