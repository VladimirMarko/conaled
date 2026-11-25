import Examples.RotationCertificatePositionedRotationMachine.Fixtures

/-!
# RotationCertificatePositionedRotationMachine: Execution
-/

namespace Examples.RotationCertificatePositionedRotationMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.RotationCertificate.PositionedRotationMachine

section ScannerContracts

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- The source is a represented prefix; old accumulators and the external suffix stay literal. -/
theorem represented_subtree_scans_into_saved (d : RotationDirection) (t : BinaryTree Unit)
    (F S z : Word) (outer : List Unit) (P : List Branch) :
    (next caller)^[(treeCode t).length]
        (some (cfg (some (phaseLabel (.scanPrefix d))) regs
          (data (treeCode t ++ z) F S (() :: outer) P) ctx)) =
      some (cfg (some (phaseLabel (if outer = [] then .seek d else .scanPrefix d)))
        (reset regs) (data z ((treeCode t).reverse ++ F) S outer P) ctx) :=
  LocalRun.iterate caller
    (scanPrefix_treeCode_localRun caller d t z outer (data [] F S [] P) regs ctx)

theorem represented_left_subtree_scans_into_scratch (t : BinaryTree Unit)
    (F S z : Word) (P : List Branch) :
    (next caller)^[(treeCode t).length]
        (some (cfg (some (phaseLabel (.scanScratch .left))) regs
          (data (treeCode t ++ z) F S [()] P) ctx)) =
      some (cfg (some (phaseLabel .checkRight)) (reset regs)
        (data z F ((treeCode t).reverse ++ S) [] P) ctx) :=
  LocalRun.iterate caller
    (scanScratch_treeCode_localRun caller .left t z [] (data [] F S [] P) regs ctx)

theorem represented_right_subtree_scans_and_inserts_its_node (t : BinaryTree Unit)
    (F S z : Word) (P : List Branch) :
    (next caller)^[(treeCode t).length]
        (some (cfg (some (phaseLabel (.scanScratch .right))) regs
          (data (treeCode t ++ z) F S [()] P) ctx)) =
      some (cfg (some (phaseLabel (.restoreScratch .successRight))) (reset regs)
        (data (1 :: z) F ((treeCode t).reverse ++ S) [] P) ctx) :=
  LocalRun.iterate caller
    (scanScratch_treeCode_localRun caller .right t z [] (data [] F S [] P) regs ctx)

theorem represented_scratch_scan_keeps_an_outer_pending_slot (d : RotationDirection)
    (t : BinaryTree Unit) (F S z : Word) (outer : List Unit) (P : List Branch) :
    (next caller)^[(treeCode t).length]
        (some (cfg (some (phaseLabel (.scanScratch d))) regs
          (data (treeCode t ++ z) F S (() :: () :: outer) P) ctx)) =
      some (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
        (data z F ((treeCode t).reverse ++ S) (() :: outer) P) ctx) := by
  simpa only [scratchScanEnd, scratchScanSource, List.cons_ne_nil, ite_false, data] using
    LocalRun.iterate caller
      (scanScratch_treeCode_localRun caller d t z (() :: outer) (data [] F S [] P) regs ctx)

/-- Continued scanning has no hidden initial-one-slot assumption. -/
theorem continued_prefix_has_its_actual_saved_segment {w : Word} {h k : Nat}
    (continued : Continues w h k) (d : RotationDirection) (F S z : Word) (P : List Branch) :
    (next caller)^[w.length]
        (some (cfg (some (phaseLabel (.scanPrefix d))) regs
          (data (w ++ z) F S (List.replicate h ()) P) ctx)) =
      some (cfg (some (phaseLabel (.scanPrefix d)))
        (if w = [] then regs else reset regs)
        (data z (w.reverse ++ F) S (List.replicate k ()) P) ctx) :=
  LocalRun.iterate caller
    (scanPrefix_continues_localRun caller continued d z (data [] F S [] P) regs ctx)

theorem continued_prefix_has_its_actual_scratch_segment {w : Word} {h k : Nat}
    (continued : Continues w h k) (d : RotationDirection) (F S z : Word) (P : List Branch) :
    (next caller)^[w.length]
        (some (cfg (some (phaseLabel (.scanScratch d))) regs
          (data (w ++ z) F S (List.replicate h ()) P) ctx)) =
      some (cfg (some (phaseLabel (.scanScratch d)))
        (if w = [] then regs else reset regs)
        (data z F (w.reverse ++ S) (List.replicate k ()) P) ctx) :=
  LocalRun.iterate caller
    (scanScratch_continues_localRun caller continued d z (data [] F S [] P) regs ctx)

end ScannerContracts

theorem nonpalindromic_right_scratch_boundary (caller : ExampleCaller) (flag : Bool) :
    (next caller)^[5]
        (some (atPhase (.scanScratch .right) flag
          (data [1,0,1,0,0,15,2] [12,3] [8,5] [()] [.right,.left]))) =
      some (cfg (some (phaseLabel (.restoreScratch .successRight))) (clean flag)
        (data [1,15,2] [12,3] [0,0,1,0,1,8,5] [] [.right,.left]) ordinaryContext) :=
  represented_right_subtree_scans_and_inserts_its_node caller (stale flag) ordinaryContext
    rightTwo [12,3] [8,5] [15,2] [.right,.left]

section TotalDirtyExecution

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-- Totality is about every actual dirty phase, with no source representation premise. -/
theorem every_dirty_phase_has_an_exact_first_live_result (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    0 < phaseSteps q D ∧ phaseSteps q D ≤ countdown (.inl q) D ∧
      FirstRun caller (cfg (some (phaseLabel q)) regs D ctx) (phaseSteps q D)
        (phaseResult q regs D ctx) ∧
      (∃ r, (phaseResult (Λ := Λ) q regs D ctx).l = some (resultLabel r)) ∧
      (phaseResult (Λ := Λ) q regs D ctx).var = reset regs ∧
      ∀ k, (phaseResult (Λ := Λ) q regs D ctx).stk (.inr k) = ctx k := by
  refine ⟨phaseSteps_pos q D, phaseSteps_le_countdown q D, ?_, ?_, rfl, fun _ => rfl⟩
  · exact firstRun_of_localRun caller (phase_localRun caller q D regs ctx)
      (by simp [phaseResult, cfg, resultLabel, Owned])
  · exact ⟨(evaluate (.inl q) D).result, rfl⟩

def arbitraryDirtyPhaseInTime (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel q)) regs D ctx)
      (some (phaseResult q regs D ctx)) (phaseSteps q D) :=
  localRunInTime caller (phase_localRun caller q D regs ctx)

theorem arbitrary_dirty_timed_data_has_the_exact_steps (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (arbitraryDirtyPhaseInTime caller q D regs ctx).steps = phaseSteps q D := rfl

/-- Ownedness is required before asserting that rank zero will be a live local result. -/
theorem every_owned_configuration_returns_live (start : Cfg Γ Λ R) (owned : Owned start.l) :
    ∃ finish r, FirstRun caller start (remainingSteps start) finish ∧
      finish.l = some (resultLabel r) ∧ finish.var = reset start.var ∧
      ∀ k, finish.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases start owned
  obtain ⟨_, _, first, ⟨r, label⟩, registers, frame⟩ :=
    every_dirty_phase_has_an_exact_first_live_result caller q D regs ctx
  exact ⟨phaseResult q regs D ctx, r, first, label, registers, frame⟩

theorem nonowned_prefix_is_only_identity (start : Cfg Γ Λ R)
    (outside : ¬ Owned start.l) :
    remainingSteps start = 0 ∧
      (next caller)^[remainingSteps start] (some start) = some start := by
  have zero : remainingSteps start = 0 := by
    have noPositive : ¬ 0 < remainingSteps start :=
      fun positive => outside ((remainingSteps_pos_iff start).mp positive)
    omega
  exact ⟨zero, by rw [zero]; rfl⟩

omit [DecidableEq K] in
theorem rank_zero_includes_both_live_results_external_and_halt
    (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) (label : Λ) :
    remainingSteps (cfg (some (resultLabel (Λ := Λ) .success)) regs D ctx) = 0 ∧
      remainingSteps (cfg (some (resultLabel (Λ := Λ) .failure)) regs D ctx) = 0 ∧
      remainingSteps (cfg (some (callerLabel label)) regs D ctx) = 0 ∧
      remainingSteps (cfg (Λ := Λ) none regs D ctx) = 0 := ⟨rfl, rfl, rfl, rfl⟩

theorem positive_rank_is_actual_resetting_progress (start : Cfg Γ Λ R)
    (owned : Owned start.l) :
    0 < remainingSteps start ∧ ∃ reached,
      step caller start = some reached ∧ remainingSteps start = remainingSteps reached + 1 ∧
      reached.var = reset start.var ∧
      ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  have positive := (remainingSteps_pos_iff start).mpr owned
  obtain ⟨reached, executed, rank⟩ := local_progress caller start positive
  have effects := local_step_data caller ⟨owned, executed⟩
  exact ⟨positive, reached, executed, rank, effects.2.1, effects.2.2⟩

theorem raw_time_bounds_are_upper_bounds_for_the_exact_clock
    (d : RotationDirection) (w : Word) (p : List Branch) :
    0 < runSteps d w p ∧ runSteps d w p ≤ 3 * w.length + p.length + 5 ∧
      runSteps d w p ≤ 4 * w.length + p.length + 12 :=
  ⟨runSteps_pos d w p, runSteps_le d w p, runSteps_le_conservative d w p⟩

end TotalDirtyExecution

theorem all_sixteen_phases_accept_both_fixed_dirty_profiles
    (caller : ExampleCaller) (flag : Bool) (q : Phase) :
    FirstRun caller (atPhase q flag dirtyPhaseA) (phaseSteps q dirtyPhaseA)
        (phaseResult q (stale flag) dirtyPhaseA ordinaryContext) ∧
      FirstRun caller (atPhase q flag dirtyPhaseB) (phaseSteps q dirtyPhaseB)
        (phaseResult q (stale flag) dirtyPhaseB ordinaryContext) :=
  ⟨(every_dirty_phase_has_an_exact_first_live_result caller q dirtyPhaseA
      (stale flag) ordinaryContext).2.2.1,
    (every_dirty_phase_has_an_exact_first_live_result caller q dirtyPhaseB
      (stale flag) ordinaryContext).2.2.1⟩

/-- A literal evaluator equality is useful only through the producer's actual owned run. -/
theorem fixture_localRun_of_evaluation (caller : ExampleCaller) (flag : Bool)
    (c : RunFixture)
    (checked : evaluate (.inl c.phase) c.before = ⟨c.result, c.after, c.ticks⟩) :
    LocalRun caller c.ticks (atPhase c.phase flag c.before) (atResult c.result flag c.after) := by
  simpa only [phaseSteps, phaseResult, checked, atPhase, atResult, reset, stale, clean] using
    phase_localRun caller c.phase c.before (stale flag) ordinaryContext

theorem fixture_expected_of_evaluation (caller : ExampleCaller) (flag : Bool)
    (c : RunFixture)
    (checked : evaluate (.inl c.phase) c.before = ⟨c.result, c.after, c.ticks⟩) :
    c.Expected caller flag :=
  firstRun_of_localRun caller (fixture_localRun_of_evaluation caller flag c checked)
    (by simp [atResult, cfg, resultLabel, Owned])

def fixtureInTime (caller : ExampleCaller) (flag : Bool) (c : RunFixture)
    (checked : evaluate (.inl c.phase) c.before = ⟨c.result, c.after, c.ticks⟩) :
    StateTransition.EvalsToInTime (step caller) (atPhase c.phase flag c.before)
      (some (atResult c.result flag c.after)) c.ticks :=
  localRunInTime caller (fixture_localRun_of_evaluation caller flag c checked)

theorem every_dirty_transfer_fixture_is_an_actual_first_return
    (caller : ExampleCaller) (flag : Bool) (c : RunFixture) (member : c ∈ transferFixtures) :
    c.Expected caller flag := by
  simp only [transferFixtures, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact firstRun_of_localRun caller
      (restoreScratch_localRun caller .successLeft dirtyData (stale flag) ordinaryContext)
      (by simp [Owned, atResult, cfg, resultLabel])
  · exact firstRun_of_localRun caller
      (restoreScratch_localRun caller .successRight dirtyData (stale flag) ordinaryContext)
      (by simp [Owned, atResult, cfg, resultLabel])
  · exact firstRun_of_localRun caller
      (restoreScratch_localRun caller .failureLeft dirtyData (stale flag) ordinaryContext)
      (by simp [Owned, atResult, cfg, resultLabel])
  · exact firstRun_of_localRun caller
      (restoreScratch_localRun caller .failureRight dirtyData (stale flag) ordinaryContext)
      (by simp [Owned, atResult, cfg, resultLabel])
  · exact firstRun_of_localRun caller
      (dropPending_localRun caller dirtyData (stale flag) ordinaryContext)
      (by simp [Owned, atResult, cfg, resultLabel])
  · exact firstRun_of_localRun caller
      (restorePrefix_localRun caller .success dirtyData (stale flag) ordinaryContext)
      (by simp [Owned, atResult, cfg, resultLabel])
  · exact firstRun_of_localRun caller
      (restorePrefix_localRun caller .failure dirtyData (stale flag) ordinaryContext)
      (by simp [Owned, atResult, cfg, resultLabel])

def dirtyTransferInTime (caller : ExampleCaller) (flag : Bool)
    (c : RunFixture) (member : c ∈ transferFixtures) :
    StateTransition.EvalsToInTime (step caller) (atPhase c.phase flag c.before)
      (some (atResult c.result flag c.after)) c.ticks where
  steps := c.ticks
  evals_in_steps := (every_dirty_transfer_fixture_is_an_actual_first_return caller flag c member).1
  steps_le_m := Nat.le_refl _

theorem raw_fixture_evaluations (c : RunFixture) (member : c ∈ rawFixtures) :
    evaluate (.inl c.phase) c.before = ⟨c.result, c.after, c.ticks⟩ := by
  simp only [rawFixtures, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [evaluate_phase, evaluate_result, advance, scratchFailure, markerWord, modeResult,
      nodeTag, emptyTag, data]

theorem every_raw_fixture_is_an_actual_first_return
    (caller : ExampleCaller) (flag : Bool) (c : RunFixture) (member : c ∈ rawFixtures) :
    c.Expected caller flag :=
  fixture_expected_of_evaluation caller flag c (raw_fixture_evaluations c member)

def rawFixtureInTime (caller : ExampleCaller) (flag : Bool)
    (c : RunFixture) (member : c ∈ rawFixtures) :
    StateTransition.EvalsToInTime (step caller) (atPhase c.phase flag c.before)
      (some (atResult c.result flag c.after)) c.ticks :=
  fixtureInTime caller flag c (raw_fixture_evaluations c member)

theorem fixed_fixture_timed_data_keeps_exact_steps (caller : ExampleCaller) (flag : Bool)
    (transfer raw : RunFixture) (isTransfer : transfer ∈ transferFixtures)
    (isRaw : raw ∈ rawFixtures) :
    (dirtyTransferInTime caller flag transfer isTransfer).steps = transfer.ticks ∧
      (rawFixtureInTime caller flag raw isRaw).steps = raw.ticks := ⟨rfl, rfl⟩

section DirtyTransferContracts

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem arbitrary_scratch_split_retains_the_empty_probe (mode : RestoreMode)
    (X F A B : Word) (H : List Unit) (P : List Branch) :
    (next caller)^[A.length]
        (some (cfg (some (phaseLabel (.restoreScratch mode))) regs (data X F (A ++ B) H P) ctx)) =
      some (cfg (some (phaseLabel (.restoreScratch mode)))
        (if A = [] then regs else reset regs) (data (A.reverse ++ X) F B H P) ctx) :=
  restoreScratch_prefix caller mode A B (data X F [] H P) regs ctx

theorem arbitrary_saved_split_retains_the_empty_probe (r : Result)
    (X A B S : Word) (H : List Unit) (P : List Branch) :
    (next caller)^[A.length]
        (some (cfg (some (phaseLabel (.restorePrefix r))) regs (data X (A ++ B) S H P) ctx)) =
      some (cfg (some (phaseLabel (.restorePrefix r)))
        (if A = [] then regs else reset regs) (data (A.reverse ++ X) B S H P) ctx) :=
  restorePrefix_prefix caller r A B (data X [] S H P) regs ctx

theorem arbitrary_pending_split_retains_the_empty_probe
    (X F S : Word) (A B : List Unit) (P : List Branch) :
    (next caller)^[A.length]
        (some (cfg (some (phaseLabel .dropPending)) regs (data X F S (A ++ B) P) ctx)) =
      some (cfg (some (phaseLabel .dropPending))
        (if A = [] then regs else reset regs) (data X F S B P) ctx) :=
  dropPending_prefix caller A B (data X F S [] P) regs ctx

/-- All four modes retain arbitrary source, saved, scratch, pending, and path data. -/
theorem four_complete_scratch_transfers_have_the_fixed_dirty_endpoints
    (X F S : Word) (H : List Unit) (P : List Branch) :
    FirstRun caller
        (cfg (some (phaseLabel (.restoreScratch .successLeft))) regs (data X F S H P) ctx)
        (S.length + F.length + 2)
        (cfg (some (resultLabel .success)) (reset regs)
          (data (F.reverse ++ [1,1] ++ S.reverse ++ X) [] [] H P) ctx) ∧
      FirstRun caller
        (cfg (some (phaseLabel (.restoreScratch .successRight))) regs (data X F S H P) ctx)
        (S.length + F.length + 2)
        (cfg (some (resultLabel .success)) (reset regs)
          (data (F.reverse ++ [1] ++ S.reverse ++ X) [] [] H P) ctx) ∧
      FirstRun caller
        (cfg (some (phaseLabel (.restoreScratch .failureLeft))) regs (data X F S H P) ctx)
        (S.length + H.length + F.length + 3)
        (cfg (some (resultLabel .failure)) (reset regs)
          (data (F.reverse ++ [1] ++ S.reverse ++ X) [] [] [] P) ctx) ∧
      FirstRun caller
        (cfg (some (phaseLabel (.restoreScratch .failureRight))) regs (data X F S H P) ctx)
        (S.length + H.length + F.length + 3)
        (cfg (some (resultLabel .failure)) (reset regs)
          (data (F.reverse ++ [1,1] ++ S.reverse ++ X) [] [] [] P) ctx) :=
  ⟨firstRun_of_localRun caller
      (restoreScratch_localRun caller .successLeft (data X F S H P) regs ctx)
      (by simp [Owned, cfg, resultLabel]),
    firstRun_of_localRun caller
      (restoreScratch_localRun caller .successRight (data X F S H P) regs ctx)
      (by simp [Owned, cfg, resultLabel]),
    firstRun_of_localRun caller
      (restoreScratch_localRun caller .failureLeft (data X F S H P) regs ctx)
      (by simp [Owned, cfg, resultLabel]),
    firstRun_of_localRun caller
      (restoreScratch_localRun caller .failureRight (data X F S H P) regs ctx)
      (by simp [Owned, cfg, resultLabel])⟩

theorem dropping_pending_preserves_dirty_scratch (X F S : Word)
    (H : List Unit) (P : List Branch) :
    FirstRun caller (cfg (some (phaseLabel .dropPending)) regs (data X F S H P) ctx)
      (H.length + F.length + 2)
      (cfg (some (resultLabel .failure)) (reset regs) (data (F.reverse ++ X) [] S [] P) ctx) :=
  firstRun_of_localRun caller (dropPending_localRun caller (data X F S H P) regs ctx)
    (by simp [Owned, cfg, resultLabel])

theorem restoring_saved_preserves_dirty_scratch_and_pending (r : Result)
    (X F S : Word) (H : List Unit) (P : List Branch) :
    FirstRun caller (cfg (some (phaseLabel (.restorePrefix r))) regs (data X F S H P) ctx)
      (F.length + 1)
      (cfg (some (resultLabel r)) (reset regs) (data (F.reverse ++ X) [] S H P) ctx) :=
  firstRun_of_localRun caller (restorePrefix_localRun caller r (data X F S H P) regs ctx)
    (by simp [Owned, cfg, resultLabel])

end DirtyTransferContracts

theorem all_partial_dirty_transfer_expectations (caller : ExampleCaller) (flag : Bool)
    (mode : RestoreMode) (r : Result) (X F S A B : Word)
    (H HA HB : List Unit) (P : List Branch) :
    ScratchSplitExpected caller flag mode X F A B H P ∧
      SavedSplitExpected caller flag r X A B S H P ∧
      PendingSplitExpected caller flag X F S HA HB P :=
  ⟨arbitrary_scratch_split_retains_the_empty_probe caller (stale flag) ordinaryContext
      mode X F A B H P,
    arbitrary_saved_split_retains_the_empty_probe caller (stale flag) ordinaryContext
      r X A B S H P,
    arbitrary_pending_split_retains_the_empty_probe caller (stale flag) ordinaryContext
      X F S HA HB P⟩

section PrefixAndTimingContracts

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-- All facts refer to one actual reached configuration, including the zero-step state. -/
theorem inclusive_prefix_has_one_rank_reset_and_frame_witness
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧
      reached.var = (if n = 0 then start.var else reset start.var) ∧
      ∀ k, reached.stk (.inr k) = start.stk (.inr k) :=
  owned_prefix_frame caller start n bound

theorem arbitrary_callers_agree_through_the_inclusive_first_handoff
    (other : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R)
    (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) :=
  prefix_caller_independent caller other start n bound

theorem installed_owned_blocks_give_the_same_actual_prefix
    (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ q, ambient (phaseLabel q) = block q)
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) =
      (fun c : Option (Cfg Γ Λ R) => c.bind (Turing.TM2.step ambient))^[n] (some start) :=
  ambient_prefix_eq caller ambient agrees start n bound

theorem every_first_dirty_exit_has_the_evaluator_clock_and_complete_endpoint
    (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : Cfg Γ Λ R)
    (first : FirstRun caller (cfg (some (phaseLabel q)) regs D ctx) n reached) :
    n = phaseSteps q D ∧ reached = phaseResult q regs D ctx :=
  first_return_unique caller q D regs ctx n reached first.1 first.2.1 first.2.2

def allRawInExactTime (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry d regs raw path ctx)
      (some (phaseResult (.seek d) regs { source := raw, path := path } ctx))
      (runSteps d raw path) := runInTimeExact caller d raw path regs ctx

def allRawInLinearTime (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry d regs raw path ctx)
      (some (phaseResult (.seek d) regs { source := raw, path := path } ctx))
      (3 * raw.length + path.length + 5) := runInLinearTime caller d raw path regs ctx

def allRawInConservativeTime (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry d regs raw path ctx)
      (some (phaseResult (.seek d) regs { source := raw, path := path } ctx))
      (4 * raw.length + path.length + 12) := runInConservativeTime caller d raw path regs ctx

theorem bounded_timing_keeps_the_actual_exact_steps (d : RotationDirection)
    (raw : Word) (path : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (allRawInExactTime caller d raw path regs ctx).steps = runSteps d raw path ∧
      (allRawInLinearTime caller d raw path regs ctx).steps = runSteps d raw path ∧
      (allRawInConservativeTime caller d raw path regs ctx).steps = runSteps d raw path ∧
      (phaseInTime caller (.seek d) { source := raw, path := path } regs ctx).steps =
        runSteps d raw path := ⟨rfl, rfl, rfl, rfl⟩

end PrefixAndTimingContracts

theorem callers_agree_through_return_and_differ_on_the_next_activation (flag : Bool) :
    (∀ n, n ≤ 7 →
      (next (sentinelCaller 13))^[n] (some (cleanEntry .left flag [1,0,1,0,0] [])) =
        (next (sentinelCaller 14))^[n] (some (cleanEntry .left flag [1,0,1,0,0] []))) ∧
      (next (sentinelCaller 13))^[8] (some (cleanEntry .left flag [1,0,1,0,0] [])) ≠
        (next (sentinelCaller 14))^[8] (some (cleanEntry .left flag [1,0,1,0,0] [])) := by
  have rank : remainingSteps (cleanEntry .left flag [1,0,1,0,0] []) = 7 := by
    have exactRank := LocalRun.remaining (sentinelCaller 13)
      (minimal_left_physical_segment (sentinelCaller 13) (stale flag) ordinaryContext)
    simpa only [cleanEntry, atPhase, remainingSteps, cfg, resultLabel, Nat.add_zero] using exactRank
  refine ⟨?_, ?_⟩
  · intro n bound
    apply prefix_caller_independent (sentinelCaller 13) (sentinelCaller 14)
    rwa [rank]
  · have first13 := (sentinel_success_three_stages flag).2.1
    have returned14 := (minimal_left_first_return (sentinelCaller 14) flag).1
    have first14 := append_actual_step (sentinelCaller 14) 7 _ _ _ returned14
      (sentinel_push_step 14 .success (clean flag) (data [1,1,0,0,0] [] [] [] [])
        [15,2,7,10,3] [(),()])
    rw [first13, first14]
    intro same
    have heads := congrArg (fun c : ExampleCfg => (c.stk (.inr (0 : Fin 2))).head?)
      (Option.some.inj same)
    have impossible : (13 : Tag) = 14 := Option.some.inj heads
    exact (by decide : (13 : Tag) ≠ 14) impossible

theorem emptyContext_eq : emptyContext = (fun _ => []) := by
  funext k
  fin_cases k <;> rfl

theorem the_actual_package_has_seven_nineteen_two_hundred_four
    (d : RotationDirection) (caller : ExampleCaller) (initial : Bool) :
    @Fintype.card (concreteMachine d caller initial).K (concreteMachine d caller initial).kFin = 7 ∧
      @Fintype.card (concreteMachine d caller initial).Λ (concreteMachine d caller initial).ΛFin = 19 ∧
      @Fintype.card (concreteMachine d caller initial).σ (concreteMachine d caller initial).σFin = 204 := by
  change Fintype.card (StackId (Fin 2)) = 7 ∧ Fintype.card (Label Unit) = 19 ∧
    Fintype.card (Registers Bool) = 204
  exact actual_finite_carrier_counts.2.2.2.2

@[instance_reducible]
def everyPackagedAlphabetIsFinite (d : RotationDirection) (caller : ExampleCaller)
    (initial : Bool) (k : (concreteMachine d caller initial).K) :
    Fintype ((concreteMachine d caller initial).Γ k) := machineAlphabetFintype caller d initial k

theorem real_package_source_input_output_and_main
    (d : RotationDirection) (caller : ExampleCaller) (initial : Bool) :
    (concreteMachine d caller initial).k₀ = .inl .source ∧
      (concreteMachine d caller initial).k₁ = .inl .source ∧
      (concreteMachine d caller initial).main = phaseLabel (.seek d) ∧
      (concreteMachine d caller initial).initialState = clean initial := ⟨rfl, rfl, rfl, rfl⟩

/-- Genuine one-input initialization fills source only, including when source is malformed. -/
theorem genuine_initializer_has_no_path_or_protected_cells
    (d : RotationDirection) (caller : ExampleCaller) (initial : Bool) (raw : Word) :
    Turing.initList (concreteMachine d caller initial) raw =
      cfg (some (phaseLabel (.seek d))) (clean initial) (data raw [] [] [] []) emptyContext := by
  rw [emptyContext_eq]
  exact initList_eq caller d initial raw

theorem actual_package_step_is_the_component_step
    (d : RotationDirection) (caller : ExampleCaller) (initial : Bool) (c : ExampleCfg) :
    (concreteMachine d caller initial).step c = step caller c := machine_step_eq caller d initial c

theorem the_package_executes_the_actually_installed_path
    (d : RotationDirection) (caller : ExampleCaller) (initial : Bool)
    (raw : Word) (path : List Branch) (regs : Registers Bool)
    (ctx : ∀ k, List (ProtectedAlphabet k)) :
    (fun c => c.bind (concreteMachine d caller initial).step)^[runSteps d raw path]
        (some (cfg (some (phaseLabel (.seek d))) regs (data raw [] [] [] path) ctx)) =
      some (phaseResult (.seek d) regs (data raw [] [] [] path) ctx) :=
  machine_cfg_run caller d initial raw path regs ctx

def allGenuineInputsInTime (d : RotationDirection) (caller : ExampleCaller)
    (initial : Bool) (raw : Word) :
    StateTransition.EvalsToInTime (concreteMachine d caller initial).step
      (Turing.initList (concreteMachine d caller initial) raw)
      (some (phaseResult (.seek d) (clean initial) (data raw [] [] [] []) (fun _ => [])))
      (runSteps d raw []) := machineInitInTime caller d initial raw

def installedConfigurationInTime (d : RotationDirection) (caller : ExampleCaller)
    (initial : Bool) (raw : Word) (path : List Branch) (regs : Registers Bool)
    (ctx : ∀ k, List (ProtectedAlphabet k)) :
    StateTransition.EvalsToInTime (concreteMachine d caller initial).step
      (cfg (some (phaseLabel (.seek d))) regs (data raw [] [] [] path) ctx)
      (some (phaseResult (.seek d) regs (data raw [] [] [] path) ctx))
      (runSteps d raw path) := machineCfgInTime caller d initial raw path regs ctx

theorem initializer_and_installed_path_are_distinct (caller : ExampleCaller)
    (initial : Bool) :
    Turing.initList (concreteMachine .left caller initial) ([1,1,0,1,0,0,0] : Word) ≠
      cfg (some (phaseLabel (.seek .left))) (clean initial)
        (data [1,1,0,1,0,0,0] [] [] [] [.left]) emptyContext := by
  rw [genuine_initializer_has_no_path_or_protected_cells]
  intro same
  have paths := congrArg (fun c : ExampleCfg => c.stk (.inl .path)) same
  cases paths

theorem genuine_root_fixture_evaluation :
    evaluate (.inl (.seek .left)) (data [1,1,0,1,0,0,0] [] [] [] []) =
      ⟨.failure, data [1,1,0,1,0,0,0] [] [] [] [], 16⟩ := by
  simp [evaluate_phase, evaluate_result, advance, markerWord, modeResult,
    nodeTag, emptyTag, data]

theorem installed_left_path_fixture_evaluation :
    evaluate (.inl (.seek .left)) (data [1,1,0,1,0,0,0] [] [] [] [.left]) =
      ⟨.success, data [1,1,1,0,0,0,0] [] [] [] [], 9⟩ := by
  simp [evaluate_phase, evaluate_result, advance, markerWord, modeResult,
    nodeTag, emptyTag, data]

theorem genuine_root_failure_and_installed_path_success_use_the_same_package
    (caller : ExampleCaller) (initial : Bool) :
    (fun c => c.bind (concreteMachine .left caller initial).step)^[16]
        (some (Turing.initList (concreteMachine .left caller initial) ([1,1,0,1,0,0,0] : Word))) =
        some (cfg (some (resultLabel .failure)) (clean initial)
          (data [1,1,0,1,0,0,0] [] [] [] []) emptyContext) ∧
      (fun c => c.bind (concreteMachine .left caller initial).step)^[9]
        (some (cfg (some (phaseLabel (.seek .left))) (clean initial)
          (data [1,1,0,1,0,0,0] [] [] [] [.left]) emptyContext)) =
        some (cfg (some (resultLabel .success)) (clean initial)
          (data [1,1,1,0,0,0,0] [] [] [] []) emptyContext) := by
  constructor
  · change (fun c : Option ExampleCfg =>
        c.bind (concreteMachine .left caller initial).step)^[16]
        (some (Turing.initList (concreteMachine .left caller initial)
          ([1,1,0,1,0,0,0] : Word))) = _
    have actual := machine_init_run caller .left initial [1,1,0,1,0,0,0]
    simpa only [concreteMachine, runSteps, phaseSteps, phaseResult,
      show ({ source := [1,1,0,1,0,0,0] } : LocalData) = data [1,1,0,1,0,0,0] [] [] [] [] from rfl,
      show ({ source := [1,1,0,1,0,0,0], path := [] } : LocalData) =
        data [1,1,0,1,0,0,0] [] [] [] [] from rfl,
      genuine_root_fixture_evaluation, emptyContext_eq, initialRegisters, clean, reset]
      using actual
  · have actual := machine_cfg_run caller .left initial [1,1,0,1,0,0,0] [.left]
      (clean initial) emptyContext
    simpa only [concreteMachine, runSteps, phaseSteps, phaseResult, entry,
      show ({ source := [1,1,0,1,0,0,0], path := [.left] } : LocalData) =
        data [1,1,0,1,0,0,0] [] [] [] [.left] from rfl,
      installed_left_path_fixture_evaluation, reset, clean]
      using actual

def genuineRootFixtureInTime (caller : ExampleCaller) (initial : Bool) :
    StateTransition.EvalsToInTime (concreteMachine .left caller initial).step
      (Turing.initList (concreteMachine .left caller initial) ([1,1,0,1,0,0,0] : Word))
      (some (cfg (some (resultLabel .failure)) (clean initial)
        (data [1,1,0,1,0,0,0] [] [] [] []) emptyContext)) 16 where
  steps := 16
  evals_in_steps :=
    (genuine_root_failure_and_installed_path_success_use_the_same_package caller initial).1
  steps_le_m := Nat.le_refl _

def installedPathFixtureInTime (caller : ExampleCaller) (initial : Bool) :
    StateTransition.EvalsToInTime (concreteMachine .left caller initial).step
      (cfg (some (phaseLabel (.seek .left))) (clean initial)
        (data [1,1,0,1,0,0,0] [] [] [] [.left]) emptyContext)
      (some (cfg (some (resultLabel .success)) (clean initial)
        (data [1,1,1,0,0,0,0] [] [] [] []) emptyContext)) 9 where
  steps := 9
  evals_in_steps :=
    (genuine_root_failure_and_installed_path_success_use_the_same_package caller initial).2
  steps_le_m := Nat.le_refl _

section BlockedScans

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- The continued-prefix premise is retained, and dirty scratch survives prefix cleanup. -/
theorem blocked_saved_scan_has_its_exact_dirty_first_return
    {w z : Word} {h k : Nat} (continued : Continues w h k)
    (blocked : TreeParserMachine.Blocked z) (d : RotationDirection)
    (F S : Word) (P : List Branch) :
    FirstRun caller
      (cfg (some (phaseLabel (.scanPrefix d))) regs
        (data (w ++ z) F S (List.replicate h ()) P) ctx)
      (2 * w.length + k + F.length + 3)
      (cfg (some (resultLabel .failure)) (reset regs)
        (data (F.reverse ++ w ++ z) [] S [] P) ctx) :=
  firstRun_of_localRun caller
    (scanPrefix_blocked_localRun caller continued blocked d (data [] F S [] P) regs ctx)
    (by simp [Owned, cfg, resultLabel])

theorem blocked_scratch_scan_restores_both_accumulators_and_direction_markers
    {w z : Word} {h k : Nat} (continued : Continues w h k)
    (blocked : TreeParserMachine.Blocked z) (d : RotationDirection)
    (F S : Word) (P : List Branch) :
    FirstRun caller
      (cfg (some (phaseLabel (.scanScratch d))) regs
        (data (w ++ z) F S (List.replicate h ()) P) ctx)
      (2 * w.length + k + S.length + F.length + 4)
      (cfg (some (resultLabel .failure)) (reset regs)
        (data (F.reverse ++ markerWord (scratchFailure d) ++ S.reverse ++ w ++ z) [] [] [] P) ctx) :=
  firstRun_of_localRun caller
    (scanScratch_blocked_localRun caller continued blocked d (data [] F S [] P) regs ctx)
    (by simp [Owned, cfg, resultLabel])

theorem both_raw_root_patterns_preserve_arbitrary_saved_words_and_suffixes
    (A : BinaryTree Unit) (F z : Word) :
    FirstRun caller
      (cfg (some (phaseLabel (.seek .left))) regs
        (data ([1] ++ treeCode A ++ [1] ++ z) F [] [] []) ctx)
      (2 * (treeCode A).length + 5 + F.length)
      (cfg (some (resultLabel .success)) (reset regs)
        (data (F.reverse ++ [1,1] ++ treeCode A ++ z) [] [] [] []) ctx) ∧
      FirstRun caller
        (cfg (some (phaseLabel (.seek .right))) regs
          (data ([1,1] ++ treeCode A ++ z) F [] [] []) ctx)
        (2 * (treeCode A).length + 4 + F.length)
        (cfg (some (resultLabel .success)) (reset regs)
          (data (F.reverse ++ [1] ++ treeCode A ++ [1] ++ z) [] [] [] []) ctx) := by
  constructor
  · simpa only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc, data, nodeTag] using
      firstRun_of_localRun caller (root_left_pattern_localRun caller A z F regs ctx)
        (by simp [Owned, cfg, resultLabel])
  · simpa only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc, data, nodeTag] using
      firstRun_of_localRun caller (root_right_pattern_localRun caller A z F regs ctx)
        (by simp [Owned, cfg, resultLabel])

end BlockedScans

theorem left_raw_root_pattern_has_the_fixed_clock_and_complete_output
    (caller : ExampleCaller) (flag : Bool) (A : BinaryTree Unit) (z : Word) :
    LeftRootPatternExpected caller flag A z := by
  have segment := root_left_pattern_localRun caller A z [] (stale flag) ordinaryContext
  have rank := LocalRun.remaining caller segment
  refine ⟨?_, ?_⟩
  · simpa only [remainingSteps, cfg, phaseLabel, resultLabel, dataOfCfg,
      List.length_nil, Nat.add_zero, List.singleton_append, List.cons_append,
      List.nil_append, List.append_assoc, runSteps, nodeTag] using rank
  · simpa only [List.singleton_append, List.cons_append, List.nil_append,
      List.length_nil, Nat.add_zero, List.reverse_nil, List.append_assoc,
      cleanEntry, atPhase, atResult, data, nodeTag, reset, stale, clean] using
      firstRun_of_localRun caller segment (by simp [Owned, cfg, resultLabel])

theorem right_raw_root_pattern_has_the_fixed_clock_and_complete_output
    (caller : ExampleCaller) (flag : Bool) (A : BinaryTree Unit) (z : Word) :
    RightRootPatternExpected caller flag A z := by
  have segment := root_right_pattern_localRun caller A z [] (stale flag) ordinaryContext
  have rank := LocalRun.remaining caller segment
  refine ⟨?_, ?_⟩
  · simpa only [remainingSteps, cfg, phaseLabel, resultLabel, dataOfCfg,
      List.length_nil, Nat.add_zero, List.singleton_append, List.cons_append,
      List.nil_append, List.append_assoc, runSteps, nodeTag] using rank
  · simpa only [List.singleton_append, List.cons_append, List.nil_append,
      List.length_nil, Nat.add_zero, List.reverse_nil, List.append_assoc,
      cleanEntry, atPhase, atResult, data, nodeTag, reset, stale, clean] using
      firstRun_of_localRun caller segment (by simp [Owned, cfg, resultLabel])

theorem protected_words_have_the_actual_two_stack_cell_sum (tags : Word) (units : List Unit) :
    contextCells (protectedWords tags units) = tags.length + units.length := by
  rw [contextCells, show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide]
  simp [protectedWords]
  rfl

theorem ordinary_context_has_seven_actual_cells : contextCells ordinaryContext = 7 :=
  protected_words_have_the_actual_two_stack_cell_sum _ _

theorem all_fixed_carrier_expectations : CarrierExpected := by
  obtain ⟨localsCount, phases, results, temporaries, stackCount, labels, registers⟩ :=
    actual_finite_carrier_counts
  exact ⟨localsCount, phases, results, temporaries, stackCount, labels, registers,
    owned_labels_stay_finite_with_nat_callers.1,
    owned_labels_stay_finite_with_nat_callers.2, ordinary_context_has_seven_actual_cells⟩

section PhysicalPrefixes

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)

/-- Rank, reset, frame, conserved Tags and the cell bound share one actual prefix. -/
theorem every_inclusive_prefix_satisfies_the_complete_fixed_contract
    (start : Cfg Γ Λ R) (n : Nat) : PrefixExpected caller start n := by
  intro bound
  obtain ⟨reached, executed, rank, path, ownership, zero, registers, frame⟩ :=
    owned_prefix_frame caller start n bound
  have bounded := local_reaches_potential_le caller path
  exact ⟨reached, executed, rank, path, ownership, zero, registers, frame,
    local_reaches_tag_debt caller path, bounded,
    (stackCells_le_potential reached).trans bounded⟩

theorem every_clean_raw_prefix_has_the_physical_dependent_sum_bound
    (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat)
    (bound : n ≤ runSteps d raw path) (reached : Cfg Γ Λ R)
    (executed : Runs caller (entry d regs raw path ctx) n reached) :
    (∑ k : StackId K, (reached.stk k).length) ≤
      2 * raw.length + path.length + contextCells ctx :=
  prefix_stackCells_le caller d raw path regs ctx n bound reached executed

omit [Fintype K] in
theorem inclusive_prefix_rank_of_actual_run (start reached : Cfg Γ Λ R)
    (total n : Nat) (rank : remainingSteps start = total) (bound : n ≤ total)
    (executed : Runs caller start n reached) : remainingSteps reached = total - n := by
  obtain ⟨actual, actualRun, actualRank, _, _⟩ :=
    owned_prefix caller start n (by simpa only [rank] using bound)
  have same := Option.some.inj (actualRun.symm.trans executed)
  subst actual
  simpa only [rank] using actualRank

end PhysicalPrefixes

def boundaryReached (flag : Bool) (b : Boundary) : ExampleCfg :=
  cfg (some (controlLabel b.2.1)) (if b.1 = 0 then stale flag else clean flag)
    b.2.2.1 ordinaryContext

def Boundary.Expected (caller : ExampleCaller) (flag : Bool)
    (d : RotationDirection) (input : Word) (total : Nat) (b : Boundary) : Prop :=
  Runs caller (cleanEntry d flag input []) b.1 (boundaryReached flag b) ∧
    remainingSteps (boundaryReached flag b) = total - b.1 ∧
    ownedCells (boundaryReached flag b) = b.2.2.2 ∧
    stackCells (boundaryReached flag b) = b.2.2.2 + 7 ∧
    tagCells (boundaryReached flag b) + debt (boundaryReached flag b).l = 5

theorem every_left_literal_boundary_is_an_actual_prefix
    (caller : ExampleCaller) (flag : Bool) (b : Boundary) (member : b ∈ leftBoundaries) :
    Runs caller (cleanEntry .left flag [1,0,1,0,0] []) b.1 (boundaryReached flag b) := by
  simp only [leftBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Runs, cleanEntry, atPhase, boundaryReached, Function.iterate_succ_apply,
      next_some, advance_step, advance, controlLabel,
      nodeTag, emptyTag, data, reset, stale, clean, markerWord, modeResult]

theorem every_right_literal_boundary_is_an_actual_prefix
    (caller : ExampleCaller) (flag : Bool) (b : Boundary) (member : b ∈ rightBoundaries) :
    Runs caller (cleanEntry .right flag [1,1,0,0,0] []) b.1 (boundaryReached flag b) := by
  simp only [rightBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Runs, cleanEntry, atPhase, boundaryReached, Function.iterate_succ_apply,
      next_some, advance_step, advance, controlLabel,
      nodeTag, emptyTag, data, reset, stale, clean, markerWord, modeResult]

theorem minimal_initial_ranks_are_seven_and_six (flag : Bool) :
    remainingSteps (cleanEntry .left flag [1,0,1,0,0] []) = 7 ∧
      remainingSteps (cleanEntry .right flag [1,1,0,0,0] []) = 6 := by
  constructor
  · simpa [remainingSteps, cleanEntry, atPhase, data, cfg, phaseLabel, resultLabel,
      dataOfCfg, treeCode, nodeTag, emptyTag] using
      LocalRun.remaining haltCaller
        (root_left_pattern_localRun haltCaller .nil [0,0] [] (stale flag) ordinaryContext)
  · simpa [remainingSteps, cleanEntry, atPhase, data, cfg, phaseLabel, resultLabel,
      dataOfCfg, treeCode, nodeTag, emptyTag] using
      LocalRun.remaining haltCaller
        (root_right_pattern_localRun haltCaller .nil [0,0] [] (stale flag) ordinaryContext)

theorem every_left_literal_boundary_has_its_rank_and_actual_cell_count
    (caller : ExampleCaller) (flag : Bool) (b : Boundary) (member : b ∈ leftBoundaries) :
    Boundary.Expected caller flag .left [1,0,1,0,0] 7 b := by
  have executed := every_left_literal_boundary_is_an_actual_prefix caller flag b member
  have bound : b.1 ≤ 7 := by
    simp only [leftBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨executed, inclusive_prefix_rank_of_actual_run caller _ _ 7 b.1
    (minimal_initial_ranks_are_seven_and_six flag).1 bound executed, ?_⟩
  simp only [leftBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [boundaryReached, stackCells_cfg]
  all_goals
    simp [ownedCells, tagCells, dataOfCfg, cfg, localCells, localTagCells,
      ordinary_context_has_seven_actual_cells, debt, controlLabel, phaseLabel,
      resultLabel, phaseDebt, data]

theorem every_right_literal_boundary_has_its_rank_and_actual_cell_count
    (caller : ExampleCaller) (flag : Bool) (b : Boundary) (member : b ∈ rightBoundaries) :
    Boundary.Expected caller flag .right [1,1,0,0,0] 6 b := by
  have executed := every_right_literal_boundary_is_an_actual_prefix caller flag b member
  have bound : b.1 ≤ 6 := by
    simp only [rightBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨executed, inclusive_prefix_rank_of_actual_run caller _ _ 6 b.1
    (minimal_initial_ranks_are_seven_and_six flag).2 bound executed, ?_⟩
  simp only [rightBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [boundaryReached, stackCells_cfg]
  all_goals
    simp [ownedCells, tagCells, dataOfCfg, cfg, localCells, localTagCells,
      ordinary_context_has_seven_actual_cells, debt, controlLabel, phaseLabel,
      resultLabel, phaseDebt, data]


theorem empty_success_restoration_reifies_two_owed_markers
    (caller : ExampleCaller) (flag : Bool) :
    step caller (atPhase (.restoreScratch .successLeft) flag (data [] [] [] [] [])) =
      some (cfg (some (phaseLabel (.restorePrefix .success))) (clean flag)
        (data [1,1] [] [] [] []) ordinaryContext) ∧
      ownedCells (atPhase (.restoreScratch .successLeft) flag (data [] [] [] [] [])) = 0 ∧
      ownedCells (cfg (some (phaseLabel (.restorePrefix .success))) (clean flag)
        (data [1,1] [] [] [] []) ordinaryContext : ExampleCfg) = 2 ∧
      debt (atPhase (.restoreScratch .successLeft) flag (data [] [] [] [] [])).l = 2 := by
  exact ⟨restoreScratch_step_nil caller .successLeft (data [] [] [] [] [])
    (stale flag) ordinaryContext, rfl, rfl, rfl⟩

theorem a_node_scan_needs_source_credit_for_its_pending_cell
    (caller : ExampleCaller) (flag : Bool) :
    step caller (atPhase (.scanPrefix .left) flag (data [1] [] [] [] [])) =
      some (cfg (some (phaseLabel (.scanPrefix .left))) (clean flag)
        (data [] [1] [] [()] []) ordinaryContext) ∧
      ownedCells (atPhase (.scanPrefix .left) flag (data [1] [] [] [] [])) = 1 ∧
      ownedCells (cfg (some (phaseLabel (.scanPrefix .left))) (clean flag)
        (data [] [1] [] [()] []) ordinaryContext : ExampleCfg) = 2 ∧
      credit (atPhase (.scanPrefix .left) flag (data [1] [] [] [] [])) = 1 := by
  exact ⟨scanPrefix_step_node caller .left [] (data [1] [] [] [] [])
    (stale flag) ordinaryContext, rfl, rfl, rfl⟩

theorem the_real_initializer_has_the_inclusive_twice_input_bound
    (caller : ExampleCaller) (d : RotationDirection) (initial : Bool) (raw : Word)
    (n : Nat) (bound : n ≤ runSteps d raw []) (reached : ExampleCfg)
    (executed : (fun c => c.bind (concreteMachine d caller initial).step)^[n]
      (some (Turing.initList (concreteMachine d caller initial) raw)) = some reached) :
    stackCells reached ≤ 2 * raw.length :=
  machine_prefix_stackCells_le caller d initial raw n bound reached executed

theorem the_real_installed_path_keeps_the_path_and_context_cell_terms
    (caller : ExampleCaller) (d : RotationDirection) (initial : Bool) (raw : Word)
    (path : List Branch) (flag : Bool) (n : Nat) (bound : n ≤ runSteps d raw path)
    (reached : ExampleCfg)
    (executed : (fun c => c.bind (concreteMachine d caller initial).step)^[n]
      (some (entry d (stale flag) raw path ordinaryContext)) = some reached) :
    stackCells reached ≤ 2 * raw.length + path.length + 7 := by
  simpa only [ordinary_context_has_seven_actual_cells] using
    machine_cfg_prefix_stackCells_le caller d initial raw path (stale flag)
      ordinaryContext n bound reached executed


end Examples.RotationCertificatePositionedRotationMachine
