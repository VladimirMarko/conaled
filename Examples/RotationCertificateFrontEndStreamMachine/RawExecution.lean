import Examples.RotationCertificateFrontEndStreamMachine.StreamExecution

/-!
# RotationCertificateFrontEndStreamMachine: RawExecution
-/

namespace Examples.RotationCertificateFrontEndStreamMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.FrontEndStreamMachine

/-! ## All 36 raw inputs compose the actual front end, stream and cleanup -/

@[simp] theorem full_reset_after_any_front_end_outcome {R : Type}
    (kind : FrontEndKind) (regs : Registers R) :
    fullReset (kind.registers regs) = fullReset regs := by cases kind <;> rfl

@[simp] theorem answer_after_any_front_end_outcome {R : Type}
    (kind : FrontEndKind) (bit : Bool) (regs : Registers R) :
    answerRegisters bit (kind.registers regs) = answerRegisters bit regs := by cases kind <;> rfl

section LiteralRawRuns

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
  (caller : Λ → Statement Γ Λ R)

theorem emptyRawFixture_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller emptyRawFixture.frontEndTicks (emptyRawFixture.start regs ctx) (emptyRawFixture.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs emptyRawFixture.raw ctx

theorem emptyRawFixture_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    emptyRawFixture.IntermediateExpected (step caller) regs ctx := by
  have first := emptyRawFixture_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller emptyRawFixture.frontEndAfter (emptyRawFixture.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[emptyRawFixture.frontEndTicks + 1] (some (emptyRawFixture.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) emptyRawFixture.beforeClear ctx)
  have sameData : emptyRawFixture.frontEndAfter = emptyRawFixture.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem emptyRawFixture_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    emptyRawFixture.RunExpected (step caller) regs ctx := by
  have first := emptyRawFixture_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller emptyRawFixture.frontEndAfter (emptyRawFixture.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 emptyRawFixture.frontEndAfter
    (answerRegisters false (emptyRawFixture.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem truncatedPrefixFixture_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller truncatedPrefixFixture.frontEndTicks (truncatedPrefixFixture.start regs ctx) (truncatedPrefixFixture.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs truncatedPrefixFixture.raw ctx

theorem truncatedPrefixFixture_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    truncatedPrefixFixture.IntermediateExpected (step caller) regs ctx := by
  have first := truncatedPrefixFixture_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller truncatedPrefixFixture.frontEndAfter (truncatedPrefixFixture.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[truncatedPrefixFixture.frontEndTicks + 1] (some (truncatedPrefixFixture.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) truncatedPrefixFixture.beforeClear ctx)
  have sameData : truncatedPrefixFixture.frontEndAfter = truncatedPrefixFixture.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem truncatedPrefixFixture_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    truncatedPrefixFixture.RunExpected (step caller) regs ctx := by
  have first := truncatedPrefixFixture_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller truncatedPrefixFixture.frontEndAfter (truncatedPrefixFixture.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 truncatedPrefixFixture.frontEndAfter
    (answerRegisters false (truncatedPrefixFixture.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawF03_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawF03.frontEndTicks (rawF03.start regs ctx) (rawF03.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawF03.raw ctx

theorem rawF03_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF03.IntermediateExpected (step caller) regs ctx := by
  have first := rawF03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawF03.frontEndAfter (rawF03.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[rawF03.frontEndTicks + 1] (some (rawF03.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) rawF03.beforeClear ctx)
  have sameData : rawF03.frontEndAfter = rawF03.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem rawF03_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF03.RunExpected (step caller) regs ctx := by
  have first := rawF03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawF03.frontEndAfter (rawF03.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 rawF03.frontEndAfter
    (answerRegisters false (rawF03.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawF04_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawF04.frontEndTicks (rawF04.start regs ctx) (rawF04.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawF04.raw ctx

theorem rawF04_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF04.IntermediateExpected (step caller) regs ctx := by
  have first := rawF04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawF04.frontEndAfter (rawF04.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[rawF04.frontEndTicks + 1] (some (rawF04.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) rawF04.beforeClear ctx)
  have sameData : rawF04.frontEndAfter = rawF04.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem rawF04_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF04.RunExpected (step caller) regs ctx := by
  have first := rawF04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawF04.frontEndAfter (rawF04.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 rawF04.frontEndAfter
    (answerRegisters false (rawF04.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawF05_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawF05.frontEndTicks (rawF05.start regs ctx) (rawF05.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawF05.raw ctx

theorem rawF05_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF05.IntermediateExpected (step caller) regs ctx := by
  have first := rawF05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawF05.frontEndAfter (rawF05.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[rawF05.frontEndTicks + 1] (some (rawF05.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) rawF05.beforeClear ctx)
  have sameData : rawF05.frontEndAfter = rawF05.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem rawF05_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF05.RunExpected (step caller) regs ctx := by
  have first := rawF05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawF05.frontEndAfter (rawF05.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 rawF05.frontEndAfter
    (answerRegisters false (rawF05.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawF06_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawF06.frontEndTicks (rawF06.start regs ctx) (rawF06.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawF06.raw ctx

theorem rawF06_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF06.IntermediateExpected (step caller) regs ctx := by
  have first := rawF06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawF06.frontEndAfter (rawF06.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[rawF06.frontEndTicks + 1] (some (rawF06.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) rawF06.beforeClear ctx)
  have sameData : rawF06.frontEndAfter = rawF06.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem rawF06_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF06.RunExpected (step caller) regs ctx := by
  have first := rawF06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawF06.frontEndAfter (rawF06.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 rawF06.frontEndAfter
    (answerRegisters false (rawF06.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawF07_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawF07.frontEndTicks (rawF07.start regs ctx) (rawF07.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawF07.raw ctx

theorem rawF07_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF07.IntermediateExpected (step caller) regs ctx := by
  have first := rawF07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawF07.frontEndAfter (rawF07.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[rawF07.frontEndTicks + 1] (some (rawF07.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) rawF07.beforeClear ctx)
  have sameData : rawF07.frontEndAfter = rawF07.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem rawF07_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF07.RunExpected (step caller) regs ctx := by
  have first := rawF07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawF07.frontEndAfter (rawF07.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 rawF07.frontEndAfter
    (answerRegisters false (rawF07.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawF08_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawF08.frontEndTicks (rawF08.start regs ctx) (rawF08.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawF08.raw ctx

theorem rawF08_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF08.IntermediateExpected (step caller) regs ctx := by
  have first := rawF08_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawF08.frontEndAfter (rawF08.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[rawF08.frontEndTicks + 1] (some (rawF08.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) rawF08.beforeClear ctx)
  have sameData : rawF08.frontEndAfter = rawF08.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem rawF08_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF08.RunExpected (step caller) regs ctx := by
  have first := rawF08_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawF08.frontEndAfter (rawF08.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 rawF08.frontEndAfter
    (answerRegisters false (rawF08.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawI01_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawI01.frontEndTicks (rawI01.start regs ctx) (rawI01.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawI01.raw ctx

theorem rawI01_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI01.IntermediateExpected (step caller) regs ctx := by
  have first := rawI01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawI01.frontEndAfter (rawI01.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[rawI01.frontEndTicks + 1] (some (rawI01.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) rawI01.beforeClear ctx)
  have sameData : rawI01.frontEndAfter = rawI01.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem rawI01_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI01.RunExpected (step caller) regs ctx := by
  have first := rawI01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawI01.frontEndAfter (rawI01.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 rawI01.frontEndAfter
    (answerRegisters false (rawI01.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawI02_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawI02.frontEndTicks (rawI02.start regs ctx) (rawI02.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawI02.raw ctx

theorem rawI02_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI02.IntermediateExpected (step caller) regs ctx := by
  have first := rawI02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawI02.frontEndAfter (rawI02.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[rawI02.frontEndTicks + 1] (some (rawI02.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) rawI02.beforeClear ctx)
  have sameData : rawI02.frontEndAfter = rawI02.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem rawI02_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI02.RunExpected (step caller) regs ctx := by
  have first := rawI02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawI02.frontEndAfter (rawI02.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 rawI02.frontEndAfter
    (answerRegisters false (rawI02.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawI03_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawI03.frontEndTicks (rawI03.start regs ctx) (rawI03.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawI03.raw ctx

theorem rawI03_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI03.IntermediateExpected (step caller) regs ctx := by
  have first := rawI03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawI03.frontEndAfter (rawI03.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[rawI03.frontEndTicks + 1] (some (rawI03.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) rawI03.beforeClear ctx)
  have sameData : rawI03.frontEndAfter = rawI03.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem rawI03_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI03.RunExpected (step caller) regs ctx := by
  have first := rawI03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawI03.frontEndAfter (rawI03.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 rawI03.frontEndAfter
    (answerRegisters false (rawI03.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawI04_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawI04.frontEndTicks (rawI04.start regs ctx) (rawI04.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawI04.raw ctx

theorem rawI04_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI04.IntermediateExpected (step caller) regs ctx := by
  have first := rawI04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawI04.frontEndAfter (rawI04.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[rawI04.frontEndTicks + 1] (some (rawI04.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) rawI04.beforeClear ctx)
  have sameData : rawI04.frontEndAfter = rawI04.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem rawI04_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI04.RunExpected (step caller) regs ctx := by
  have first := rawI04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawI04.frontEndAfter (rawI04.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 rawI04.frontEndAfter
    (answerRegisters false (rawI04.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawI05_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawI05.frontEndTicks (rawI05.start regs ctx) (rawI05.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawI05.raw ctx

theorem rawI05_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI05.IntermediateExpected (step caller) regs ctx := by
  have first := rawI05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawI05.frontEndAfter (rawI05.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[rawI05.frontEndTicks + 1] (some (rawI05.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) rawI05.beforeClear ctx)
  have sameData : rawI05.frontEndAfter = rawI05.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem rawI05_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI05.RunExpected (step caller) regs ctx := by
  have first := rawI05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawI05.frontEndAfter (rawI05.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 rawI05.frontEndAfter
    (answerRegisters false (rawI05.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawI06_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawI06.frontEndTicks (rawI06.start regs ctx) (rawI06.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawI06.raw ctx

theorem rawI06_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI06.IntermediateExpected (step caller) regs ctx := by
  have first := rawI06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawI06.frontEndAfter (rawI06.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[rawI06.frontEndTicks + 1] (some (rawI06.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) rawI06.beforeClear ctx)
  have sameData : rawI06.frontEndAfter = rawI06.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem rawI06_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI06.RunExpected (step caller) regs ctx := by
  have first := rawI06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawI06.frontEndAfter (rawI06.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 rawI06.frontEndAfter
    (answerRegisters false (rawI06.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawI07_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawI07.frontEndTicks (rawI07.start regs ctx) (rawI07.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawI07.raw ctx

theorem rawI07_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI07.IntermediateExpected (step caller) regs ctx := by
  have first := rawI07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawI07.frontEndAfter (rawI07.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[rawI07.frontEndTicks + 1] (some (rawI07.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) rawI07.beforeClear ctx)
  have sameData : rawI07.frontEndAfter = rawI07.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem rawI07_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI07.RunExpected (step caller) regs ctx := by
  have first := rawI07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawI07.frontEndAfter (rawI07.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 rawI07.frontEndAfter
    (answerRegisters false (rawI07.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawC01_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawC01.frontEndTicks (rawC01.start regs ctx) (rawC01.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawC01.raw ctx

theorem rawC01_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawC01.IntermediateExpected (step caller) regs ctx := by
  have first := rawC01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawC01.frontEndAfter (rawC01.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[rawC01.frontEndTicks + 1] (some (rawC01.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) rawC01.beforeClear ctx)
  have sameData : rawC01.frontEndAfter = rawC01.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem rawC01_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawC01.RunExpected (step caller) regs ctx := by
  have first := rawC01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawC01.frontEndAfter (rawC01.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 rawC01.frontEndAfter
    (answerRegisters false (rawC01.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawC02_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawC02.frontEndTicks (rawC02.start regs ctx) (rawC02.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawC02.raw ctx

theorem rawC02_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawC02.IntermediateExpected (step caller) regs ctx := by
  have first := rawC02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawC02.frontEndAfter (rawC02.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[rawC02.frontEndTicks + 1] (some (rawC02.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) rawC02.beforeClear ctx)
  have sameData : rawC02.frontEndAfter = rawC02.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem rawC02_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawC02.RunExpected (step caller) regs ctx := by
  have first := rawC02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawC02.frontEndAfter (rawC02.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 rawC02.frontEndAfter
    (answerRegisters false (rawC02.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawC03_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawC03.frontEndTicks (rawC03.start regs ctx) (rawC03.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawC03.raw ctx

theorem rawC03_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawC03.IntermediateExpected (step caller) regs ctx := by
  have first := rawC03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawC03.frontEndAfter (rawC03.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[rawC03.frontEndTicks + 1] (some (rawC03.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) rawC03.beforeClear ctx)
  have sameData : rawC03.frontEndAfter = rawC03.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem rawC03_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawC03.RunExpected (step caller) regs ctx := by
  have first := rawC03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller rawC03.frontEndAfter (rawC03.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 rawC03.frontEndAfter
    (answerRegisters false (rawC03.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV01_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV01.frontEndTicks (rawV01.start regs ctx) (rawV01.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV01.raw ctx

theorem rawV01_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV01.IntermediateExpected (step caller) regs ctx := by
  have first := rawV01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV01.frontEndAfter (rawV01.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV01_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV01.result rawV01.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV01_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV01.RunExpected (step caller) regs ctx := by
  have first := rawV01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV01.frontEndAfter (rawV01.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV01_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV01.result rawV01.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV01.beforeClear
    (answerRegisters rawV01.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV02_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV02.frontEndTicks (rawV02.start regs ctx) (rawV02.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV02.raw ctx

theorem rawV02_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV02.IntermediateExpected (step caller) regs ctx := by
  have first := rawV02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV02.frontEndAfter (rawV02.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV02_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV02.result rawV02.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV02_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV02.RunExpected (step caller) regs ctx := by
  have first := rawV02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV02.frontEndAfter (rawV02.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV02_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV02.result rawV02.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV02.beforeClear
    (answerRegisters rawV02.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV03_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV03.frontEndTicks (rawV03.start regs ctx) (rawV03.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV03.raw ctx

theorem rawV03_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV03.IntermediateExpected (step caller) regs ctx := by
  have first := rawV03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV03.frontEndAfter (rawV03.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV03_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV03.result rawV03.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV03_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV03.RunExpected (step caller) regs ctx := by
  have first := rawV03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV03.frontEndAfter (rawV03.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV03_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV03.result rawV03.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV03.beforeClear
    (answerRegisters rawV03.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV04_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV04.frontEndTicks (rawV04.start regs ctx) (rawV04.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV04.raw ctx

theorem rawV04_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV04.IntermediateExpected (step caller) regs ctx := by
  have first := rawV04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV04.frontEndAfter (rawV04.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV04_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV04.result rawV04.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV04_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV04.RunExpected (step caller) regs ctx := by
  have first := rawV04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV04.frontEndAfter (rawV04.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV04_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV04.result rawV04.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV04.beforeClear
    (answerRegisters rawV04.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV05_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV05.frontEndTicks (rawV05.start regs ctx) (rawV05.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV05.raw ctx

theorem rawV05_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV05.IntermediateExpected (step caller) regs ctx := by
  have first := rawV05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV05.frontEndAfter (rawV05.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV05_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV05.result rawV05.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV05_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV05.RunExpected (step caller) regs ctx := by
  have first := rawV05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV05.frontEndAfter (rawV05.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV05_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV05.result rawV05.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV05.beforeClear
    (answerRegisters rawV05.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV06_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV06.frontEndTicks (rawV06.start regs ctx) (rawV06.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV06.raw ctx

theorem rawV06_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV06.IntermediateExpected (step caller) regs ctx := by
  have first := rawV06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV06.frontEndAfter (rawV06.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV06_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV06.result rawV06.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV06_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV06.RunExpected (step caller) regs ctx := by
  have first := rawV06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV06.frontEndAfter (rawV06.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV06_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV06.result rawV06.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV06.beforeClear
    (answerRegisters rawV06.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV07_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV07.frontEndTicks (rawV07.start regs ctx) (rawV07.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV07.raw ctx

theorem rawV07_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV07.IntermediateExpected (step caller) regs ctx := by
  have first := rawV07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV07.frontEndAfter (rawV07.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV07_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV07.result rawV07.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV07_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV07.RunExpected (step caller) regs ctx := by
  have first := rawV07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV07.frontEndAfter (rawV07.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV07_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV07.result rawV07.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV07.beforeClear
    (answerRegisters rawV07.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV08_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV08.frontEndTicks (rawV08.start regs ctx) (rawV08.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV08.raw ctx

theorem rawV08_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV08.IntermediateExpected (step caller) regs ctx := by
  have first := rawV08_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV08.frontEndAfter (rawV08.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV08_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV08.result rawV08.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV08_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV08.RunExpected (step caller) regs ctx := by
  have first := rawV08_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV08.frontEndAfter (rawV08.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV08_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV08.result rawV08.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV08.beforeClear
    (answerRegisters rawV08.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV09_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV09.frontEndTicks (rawV09.start regs ctx) (rawV09.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV09.raw ctx

theorem rawV09_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV09.IntermediateExpected (step caller) regs ctx := by
  have first := rawV09_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV09.frontEndAfter (rawV09.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV09_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV09.result rawV09.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV09_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV09.RunExpected (step caller) regs ctx := by
  have first := rawV09_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV09.frontEndAfter (rawV09.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV09_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV09.result rawV09.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV09.beforeClear
    (answerRegisters rawV09.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV10_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV10.frontEndTicks (rawV10.start regs ctx) (rawV10.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV10.raw ctx

theorem rawV10_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV10.IntermediateExpected (step caller) regs ctx := by
  have first := rawV10_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV10.frontEndAfter (rawV10.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV10_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV10.result rawV10.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV10_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV10.RunExpected (step caller) regs ctx := by
  have first := rawV10_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV10.frontEndAfter (rawV10.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV10_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV10.result rawV10.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV10.beforeClear
    (answerRegisters rawV10.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV11_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV11.frontEndTicks (rawV11.start regs ctx) (rawV11.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV11.raw ctx

theorem rawV11_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV11.IntermediateExpected (step caller) regs ctx := by
  have first := rawV11_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV11.frontEndAfter (rawV11.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV11_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV11.result rawV11.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV11_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV11.RunExpected (step caller) regs ctx := by
  have first := rawV11_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV11.frontEndAfter (rawV11.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV11_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV11.result rawV11.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV11.beforeClear
    (answerRegisters rawV11.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV12_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV12.frontEndTicks (rawV12.start regs ctx) (rawV12.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV12.raw ctx

theorem rawV12_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV12.IntermediateExpected (step caller) regs ctx := by
  have first := rawV12_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV12.frontEndAfter (rawV12.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV12_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV12.result rawV12.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV12_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV12.RunExpected (step caller) regs ctx := by
  have first := rawV12_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV12.frontEndAfter (rawV12.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV12_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV12.result rawV12.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV12.beforeClear
    (answerRegisters rawV12.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV13_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV13.frontEndTicks (rawV13.start regs ctx) (rawV13.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV13.raw ctx

theorem rawV13_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV13.IntermediateExpected (step caller) regs ctx := by
  have first := rawV13_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV13.frontEndAfter (rawV13.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV13_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV13.result rawV13.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV13_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV13.RunExpected (step caller) regs ctx := by
  have first := rawV13_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV13.frontEndAfter (rawV13.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV13_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV13.result rawV13.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV13.beforeClear
    (answerRegisters rawV13.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV14_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV14.frontEndTicks (rawV14.start regs ctx) (rawV14.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV14.raw ctx

theorem rawV14_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV14.IntermediateExpected (step caller) regs ctx := by
  have first := rawV14_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV14.frontEndAfter (rawV14.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV14_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV14.result rawV14.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV14_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV14.RunExpected (step caller) regs ctx := by
  have first := rawV14_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV14.frontEndAfter (rawV14.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV14_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV14.result rawV14.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV14.beforeClear
    (answerRegisters rawV14.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV15_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV15.frontEndTicks (rawV15.start regs ctx) (rawV15.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV15.raw ctx

theorem rawV15_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV15.IntermediateExpected (step caller) regs ctx := by
  have first := rawV15_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV15.frontEndAfter (rawV15.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV15_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV15.result rawV15.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV15_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV15.RunExpected (step caller) regs ctx := by
  have first := rawV15_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV15.frontEndAfter (rawV15.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV15_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV15.result rawV15.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV15.beforeClear
    (answerRegisters rawV15.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV16_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV16.frontEndTicks (rawV16.start regs ctx) (rawV16.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV16.raw ctx

theorem rawV16_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV16.IntermediateExpected (step caller) regs ctx := by
  have first := rawV16_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV16.frontEndAfter (rawV16.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV16_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV16.result rawV16.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV16_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV16.RunExpected (step caller) regs ctx := by
  have first := rawV16_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV16.frontEndAfter (rawV16.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV16_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV16.result rawV16.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV16.beforeClear
    (answerRegisters rawV16.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV17_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV17.frontEndTicks (rawV17.start regs ctx) (rawV17.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV17.raw ctx

theorem rawV17_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV17.IntermediateExpected (step caller) regs ctx := by
  have first := rawV17_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV17.frontEndAfter (rawV17.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV17_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV17.result rawV17.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV17_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV17.RunExpected (step caller) regs ctx := by
  have first := rawV17_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV17.frontEndAfter (rawV17.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV17_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV17.result rawV17.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV17.beforeClear
    (answerRegisters rawV17.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem rawV18_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller rawV18.frontEndTicks (rawV18.start regs ctx) (rawV18.frontEndFinish regs ctx) :=
  front_end_clean_localRun caller regs rawV18.raw ctx

theorem rawV18_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV18.IntermediateExpected (step caller) regs ctx := by
  have first := rawV18_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV18.frontEndAfter (rawV18.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV18_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV18.result rawV18.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem rawV18_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV18.RunExpected (step caller) regs ctx := by
  have first := rawV18_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller rawV18.frontEndAfter (rawV18.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (rawV18_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller rawV18.result rawV18.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 rawV18.beforeClear
    (answerRegisters rawV18.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

/-- Actual first-halt uniqueness identifies the proof-side clock without defining a fixture by it. -/
theorem an_actual_raw_fixture_has_the_canonical_clock
    (fixture : RawFixture) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (checked : fixture.RunExpected (step caller) regs ctx) : fixture.ticks = runSteps fixture.raw := by
  have first := LocalRun.of_iterate caller checked.1 checked.2.2
  have canonical := run_localRun caller regs fixture.raw ctx
  apply (LocalRun.first_unique caller first canonical ?_ ?_).1
  · rw [checked.2.1]
    exact not_owned_none
  · rw [runResult_eq]
    exact not_owned_none

variable [Fintype K]

theorem emptyRawFixture_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (emptyRawFixture.start regs ctx) emptyRawFixture.ticks (emptyRawFixture.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller emptyRawFixture regs ctx
    (emptyRawFixture_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs emptyRawFixture.raw ctx)
  rw [← clock] at peak
  exact peak

theorem emptyRawFixture_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    emptyRawFixture.Expected (step caller) regs ctx :=
  ⟨emptyRawFixture_actual_first_halt caller regs ctx, emptyRawFixture_actual_intermediates caller regs ctx,
    by trivial, emptyRawFixture_actual_exact_peak caller regs ctx⟩

theorem truncatedPrefixFixture_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (truncatedPrefixFixture.start regs ctx) truncatedPrefixFixture.ticks (truncatedPrefixFixture.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller truncatedPrefixFixture regs ctx
    (truncatedPrefixFixture_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs truncatedPrefixFixture.raw ctx)
  rw [← clock] at peak
  exact peak

theorem truncatedPrefixFixture_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    truncatedPrefixFixture.Expected (step caller) regs ctx :=
  ⟨truncatedPrefixFixture_actual_first_halt caller regs ctx, truncatedPrefixFixture_actual_intermediates caller regs ctx,
    by trivial, truncatedPrefixFixture_actual_exact_peak caller regs ctx⟩

theorem rawF03_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawF03.start regs ctx) rawF03.ticks (rawF03.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawF03 regs ctx
    (rawF03_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawF03.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawF03_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF03.Expected (step caller) regs ctx :=
  ⟨rawF03_actual_first_halt caller regs ctx, rawF03_actual_intermediates caller regs ctx,
    by trivial, rawF03_actual_exact_peak caller regs ctx⟩

theorem rawF04_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawF04.start regs ctx) rawF04.ticks (rawF04.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawF04 regs ctx
    (rawF04_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawF04.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawF04_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF04.Expected (step caller) regs ctx :=
  ⟨rawF04_actual_first_halt caller regs ctx, rawF04_actual_intermediates caller regs ctx,
    by trivial, rawF04_actual_exact_peak caller regs ctx⟩

theorem rawF05_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawF05.start regs ctx) rawF05.ticks (rawF05.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawF05 regs ctx
    (rawF05_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawF05.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawF05_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF05.Expected (step caller) regs ctx :=
  ⟨rawF05_actual_first_halt caller regs ctx, rawF05_actual_intermediates caller regs ctx,
    by trivial, rawF05_actual_exact_peak caller regs ctx⟩

theorem rawF06_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawF06.start regs ctx) rawF06.ticks (rawF06.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawF06 regs ctx
    (rawF06_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawF06.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawF06_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF06.Expected (step caller) regs ctx :=
  ⟨rawF06_actual_first_halt caller regs ctx, rawF06_actual_intermediates caller regs ctx,
    by trivial, rawF06_actual_exact_peak caller regs ctx⟩

theorem rawF07_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawF07.start regs ctx) rawF07.ticks (rawF07.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawF07 regs ctx
    (rawF07_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawF07.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawF07_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF07.Expected (step caller) regs ctx :=
  ⟨rawF07_actual_first_halt caller regs ctx, rawF07_actual_intermediates caller regs ctx,
    by trivial, rawF07_actual_exact_peak caller regs ctx⟩

theorem rawF08_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawF08.start regs ctx) rawF08.ticks (rawF08.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawF08 regs ctx
    (rawF08_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawF08.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawF08_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawF08.Expected (step caller) regs ctx :=
  ⟨rawF08_actual_first_halt caller regs ctx, rawF08_actual_intermediates caller regs ctx,
    by trivial, rawF08_actual_exact_peak caller regs ctx⟩

theorem rawI01_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawI01.start regs ctx) rawI01.ticks (rawI01.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawI01 regs ctx
    (rawI01_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawI01.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawI01_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI01.Expected (step caller) regs ctx :=
  ⟨rawI01_actual_first_halt caller regs ctx, rawI01_actual_intermediates caller regs ctx,
    by trivial, rawI01_actual_exact_peak caller regs ctx⟩

theorem rawI02_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawI02.start regs ctx) rawI02.ticks (rawI02.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawI02 regs ctx
    (rawI02_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawI02.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawI02_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI02.Expected (step caller) regs ctx :=
  ⟨rawI02_actual_first_halt caller regs ctx, rawI02_actual_intermediates caller regs ctx,
    by trivial, rawI02_actual_exact_peak caller regs ctx⟩

theorem rawI03_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawI03.start regs ctx) rawI03.ticks (rawI03.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawI03 regs ctx
    (rawI03_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawI03.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawI03_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI03.Expected (step caller) regs ctx :=
  ⟨rawI03_actual_first_halt caller regs ctx, rawI03_actual_intermediates caller regs ctx,
    by trivial, rawI03_actual_exact_peak caller regs ctx⟩

theorem rawI04_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawI04.start regs ctx) rawI04.ticks (rawI04.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawI04 regs ctx
    (rawI04_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawI04.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawI04_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI04.Expected (step caller) regs ctx :=
  ⟨rawI04_actual_first_halt caller regs ctx, rawI04_actual_intermediates caller regs ctx,
    by trivial, rawI04_actual_exact_peak caller regs ctx⟩

theorem rawI05_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawI05.start regs ctx) rawI05.ticks (rawI05.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawI05 regs ctx
    (rawI05_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawI05.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawI05_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI05.Expected (step caller) regs ctx :=
  ⟨rawI05_actual_first_halt caller regs ctx, rawI05_actual_intermediates caller regs ctx,
    by trivial, rawI05_actual_exact_peak caller regs ctx⟩

theorem rawI06_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawI06.start regs ctx) rawI06.ticks (rawI06.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawI06 regs ctx
    (rawI06_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawI06.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawI06_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI06.Expected (step caller) regs ctx :=
  ⟨rawI06_actual_first_halt caller regs ctx, rawI06_actual_intermediates caller regs ctx,
    by trivial, rawI06_actual_exact_peak caller regs ctx⟩

theorem rawI07_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawI07.start regs ctx) rawI07.ticks (rawI07.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawI07 regs ctx
    (rawI07_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawI07.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawI07_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawI07.Expected (step caller) regs ctx :=
  ⟨rawI07_actual_first_halt caller regs ctx, rawI07_actual_intermediates caller regs ctx,
    by trivial, rawI07_actual_exact_peak caller regs ctx⟩

theorem rawC01_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawC01.start regs ctx) rawC01.ticks (rawC01.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawC01 regs ctx
    (rawC01_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawC01.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawC01_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawC01.Expected (step caller) regs ctx :=
  ⟨rawC01_actual_first_halt caller regs ctx, rawC01_actual_intermediates caller regs ctx,
    by trivial, rawC01_actual_exact_peak caller regs ctx⟩

theorem rawC02_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawC02.start regs ctx) rawC02.ticks (rawC02.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawC02 regs ctx
    (rawC02_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawC02.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawC02_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawC02.Expected (step caller) regs ctx :=
  ⟨rawC02_actual_first_halt caller regs ctx, rawC02_actual_intermediates caller regs ctx,
    by trivial, rawC02_actual_exact_peak caller regs ctx⟩

theorem rawC03_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawC03.start regs ctx) rawC03.ticks (rawC03.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawC03 regs ctx
    (rawC03_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawC03.raw ctx)
  rw [← clock] at peak
  have literalPeak : max rawC03.raw.length 1 = rawC03.peak := by
    norm_num [rawC03]
  rw [literalPeak] at peak
  exact peak

theorem rawC03_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawC03.Expected (step caller) regs ctx :=
  ⟨rawC03_actual_first_halt caller regs ctx, rawC03_actual_intermediates caller regs ctx,
    by trivial, rawC03_actual_exact_peak caller regs ctx⟩

theorem rawV01_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV01.start regs ctx) rawV01.ticks (rawV01.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV01 regs ctx
    (rawV01_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV01.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawV01_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV01.Expected (step caller) regs ctx :=
  ⟨rawV01_actual_first_halt caller regs ctx, rawV01_actual_intermediates caller regs ctx,
    rawV01_stream_actual_exact_peak caller regs ctx, rawV01_actual_exact_peak caller regs ctx⟩

theorem rawV02_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV02.start regs ctx) rawV02.ticks (rawV02.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV02 regs ctx
    (rawV02_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV02.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawV02_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV02.Expected (step caller) regs ctx :=
  ⟨rawV02_actual_first_halt caller regs ctx, rawV02_actual_intermediates caller regs ctx,
    rawV02_stream_actual_exact_peak caller regs ctx, rawV02_actual_exact_peak caller regs ctx⟩

theorem rawV03_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV03.start regs ctx) rawV03.ticks (rawV03.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV03 regs ctx
    (rawV03_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV03.raw ctx)
  rw [← clock] at peak
  have literalPeak : max rawV03.raw.length 1 = rawV03.peak := by
    norm_num [rawV03]
  rw [literalPeak] at peak
  exact peak

theorem rawV03_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV03.Expected (step caller) regs ctx :=
  ⟨rawV03_actual_first_halt caller regs ctx, rawV03_actual_intermediates caller regs ctx,
    rawV03_stream_actual_exact_peak caller regs ctx, rawV03_actual_exact_peak caller regs ctx⟩

theorem rawV04_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV04.start regs ctx) rawV04.ticks (rawV04.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV04 regs ctx
    (rawV04_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV04.raw ctx)
  rw [← clock] at peak
  have literalPeak : max rawV04.raw.length 1 = rawV04.peak := by
    norm_num [rawV04]
  rw [literalPeak] at peak
  exact peak

theorem rawV04_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV04.Expected (step caller) regs ctx :=
  ⟨rawV04_actual_first_halt caller regs ctx, rawV04_actual_intermediates caller regs ctx,
    rawV04_stream_actual_exact_peak caller regs ctx, rawV04_actual_exact_peak caller regs ctx⟩

theorem rawV05_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV05.start regs ctx) rawV05.ticks (rawV05.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV05 regs ctx
    (rawV05_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV05.raw ctx)
  rw [← clock] at peak
  have literalPeak : max rawV05.raw.length 1 = rawV05.peak := by
    norm_num [rawV05]
  rw [literalPeak] at peak
  exact peak

theorem rawV05_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV05.Expected (step caller) regs ctx :=
  ⟨rawV05_actual_first_halt caller regs ctx, rawV05_actual_intermediates caller regs ctx,
    rawV05_stream_actual_exact_peak caller regs ctx, rawV05_actual_exact_peak caller regs ctx⟩

theorem rawV06_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV06.start regs ctx) rawV06.ticks (rawV06.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV06 regs ctx
    (rawV06_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV06.raw ctx)
  rw [← clock] at peak
  have literalPeak : max rawV06.raw.length 1 = rawV06.peak := by
    norm_num [rawV06]
  rw [literalPeak] at peak
  exact peak

theorem rawV06_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV06.Expected (step caller) regs ctx :=
  ⟨rawV06_actual_first_halt caller regs ctx, rawV06_actual_intermediates caller regs ctx,
    rawV06_stream_actual_exact_peak caller regs ctx, rawV06_actual_exact_peak caller regs ctx⟩

theorem rawV07_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV07.start regs ctx) rawV07.ticks (rawV07.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV07 regs ctx
    (rawV07_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV07.raw ctx)
  rw [← clock] at peak
  have literalPeak : max rawV07.raw.length 1 = rawV07.peak := by
    norm_num [rawV07]
  rw [literalPeak] at peak
  exact peak

theorem rawV07_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV07.Expected (step caller) regs ctx :=
  ⟨rawV07_actual_first_halt caller regs ctx, rawV07_actual_intermediates caller regs ctx,
    rawV07_stream_actual_exact_peak caller regs ctx, rawV07_actual_exact_peak caller regs ctx⟩

theorem rawV08_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV08.start regs ctx) rawV08.ticks (rawV08.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV08 regs ctx
    (rawV08_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV08.raw ctx)
  rw [← clock] at peak
  have literalPeak : max rawV08.raw.length 1 = rawV08.peak := by
    norm_num [rawV08]
  rw [literalPeak] at peak
  exact peak

theorem rawV08_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV08.Expected (step caller) regs ctx :=
  ⟨rawV08_actual_first_halt caller regs ctx, rawV08_actual_intermediates caller regs ctx,
    rawV08_stream_actual_exact_peak caller regs ctx, rawV08_actual_exact_peak caller regs ctx⟩

theorem rawV09_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV09.start regs ctx) rawV09.ticks (rawV09.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV09 regs ctx
    (rawV09_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV09.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawV09_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV09.Expected (step caller) regs ctx :=
  ⟨rawV09_actual_first_halt caller regs ctx, rawV09_actual_intermediates caller regs ctx,
    rawV09_stream_actual_exact_peak caller regs ctx, rawV09_actual_exact_peak caller regs ctx⟩

theorem rawV10_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV10.start regs ctx) rawV10.ticks (rawV10.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV10 regs ctx
    (rawV10_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV10.raw ctx)
  rw [← clock] at peak
  have literalPeak : max rawV10.raw.length 1 = rawV10.peak := by
    norm_num [rawV10]
  rw [literalPeak] at peak
  exact peak

theorem rawV10_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV10.Expected (step caller) regs ctx :=
  ⟨rawV10_actual_first_halt caller regs ctx, rawV10_actual_intermediates caller regs ctx,
    rawV10_stream_actual_exact_peak caller regs ctx, rawV10_actual_exact_peak caller regs ctx⟩

theorem rawV11_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV11.start regs ctx) rawV11.ticks (rawV11.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV11 regs ctx
    (rawV11_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV11.raw ctx)
  rw [← clock] at peak
  have literalPeak : max rawV11.raw.length 1 = rawV11.peak := by
    norm_num [rawV11]
  rw [literalPeak] at peak
  exact peak

theorem rawV11_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV11.Expected (step caller) regs ctx :=
  ⟨rawV11_actual_first_halt caller regs ctx, rawV11_actual_intermediates caller regs ctx,
    rawV11_stream_actual_exact_peak caller regs ctx, rawV11_actual_exact_peak caller regs ctx⟩

theorem rawV12_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV12.start regs ctx) rawV12.ticks (rawV12.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV12 regs ctx
    (rawV12_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV12.raw ctx)
  rw [← clock] at peak
  have literalPeak : max rawV12.raw.length 1 = rawV12.peak := by
    norm_num [rawV12]
  rw [literalPeak] at peak
  exact peak

theorem rawV12_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV12.Expected (step caller) regs ctx :=
  ⟨rawV12_actual_first_halt caller regs ctx, rawV12_actual_intermediates caller regs ctx,
    rawV12_stream_actual_exact_peak caller regs ctx, rawV12_actual_exact_peak caller regs ctx⟩

theorem rawV13_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV13.start regs ctx) rawV13.ticks (rawV13.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV13 regs ctx
    (rawV13_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV13.raw ctx)
  rw [← clock] at peak
  have literalPeak : max rawV13.raw.length 1 = rawV13.peak := by
    norm_num [rawV13]
  rw [literalPeak] at peak
  exact peak

theorem rawV13_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV13.Expected (step caller) regs ctx :=
  ⟨rawV13_actual_first_halt caller regs ctx, rawV13_actual_intermediates caller regs ctx,
    rawV13_stream_actual_exact_peak caller regs ctx, rawV13_actual_exact_peak caller regs ctx⟩

theorem rawV14_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV14.start regs ctx) rawV14.ticks (rawV14.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV14 regs ctx
    (rawV14_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV14.raw ctx)
  rw [← clock] at peak
  have literalPeak : max rawV14.raw.length 1 = rawV14.peak := by
    norm_num [rawV14]
  rw [literalPeak] at peak
  exact peak

theorem rawV14_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV14.Expected (step caller) regs ctx :=
  ⟨rawV14_actual_first_halt caller regs ctx, rawV14_actual_intermediates caller regs ctx,
    rawV14_stream_actual_exact_peak caller regs ctx, rawV14_actual_exact_peak caller regs ctx⟩

theorem rawV15_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV15.start regs ctx) rawV15.ticks (rawV15.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV15 regs ctx
    (rawV15_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV15.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawV15_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV15.Expected (step caller) regs ctx :=
  ⟨rawV15_actual_first_halt caller regs ctx, rawV15_actual_intermediates caller regs ctx,
    rawV15_stream_actual_exact_peak caller regs ctx, rawV15_actual_exact_peak caller regs ctx⟩

theorem rawV16_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV16.start regs ctx) rawV16.ticks (rawV16.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV16 regs ctx
    (rawV16_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV16.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawV16_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV16.Expected (step caller) regs ctx :=
  ⟨rawV16_actual_first_halt caller regs ctx, rawV16_actual_intermediates caller regs ctx,
    rawV16_stream_actual_exact_peak caller regs ctx, rawV16_actual_exact_peak caller regs ctx⟩

theorem rawV17_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV17.start regs ctx) rawV17.ticks (rawV17.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV17 regs ctx
    (rawV17_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV17.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawV17_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV17.Expected (step caller) regs ctx :=
  ⟨rawV17_actual_first_halt caller regs ctx, rawV17_actual_intermediates caller regs ctx,
    rawV17_stream_actual_exact_peak caller regs ctx, rawV17_actual_exact_peak caller regs ctx⟩

theorem rawV18_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (rawV18.start regs ctx) rawV18.ticks (rawV18.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller rawV18 regs ctx
    (rawV18_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs rawV18.raw ctx)
  rw [← clock] at peak
  exact peak

theorem rawV18_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    rawV18.Expected (step caller) regs ctx :=
  ⟨rawV18_actual_first_halt caller regs ctx, rawV18_actual_intermediates caller regs ctx,
    rawV18_stream_actual_exact_peak caller regs ctx, rawV18_actual_exact_peak caller regs ctx⟩

theorem all_original_raw_rows_execute_with_their_complete_endpoints_and_peaks
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∀ fixture ∈ rawCases, fixture.Expected (step caller) regs ctx := by
  intro fixture member
  simp only [rawCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact emptyRawFixture_expected caller regs ctx
  · exact truncatedPrefixFixture_expected caller regs ctx
  · exact rawF03_expected caller regs ctx
  · exact rawF04_expected caller regs ctx
  · exact rawF05_expected caller regs ctx
  · exact rawF06_expected caller regs ctx
  · exact rawF07_expected caller regs ctx
  · exact rawF08_expected caller regs ctx
  · exact rawI01_expected caller regs ctx
  · exact rawI02_expected caller regs ctx
  · exact rawI03_expected caller regs ctx
  · exact rawI04_expected caller regs ctx
  · exact rawI05_expected caller regs ctx
  · exact rawI06_expected caller regs ctx
  · exact rawI07_expected caller regs ctx
  · exact rawC01_expected caller regs ctx
  · exact rawC02_expected caller regs ctx
  · exact rawC03_expected caller regs ctx
  · exact rawV01_expected caller regs ctx
  · exact rawV02_expected caller regs ctx
  · exact rawV03_expected caller regs ctx
  · exact rawV04_expected caller regs ctx
  · exact rawV05_expected caller regs ctx
  · exact rawV06_expected caller regs ctx
  · exact rawV07_expected caller regs ctx
  · exact rawV08_expected caller regs ctx
  · exact rawV09_expected caller regs ctx
  · exact rawV10_expected caller regs ctx
  · exact rawV11_expected caller regs ctx
  · exact rawV12_expected caller regs ctx
  · exact rawV13_expected caller regs ctx
  · exact rawV14_expected caller regs ctx
  · exact rawV15_expected caller regs ctx
  · exact rawV16_expected caller regs ctx
  · exact rawV17_expected caller regs ctx
  · exact rawV18_expected caller regs ctx

end LiteralRawRuns

/-! The operational raw-case aggregate has no finite-context hypothesis. -/

theorem all_original_raw_rows_have_their_actual_first_halt
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (fixture : RawFixture) (member : fixture ∈ rawCases) :
    fixture.RunExpected (step caller) regs ctx := by
  simp only [rawCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact emptyRawFixture_actual_first_halt caller regs ctx
  · exact truncatedPrefixFixture_actual_first_halt caller regs ctx
  · exact rawF03_actual_first_halt caller regs ctx
  · exact rawF04_actual_first_halt caller regs ctx
  · exact rawF05_actual_first_halt caller regs ctx
  · exact rawF06_actual_first_halt caller regs ctx
  · exact rawF07_actual_first_halt caller regs ctx
  · exact rawF08_actual_first_halt caller regs ctx
  · exact rawI01_actual_first_halt caller regs ctx
  · exact rawI02_actual_first_halt caller regs ctx
  · exact rawI03_actual_first_halt caller regs ctx
  · exact rawI04_actual_first_halt caller regs ctx
  · exact rawI05_actual_first_halt caller regs ctx
  · exact rawI06_actual_first_halt caller regs ctx
  · exact rawI07_actual_first_halt caller regs ctx
  · exact rawC01_actual_first_halt caller regs ctx
  · exact rawC02_actual_first_halt caller regs ctx
  · exact rawC03_actual_first_halt caller regs ctx
  · exact rawV01_actual_first_halt caller regs ctx
  · exact rawV02_actual_first_halt caller regs ctx
  · exact rawV03_actual_first_halt caller regs ctx
  · exact rawV04_actual_first_halt caller regs ctx
  · exact rawV05_actual_first_halt caller regs ctx
  · exact rawV06_actual_first_halt caller regs ctx
  · exact rawV07_actual_first_halt caller regs ctx
  · exact rawV08_actual_first_halt caller regs ctx
  · exact rawV09_actual_first_halt caller regs ctx
  · exact rawV10_actual_first_halt caller regs ctx
  · exact rawV11_actual_first_halt caller regs ctx
  · exact rawV12_actual_first_halt caller regs ctx
  · exact rawV13_actual_first_halt caller regs ctx
  · exact rawV14_actual_first_halt caller regs ctx
  · exact rawV15_actual_first_halt caller regs ctx
  · exact rawV16_actual_first_halt caller regs ctx
  · exact rawV17_actual_first_halt caller regs ctx
  · exact rawV18_actual_first_halt caller regs ctx


end Examples.RotationCertificateFrontEndStreamMachine
