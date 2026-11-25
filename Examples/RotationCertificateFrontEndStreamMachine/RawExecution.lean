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

theorem raw_F01_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_F01.frontEndTicks (raw_F01.start regs ctx) (raw_F01.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_F01.raw ctx

theorem raw_F01_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F01.IntermediateExpected (step caller) regs ctx := by
  have first := raw_F01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F01.frontEndAfter (raw_F01.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_F01.frontEndTicks + 1] (some (raw_F01.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_F01.beforeClear ctx)
  have sameData : raw_F01.frontEndAfter = raw_F01.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_F01_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F01.RunExpected (step caller) regs ctx := by
  have first := raw_F01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F01.frontEndAfter (raw_F01.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_F01.frontEndAfter
    (answerRegisters false (raw_F01.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_F02_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_F02.frontEndTicks (raw_F02.start regs ctx) (raw_F02.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_F02.raw ctx

theorem raw_F02_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F02.IntermediateExpected (step caller) regs ctx := by
  have first := raw_F02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F02.frontEndAfter (raw_F02.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_F02.frontEndTicks + 1] (some (raw_F02.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_F02.beforeClear ctx)
  have sameData : raw_F02.frontEndAfter = raw_F02.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_F02_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F02.RunExpected (step caller) regs ctx := by
  have first := raw_F02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F02.frontEndAfter (raw_F02.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_F02.frontEndAfter
    (answerRegisters false (raw_F02.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_F03_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_F03.frontEndTicks (raw_F03.start regs ctx) (raw_F03.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_F03.raw ctx

theorem raw_F03_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F03.IntermediateExpected (step caller) regs ctx := by
  have first := raw_F03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F03.frontEndAfter (raw_F03.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_F03.frontEndTicks + 1] (some (raw_F03.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_F03.beforeClear ctx)
  have sameData : raw_F03.frontEndAfter = raw_F03.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_F03_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F03.RunExpected (step caller) regs ctx := by
  have first := raw_F03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F03.frontEndAfter (raw_F03.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_F03.frontEndAfter
    (answerRegisters false (raw_F03.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_F04_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_F04.frontEndTicks (raw_F04.start regs ctx) (raw_F04.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_F04.raw ctx

theorem raw_F04_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F04.IntermediateExpected (step caller) regs ctx := by
  have first := raw_F04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F04.frontEndAfter (raw_F04.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_F04.frontEndTicks + 1] (some (raw_F04.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_F04.beforeClear ctx)
  have sameData : raw_F04.frontEndAfter = raw_F04.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_F04_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F04.RunExpected (step caller) regs ctx := by
  have first := raw_F04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F04.frontEndAfter (raw_F04.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_F04.frontEndAfter
    (answerRegisters false (raw_F04.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_F05_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_F05.frontEndTicks (raw_F05.start regs ctx) (raw_F05.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_F05.raw ctx

theorem raw_F05_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F05.IntermediateExpected (step caller) regs ctx := by
  have first := raw_F05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F05.frontEndAfter (raw_F05.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_F05.frontEndTicks + 1] (some (raw_F05.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_F05.beforeClear ctx)
  have sameData : raw_F05.frontEndAfter = raw_F05.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_F05_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F05.RunExpected (step caller) regs ctx := by
  have first := raw_F05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F05.frontEndAfter (raw_F05.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_F05.frontEndAfter
    (answerRegisters false (raw_F05.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_F06_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_F06.frontEndTicks (raw_F06.start regs ctx) (raw_F06.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_F06.raw ctx

theorem raw_F06_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F06.IntermediateExpected (step caller) regs ctx := by
  have first := raw_F06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F06.frontEndAfter (raw_F06.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_F06.frontEndTicks + 1] (some (raw_F06.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_F06.beforeClear ctx)
  have sameData : raw_F06.frontEndAfter = raw_F06.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_F06_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F06.RunExpected (step caller) regs ctx := by
  have first := raw_F06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F06.frontEndAfter (raw_F06.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_F06.frontEndAfter
    (answerRegisters false (raw_F06.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_F07_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_F07.frontEndTicks (raw_F07.start regs ctx) (raw_F07.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_F07.raw ctx

theorem raw_F07_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F07.IntermediateExpected (step caller) regs ctx := by
  have first := raw_F07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F07.frontEndAfter (raw_F07.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_F07.frontEndTicks + 1] (some (raw_F07.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_F07.beforeClear ctx)
  have sameData : raw_F07.frontEndAfter = raw_F07.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_F07_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F07.RunExpected (step caller) regs ctx := by
  have first := raw_F07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F07.frontEndAfter (raw_F07.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_F07.frontEndAfter
    (answerRegisters false (raw_F07.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_F08_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_F08.frontEndTicks (raw_F08.start regs ctx) (raw_F08.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_F08.raw ctx

theorem raw_F08_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F08.IntermediateExpected (step caller) regs ctx := by
  have first := raw_F08_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F08.frontEndAfter (raw_F08.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_F08.frontEndTicks + 1] (some (raw_F08.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_F08.beforeClear ctx)
  have sameData : raw_F08.frontEndAfter = raw_F08.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_F08_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F08.RunExpected (step caller) regs ctx := by
  have first := raw_F08_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F08.frontEndAfter (raw_F08.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_F08.frontEndAfter
    (answerRegisters false (raw_F08.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_I01_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_I01.frontEndTicks (raw_I01.start regs ctx) (raw_I01.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_I01.raw ctx

theorem raw_I01_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I01.IntermediateExpected (step caller) regs ctx := by
  have first := raw_I01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I01.frontEndAfter (raw_I01.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_I01.frontEndTicks + 1] (some (raw_I01.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_I01.beforeClear ctx)
  have sameData : raw_I01.frontEndAfter = raw_I01.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_I01_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I01.RunExpected (step caller) regs ctx := by
  have first := raw_I01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I01.frontEndAfter (raw_I01.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_I01.frontEndAfter
    (answerRegisters false (raw_I01.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_I02_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_I02.frontEndTicks (raw_I02.start regs ctx) (raw_I02.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_I02.raw ctx

theorem raw_I02_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I02.IntermediateExpected (step caller) regs ctx := by
  have first := raw_I02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I02.frontEndAfter (raw_I02.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_I02.frontEndTicks + 1] (some (raw_I02.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_I02.beforeClear ctx)
  have sameData : raw_I02.frontEndAfter = raw_I02.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_I02_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I02.RunExpected (step caller) regs ctx := by
  have first := raw_I02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I02.frontEndAfter (raw_I02.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_I02.frontEndAfter
    (answerRegisters false (raw_I02.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_I03_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_I03.frontEndTicks (raw_I03.start regs ctx) (raw_I03.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_I03.raw ctx

theorem raw_I03_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I03.IntermediateExpected (step caller) regs ctx := by
  have first := raw_I03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I03.frontEndAfter (raw_I03.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_I03.frontEndTicks + 1] (some (raw_I03.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_I03.beforeClear ctx)
  have sameData : raw_I03.frontEndAfter = raw_I03.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_I03_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I03.RunExpected (step caller) regs ctx := by
  have first := raw_I03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I03.frontEndAfter (raw_I03.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_I03.frontEndAfter
    (answerRegisters false (raw_I03.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_I04_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_I04.frontEndTicks (raw_I04.start regs ctx) (raw_I04.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_I04.raw ctx

theorem raw_I04_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I04.IntermediateExpected (step caller) regs ctx := by
  have first := raw_I04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I04.frontEndAfter (raw_I04.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_I04.frontEndTicks + 1] (some (raw_I04.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_I04.beforeClear ctx)
  have sameData : raw_I04.frontEndAfter = raw_I04.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_I04_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I04.RunExpected (step caller) regs ctx := by
  have first := raw_I04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I04.frontEndAfter (raw_I04.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_I04.frontEndAfter
    (answerRegisters false (raw_I04.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_I05_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_I05.frontEndTicks (raw_I05.start regs ctx) (raw_I05.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_I05.raw ctx

theorem raw_I05_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I05.IntermediateExpected (step caller) regs ctx := by
  have first := raw_I05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I05.frontEndAfter (raw_I05.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_I05.frontEndTicks + 1] (some (raw_I05.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_I05.beforeClear ctx)
  have sameData : raw_I05.frontEndAfter = raw_I05.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_I05_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I05.RunExpected (step caller) regs ctx := by
  have first := raw_I05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I05.frontEndAfter (raw_I05.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_I05.frontEndAfter
    (answerRegisters false (raw_I05.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_I06_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_I06.frontEndTicks (raw_I06.start regs ctx) (raw_I06.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_I06.raw ctx

theorem raw_I06_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I06.IntermediateExpected (step caller) regs ctx := by
  have first := raw_I06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I06.frontEndAfter (raw_I06.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_I06.frontEndTicks + 1] (some (raw_I06.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_I06.beforeClear ctx)
  have sameData : raw_I06.frontEndAfter = raw_I06.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_I06_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I06.RunExpected (step caller) regs ctx := by
  have first := raw_I06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I06.frontEndAfter (raw_I06.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_I06.frontEndAfter
    (answerRegisters false (raw_I06.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_I07_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_I07.frontEndTicks (raw_I07.start regs ctx) (raw_I07.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_I07.raw ctx

theorem raw_I07_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I07.IntermediateExpected (step caller) regs ctx := by
  have first := raw_I07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I07.frontEndAfter (raw_I07.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_I07.frontEndTicks + 1] (some (raw_I07.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_I07.beforeClear ctx)
  have sameData : raw_I07.frontEndAfter = raw_I07.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_I07_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I07.RunExpected (step caller) regs ctx := by
  have first := raw_I07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I07.frontEndAfter (raw_I07.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_I07.frontEndAfter
    (answerRegisters false (raw_I07.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_C01_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_C01.frontEndTicks (raw_C01.start regs ctx) (raw_C01.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_C01.raw ctx

theorem raw_C01_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C01.IntermediateExpected (step caller) regs ctx := by
  have first := raw_C01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_C01.frontEndAfter (raw_C01.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_C01.frontEndTicks + 1] (some (raw_C01.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_C01.beforeClear ctx)
  have sameData : raw_C01.frontEndAfter = raw_C01.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_C01_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C01.RunExpected (step caller) regs ctx := by
  have first := raw_C01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_C01.frontEndAfter (raw_C01.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_C01.frontEndAfter
    (answerRegisters false (raw_C01.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_C02_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_C02.frontEndTicks (raw_C02.start regs ctx) (raw_C02.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_C02.raw ctx

theorem raw_C02_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C02.IntermediateExpected (step caller) regs ctx := by
  have first := raw_C02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_C02.frontEndAfter (raw_C02.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_C02.frontEndTicks + 1] (some (raw_C02.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_C02.beforeClear ctx)
  have sameData : raw_C02.frontEndAfter = raw_C02.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_C02_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C02.RunExpected (step caller) regs ctx := by
  have first := raw_C02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_C02.frontEndAfter (raw_C02.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_C02.frontEndAfter
    (answerRegisters false (raw_C02.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_C03_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_C03.frontEndTicks (raw_C03.start regs ctx) (raw_C03.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_C03.raw ctx

theorem raw_C03_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C03.IntermediateExpected (step caller) regs ctx := by
  have first := raw_C03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_C03.frontEndAfter (raw_C03.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_C03.frontEndTicks + 1] (some (raw_C03.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_C03.beforeClear ctx)
  have sameData : raw_C03.frontEndAfter = raw_C03.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_C03_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C03.RunExpected (step caller) regs ctx := by
  have first := raw_C03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_C03.frontEndAfter (raw_C03.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_C03.frontEndAfter
    (answerRegisters false (raw_C03.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V01_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V01.frontEndTicks (raw_V01.start regs ctx) (raw_V01.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V01.raw ctx

theorem raw_V01_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V01.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V01.frontEndAfter (raw_V01.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V01_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V01.result raw_V01.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V01_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V01.RunExpected (step caller) regs ctx := by
  have first := raw_V01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V01.frontEndAfter (raw_V01.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V01_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V01.result raw_V01.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V01.beforeClear
    (answerRegisters raw_V01.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V02_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V02.frontEndTicks (raw_V02.start regs ctx) (raw_V02.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V02.raw ctx

theorem raw_V02_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V02.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V02.frontEndAfter (raw_V02.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V02_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V02.result raw_V02.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V02_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V02.RunExpected (step caller) regs ctx := by
  have first := raw_V02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V02.frontEndAfter (raw_V02.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V02_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V02.result raw_V02.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V02.beforeClear
    (answerRegisters raw_V02.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V03_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V03.frontEndTicks (raw_V03.start regs ctx) (raw_V03.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V03.raw ctx

theorem raw_V03_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V03.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V03.frontEndAfter (raw_V03.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V03_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V03.result raw_V03.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V03_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V03.RunExpected (step caller) regs ctx := by
  have first := raw_V03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V03.frontEndAfter (raw_V03.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V03_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V03.result raw_V03.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V03.beforeClear
    (answerRegisters raw_V03.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V04_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V04.frontEndTicks (raw_V04.start regs ctx) (raw_V04.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V04.raw ctx

theorem raw_V04_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V04.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V04.frontEndAfter (raw_V04.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V04_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V04.result raw_V04.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V04_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V04.RunExpected (step caller) regs ctx := by
  have first := raw_V04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V04.frontEndAfter (raw_V04.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V04_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V04.result raw_V04.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V04.beforeClear
    (answerRegisters raw_V04.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V05_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V05.frontEndTicks (raw_V05.start regs ctx) (raw_V05.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V05.raw ctx

theorem raw_V05_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V05.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V05.frontEndAfter (raw_V05.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V05_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V05.result raw_V05.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V05_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V05.RunExpected (step caller) regs ctx := by
  have first := raw_V05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V05.frontEndAfter (raw_V05.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V05_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V05.result raw_V05.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V05.beforeClear
    (answerRegisters raw_V05.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V06_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V06.frontEndTicks (raw_V06.start regs ctx) (raw_V06.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V06.raw ctx

theorem raw_V06_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V06.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V06.frontEndAfter (raw_V06.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V06_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V06.result raw_V06.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V06_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V06.RunExpected (step caller) regs ctx := by
  have first := raw_V06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V06.frontEndAfter (raw_V06.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V06_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V06.result raw_V06.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V06.beforeClear
    (answerRegisters raw_V06.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V07_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V07.frontEndTicks (raw_V07.start regs ctx) (raw_V07.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V07.raw ctx

theorem raw_V07_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V07.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V07.frontEndAfter (raw_V07.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V07_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V07.result raw_V07.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V07_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V07.RunExpected (step caller) regs ctx := by
  have first := raw_V07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V07.frontEndAfter (raw_V07.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V07_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V07.result raw_V07.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V07.beforeClear
    (answerRegisters raw_V07.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V08_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V08.frontEndTicks (raw_V08.start regs ctx) (raw_V08.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V08.raw ctx

theorem raw_V08_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V08.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V08_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V08.frontEndAfter (raw_V08.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V08_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V08.result raw_V08.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V08_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V08.RunExpected (step caller) regs ctx := by
  have first := raw_V08_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V08.frontEndAfter (raw_V08.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V08_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V08.result raw_V08.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V08.beforeClear
    (answerRegisters raw_V08.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V09_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V09.frontEndTicks (raw_V09.start regs ctx) (raw_V09.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V09.raw ctx

theorem raw_V09_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V09.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V09_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V09.frontEndAfter (raw_V09.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V09_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V09.result raw_V09.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V09_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V09.RunExpected (step caller) regs ctx := by
  have first := raw_V09_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V09.frontEndAfter (raw_V09.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V09_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V09.result raw_V09.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V09.beforeClear
    (answerRegisters raw_V09.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V10_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V10.frontEndTicks (raw_V10.start regs ctx) (raw_V10.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V10.raw ctx

theorem raw_V10_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V10.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V10_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V10.frontEndAfter (raw_V10.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V10_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V10.result raw_V10.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V10_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V10.RunExpected (step caller) regs ctx := by
  have first := raw_V10_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V10.frontEndAfter (raw_V10.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V10_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V10.result raw_V10.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V10.beforeClear
    (answerRegisters raw_V10.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V11_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V11.frontEndTicks (raw_V11.start regs ctx) (raw_V11.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V11.raw ctx

theorem raw_V11_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V11.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V11_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V11.frontEndAfter (raw_V11.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V11_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V11.result raw_V11.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V11_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V11.RunExpected (step caller) regs ctx := by
  have first := raw_V11_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V11.frontEndAfter (raw_V11.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V11_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V11.result raw_V11.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V11.beforeClear
    (answerRegisters raw_V11.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V12_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V12.frontEndTicks (raw_V12.start regs ctx) (raw_V12.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V12.raw ctx

theorem raw_V12_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V12.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V12_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V12.frontEndAfter (raw_V12.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V12_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V12.result raw_V12.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V12_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V12.RunExpected (step caller) regs ctx := by
  have first := raw_V12_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V12.frontEndAfter (raw_V12.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V12_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V12.result raw_V12.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V12.beforeClear
    (answerRegisters raw_V12.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V13_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V13.frontEndTicks (raw_V13.start regs ctx) (raw_V13.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V13.raw ctx

theorem raw_V13_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V13.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V13_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V13.frontEndAfter (raw_V13.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V13_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V13.result raw_V13.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V13_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V13.RunExpected (step caller) regs ctx := by
  have first := raw_V13_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V13.frontEndAfter (raw_V13.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V13_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V13.result raw_V13.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V13.beforeClear
    (answerRegisters raw_V13.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V14_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V14.frontEndTicks (raw_V14.start regs ctx) (raw_V14.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V14.raw ctx

theorem raw_V14_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V14.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V14_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V14.frontEndAfter (raw_V14.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V14_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V14.result raw_V14.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V14_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V14.RunExpected (step caller) regs ctx := by
  have first := raw_V14_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V14.frontEndAfter (raw_V14.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V14_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V14.result raw_V14.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V14.beforeClear
    (answerRegisters raw_V14.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V15_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V15.frontEndTicks (raw_V15.start regs ctx) (raw_V15.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V15.raw ctx

theorem raw_V15_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V15.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V15_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V15.frontEndAfter (raw_V15.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V15_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V15.result raw_V15.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V15_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V15.RunExpected (step caller) regs ctx := by
  have first := raw_V15_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V15.frontEndAfter (raw_V15.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V15_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V15.result raw_V15.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V15.beforeClear
    (answerRegisters raw_V15.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V16_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V16.frontEndTicks (raw_V16.start regs ctx) (raw_V16.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V16.raw ctx

theorem raw_V16_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V16.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V16_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V16.frontEndAfter (raw_V16.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V16_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V16.result raw_V16.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V16_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V16.RunExpected (step caller) regs ctx := by
  have first := raw_V16_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V16.frontEndAfter (raw_V16.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V16_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V16.result raw_V16.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V16.beforeClear
    (answerRegisters raw_V16.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V17_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V17.frontEndTicks (raw_V17.start regs ctx) (raw_V17.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V17.raw ctx

theorem raw_V17_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V17.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V17_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V17.frontEndAfter (raw_V17.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V17_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V17.result raw_V17.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V17_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V17.RunExpected (step caller) regs ctx := by
  have first := raw_V17_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V17.frontEndAfter (raw_V17.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V17_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V17.result raw_V17.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V17.beforeClear
    (answerRegisters raw_V17.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V18_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V18.frontEndTicks (raw_V18.start regs ctx) (raw_V18.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V18.raw ctx

theorem raw_V18_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V18.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V18_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V18.frontEndAfter (raw_V18.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V18_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V18.result raw_V18.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V18_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V18.RunExpected (step caller) regs ctx := by
  have first := raw_V18_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V18.frontEndAfter (raw_V18.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V18_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V18.result raw_V18.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V18.beforeClear
    (answerRegisters raw_V18.result (fullReset regs)) ctx
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

theorem raw_F01_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_F01.start regs ctx) raw_F01.ticks (raw_F01.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_F01 regs ctx
    (raw_F01_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_F01.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_F01_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F01.Expected (step caller) regs ctx :=
  ⟨raw_F01_actual_first_halt caller regs ctx, raw_F01_actual_intermediates caller regs ctx,
    by trivial, raw_F01_actual_exact_peak caller regs ctx⟩

theorem raw_F02_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_F02.start regs ctx) raw_F02.ticks (raw_F02.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_F02 regs ctx
    (raw_F02_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_F02.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_F02_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F02.Expected (step caller) regs ctx :=
  ⟨raw_F02_actual_first_halt caller regs ctx, raw_F02_actual_intermediates caller regs ctx,
    by trivial, raw_F02_actual_exact_peak caller regs ctx⟩

theorem raw_F03_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_F03.start regs ctx) raw_F03.ticks (raw_F03.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_F03 regs ctx
    (raw_F03_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_F03.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_F03_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F03.Expected (step caller) regs ctx :=
  ⟨raw_F03_actual_first_halt caller regs ctx, raw_F03_actual_intermediates caller regs ctx,
    by trivial, raw_F03_actual_exact_peak caller regs ctx⟩

theorem raw_F04_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_F04.start regs ctx) raw_F04.ticks (raw_F04.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_F04 regs ctx
    (raw_F04_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_F04.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_F04_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F04.Expected (step caller) regs ctx :=
  ⟨raw_F04_actual_first_halt caller regs ctx, raw_F04_actual_intermediates caller regs ctx,
    by trivial, raw_F04_actual_exact_peak caller regs ctx⟩

theorem raw_F05_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_F05.start regs ctx) raw_F05.ticks (raw_F05.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_F05 regs ctx
    (raw_F05_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_F05.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_F05_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F05.Expected (step caller) regs ctx :=
  ⟨raw_F05_actual_first_halt caller regs ctx, raw_F05_actual_intermediates caller regs ctx,
    by trivial, raw_F05_actual_exact_peak caller regs ctx⟩

theorem raw_F06_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_F06.start regs ctx) raw_F06.ticks (raw_F06.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_F06 regs ctx
    (raw_F06_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_F06.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_F06_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F06.Expected (step caller) regs ctx :=
  ⟨raw_F06_actual_first_halt caller regs ctx, raw_F06_actual_intermediates caller regs ctx,
    by trivial, raw_F06_actual_exact_peak caller regs ctx⟩

theorem raw_F07_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_F07.start regs ctx) raw_F07.ticks (raw_F07.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_F07 regs ctx
    (raw_F07_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_F07.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_F07_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F07.Expected (step caller) regs ctx :=
  ⟨raw_F07_actual_first_halt caller regs ctx, raw_F07_actual_intermediates caller regs ctx,
    by trivial, raw_F07_actual_exact_peak caller regs ctx⟩

theorem raw_F08_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_F08.start regs ctx) raw_F08.ticks (raw_F08.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_F08 regs ctx
    (raw_F08_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_F08.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_F08_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F08.Expected (step caller) regs ctx :=
  ⟨raw_F08_actual_first_halt caller regs ctx, raw_F08_actual_intermediates caller regs ctx,
    by trivial, raw_F08_actual_exact_peak caller regs ctx⟩

theorem raw_I01_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_I01.start regs ctx) raw_I01.ticks (raw_I01.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_I01 regs ctx
    (raw_I01_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_I01.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_I01_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I01.Expected (step caller) regs ctx :=
  ⟨raw_I01_actual_first_halt caller regs ctx, raw_I01_actual_intermediates caller regs ctx,
    by trivial, raw_I01_actual_exact_peak caller regs ctx⟩

theorem raw_I02_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_I02.start regs ctx) raw_I02.ticks (raw_I02.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_I02 regs ctx
    (raw_I02_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_I02.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_I02_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I02.Expected (step caller) regs ctx :=
  ⟨raw_I02_actual_first_halt caller regs ctx, raw_I02_actual_intermediates caller regs ctx,
    by trivial, raw_I02_actual_exact_peak caller regs ctx⟩

theorem raw_I03_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_I03.start regs ctx) raw_I03.ticks (raw_I03.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_I03 regs ctx
    (raw_I03_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_I03.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_I03_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I03.Expected (step caller) regs ctx :=
  ⟨raw_I03_actual_first_halt caller regs ctx, raw_I03_actual_intermediates caller regs ctx,
    by trivial, raw_I03_actual_exact_peak caller regs ctx⟩

theorem raw_I04_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_I04.start regs ctx) raw_I04.ticks (raw_I04.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_I04 regs ctx
    (raw_I04_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_I04.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_I04_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I04.Expected (step caller) regs ctx :=
  ⟨raw_I04_actual_first_halt caller regs ctx, raw_I04_actual_intermediates caller regs ctx,
    by trivial, raw_I04_actual_exact_peak caller regs ctx⟩

theorem raw_I05_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_I05.start regs ctx) raw_I05.ticks (raw_I05.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_I05 regs ctx
    (raw_I05_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_I05.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_I05_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I05.Expected (step caller) regs ctx :=
  ⟨raw_I05_actual_first_halt caller regs ctx, raw_I05_actual_intermediates caller regs ctx,
    by trivial, raw_I05_actual_exact_peak caller regs ctx⟩

theorem raw_I06_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_I06.start regs ctx) raw_I06.ticks (raw_I06.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_I06 regs ctx
    (raw_I06_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_I06.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_I06_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I06.Expected (step caller) regs ctx :=
  ⟨raw_I06_actual_first_halt caller regs ctx, raw_I06_actual_intermediates caller regs ctx,
    by trivial, raw_I06_actual_exact_peak caller regs ctx⟩

theorem raw_I07_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_I07.start regs ctx) raw_I07.ticks (raw_I07.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_I07 regs ctx
    (raw_I07_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_I07.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_I07_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I07.Expected (step caller) regs ctx :=
  ⟨raw_I07_actual_first_halt caller regs ctx, raw_I07_actual_intermediates caller regs ctx,
    by trivial, raw_I07_actual_exact_peak caller regs ctx⟩

theorem raw_C01_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_C01.start regs ctx) raw_C01.ticks (raw_C01.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_C01 regs ctx
    (raw_C01_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_C01.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_C01_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C01.Expected (step caller) regs ctx :=
  ⟨raw_C01_actual_first_halt caller regs ctx, raw_C01_actual_intermediates caller regs ctx,
    by trivial, raw_C01_actual_exact_peak caller regs ctx⟩

theorem raw_C02_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_C02.start regs ctx) raw_C02.ticks (raw_C02.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_C02 regs ctx
    (raw_C02_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_C02.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_C02_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C02.Expected (step caller) regs ctx :=
  ⟨raw_C02_actual_first_halt caller regs ctx, raw_C02_actual_intermediates caller regs ctx,
    by trivial, raw_C02_actual_exact_peak caller regs ctx⟩

theorem raw_C03_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_C03.start regs ctx) raw_C03.ticks (raw_C03.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_C03 regs ctx
    (raw_C03_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_C03.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_C03.raw.length 1 = raw_C03.peak := by
    norm_num [raw_C03]
  rw [literalPeak] at peak
  exact peak

theorem raw_C03_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C03.Expected (step caller) regs ctx :=
  ⟨raw_C03_actual_first_halt caller regs ctx, raw_C03_actual_intermediates caller regs ctx,
    by trivial, raw_C03_actual_exact_peak caller regs ctx⟩

theorem raw_V01_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V01.start regs ctx) raw_V01.ticks (raw_V01.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V01 regs ctx
    (raw_V01_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V01.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_V01_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V01.Expected (step caller) regs ctx :=
  ⟨raw_V01_actual_first_halt caller regs ctx, raw_V01_actual_intermediates caller regs ctx,
    raw_V01_stream_actual_exact_peak caller regs ctx, raw_V01_actual_exact_peak caller regs ctx⟩

theorem raw_V02_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V02.start regs ctx) raw_V02.ticks (raw_V02.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V02 regs ctx
    (raw_V02_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V02.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_V02_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V02.Expected (step caller) regs ctx :=
  ⟨raw_V02_actual_first_halt caller regs ctx, raw_V02_actual_intermediates caller regs ctx,
    raw_V02_stream_actual_exact_peak caller regs ctx, raw_V02_actual_exact_peak caller regs ctx⟩

theorem raw_V03_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V03.start regs ctx) raw_V03.ticks (raw_V03.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V03 regs ctx
    (raw_V03_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V03.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V03.raw.length 1 = raw_V03.peak := by
    norm_num [raw_V03]
  rw [literalPeak] at peak
  exact peak

theorem raw_V03_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V03.Expected (step caller) regs ctx :=
  ⟨raw_V03_actual_first_halt caller regs ctx, raw_V03_actual_intermediates caller regs ctx,
    raw_V03_stream_actual_exact_peak caller regs ctx, raw_V03_actual_exact_peak caller regs ctx⟩

theorem raw_V04_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V04.start regs ctx) raw_V04.ticks (raw_V04.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V04 regs ctx
    (raw_V04_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V04.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V04.raw.length 1 = raw_V04.peak := by
    norm_num [raw_V04]
  rw [literalPeak] at peak
  exact peak

theorem raw_V04_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V04.Expected (step caller) regs ctx :=
  ⟨raw_V04_actual_first_halt caller regs ctx, raw_V04_actual_intermediates caller regs ctx,
    raw_V04_stream_actual_exact_peak caller regs ctx, raw_V04_actual_exact_peak caller regs ctx⟩

theorem raw_V05_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V05.start regs ctx) raw_V05.ticks (raw_V05.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V05 regs ctx
    (raw_V05_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V05.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V05.raw.length 1 = raw_V05.peak := by
    norm_num [raw_V05]
  rw [literalPeak] at peak
  exact peak

theorem raw_V05_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V05.Expected (step caller) regs ctx :=
  ⟨raw_V05_actual_first_halt caller regs ctx, raw_V05_actual_intermediates caller regs ctx,
    raw_V05_stream_actual_exact_peak caller regs ctx, raw_V05_actual_exact_peak caller regs ctx⟩

theorem raw_V06_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V06.start regs ctx) raw_V06.ticks (raw_V06.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V06 regs ctx
    (raw_V06_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V06.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V06.raw.length 1 = raw_V06.peak := by
    norm_num [raw_V06]
  rw [literalPeak] at peak
  exact peak

theorem raw_V06_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V06.Expected (step caller) regs ctx :=
  ⟨raw_V06_actual_first_halt caller regs ctx, raw_V06_actual_intermediates caller regs ctx,
    raw_V06_stream_actual_exact_peak caller regs ctx, raw_V06_actual_exact_peak caller regs ctx⟩

theorem raw_V07_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V07.start regs ctx) raw_V07.ticks (raw_V07.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V07 regs ctx
    (raw_V07_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V07.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V07.raw.length 1 = raw_V07.peak := by
    norm_num [raw_V07]
  rw [literalPeak] at peak
  exact peak

theorem raw_V07_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V07.Expected (step caller) regs ctx :=
  ⟨raw_V07_actual_first_halt caller regs ctx, raw_V07_actual_intermediates caller regs ctx,
    raw_V07_stream_actual_exact_peak caller regs ctx, raw_V07_actual_exact_peak caller regs ctx⟩

theorem raw_V08_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V08.start regs ctx) raw_V08.ticks (raw_V08.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V08 regs ctx
    (raw_V08_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V08.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V08.raw.length 1 = raw_V08.peak := by
    norm_num [raw_V08]
  rw [literalPeak] at peak
  exact peak

theorem raw_V08_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V08.Expected (step caller) regs ctx :=
  ⟨raw_V08_actual_first_halt caller regs ctx, raw_V08_actual_intermediates caller regs ctx,
    raw_V08_stream_actual_exact_peak caller regs ctx, raw_V08_actual_exact_peak caller regs ctx⟩

theorem raw_V09_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V09.start regs ctx) raw_V09.ticks (raw_V09.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V09 regs ctx
    (raw_V09_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V09.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_V09_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V09.Expected (step caller) regs ctx :=
  ⟨raw_V09_actual_first_halt caller regs ctx, raw_V09_actual_intermediates caller regs ctx,
    raw_V09_stream_actual_exact_peak caller regs ctx, raw_V09_actual_exact_peak caller regs ctx⟩

theorem raw_V10_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V10.start regs ctx) raw_V10.ticks (raw_V10.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V10 regs ctx
    (raw_V10_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V10.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V10.raw.length 1 = raw_V10.peak := by
    norm_num [raw_V10]
  rw [literalPeak] at peak
  exact peak

theorem raw_V10_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V10.Expected (step caller) regs ctx :=
  ⟨raw_V10_actual_first_halt caller regs ctx, raw_V10_actual_intermediates caller regs ctx,
    raw_V10_stream_actual_exact_peak caller regs ctx, raw_V10_actual_exact_peak caller regs ctx⟩

theorem raw_V11_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V11.start regs ctx) raw_V11.ticks (raw_V11.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V11 regs ctx
    (raw_V11_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V11.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V11.raw.length 1 = raw_V11.peak := by
    norm_num [raw_V11]
  rw [literalPeak] at peak
  exact peak

theorem raw_V11_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V11.Expected (step caller) regs ctx :=
  ⟨raw_V11_actual_first_halt caller regs ctx, raw_V11_actual_intermediates caller regs ctx,
    raw_V11_stream_actual_exact_peak caller regs ctx, raw_V11_actual_exact_peak caller regs ctx⟩

theorem raw_V12_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V12.start regs ctx) raw_V12.ticks (raw_V12.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V12 regs ctx
    (raw_V12_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V12.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V12.raw.length 1 = raw_V12.peak := by
    norm_num [raw_V12]
  rw [literalPeak] at peak
  exact peak

theorem raw_V12_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V12.Expected (step caller) regs ctx :=
  ⟨raw_V12_actual_first_halt caller regs ctx, raw_V12_actual_intermediates caller regs ctx,
    raw_V12_stream_actual_exact_peak caller regs ctx, raw_V12_actual_exact_peak caller regs ctx⟩

theorem raw_V13_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V13.start regs ctx) raw_V13.ticks (raw_V13.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V13 regs ctx
    (raw_V13_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V13.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V13.raw.length 1 = raw_V13.peak := by
    norm_num [raw_V13]
  rw [literalPeak] at peak
  exact peak

theorem raw_V13_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V13.Expected (step caller) regs ctx :=
  ⟨raw_V13_actual_first_halt caller regs ctx, raw_V13_actual_intermediates caller regs ctx,
    raw_V13_stream_actual_exact_peak caller regs ctx, raw_V13_actual_exact_peak caller regs ctx⟩

theorem raw_V14_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V14.start regs ctx) raw_V14.ticks (raw_V14.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V14 regs ctx
    (raw_V14_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V14.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V14.raw.length 1 = raw_V14.peak := by
    norm_num [raw_V14]
  rw [literalPeak] at peak
  exact peak

theorem raw_V14_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V14.Expected (step caller) regs ctx :=
  ⟨raw_V14_actual_first_halt caller regs ctx, raw_V14_actual_intermediates caller regs ctx,
    raw_V14_stream_actual_exact_peak caller regs ctx, raw_V14_actual_exact_peak caller regs ctx⟩

theorem raw_V15_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V15.start regs ctx) raw_V15.ticks (raw_V15.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V15 regs ctx
    (raw_V15_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V15.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_V15_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V15.Expected (step caller) regs ctx :=
  ⟨raw_V15_actual_first_halt caller regs ctx, raw_V15_actual_intermediates caller regs ctx,
    raw_V15_stream_actual_exact_peak caller regs ctx, raw_V15_actual_exact_peak caller regs ctx⟩

theorem raw_V16_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V16.start regs ctx) raw_V16.ticks (raw_V16.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V16 regs ctx
    (raw_V16_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V16.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_V16_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V16.Expected (step caller) regs ctx :=
  ⟨raw_V16_actual_first_halt caller regs ctx, raw_V16_actual_intermediates caller regs ctx,
    raw_V16_stream_actual_exact_peak caller regs ctx, raw_V16_actual_exact_peak caller regs ctx⟩

theorem raw_V17_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V17.start regs ctx) raw_V17.ticks (raw_V17.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V17 regs ctx
    (raw_V17_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V17.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_V17_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V17.Expected (step caller) regs ctx :=
  ⟨raw_V17_actual_first_halt caller regs ctx, raw_V17_actual_intermediates caller regs ctx,
    raw_V17_stream_actual_exact_peak caller regs ctx, raw_V17_actual_exact_peak caller regs ctx⟩

theorem raw_V18_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V18.start regs ctx) raw_V18.ticks (raw_V18.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V18 regs ctx
    (raw_V18_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V18.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_V18_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V18.Expected (step caller) regs ctx :=
  ⟨raw_V18_actual_first_halt caller regs ctx, raw_V18_actual_intermediates caller regs ctx,
    raw_V18_stream_actual_exact_peak caller regs ctx, raw_V18_actual_exact_peak caller regs ctx⟩

theorem all_original_raw_rows_execute_with_their_complete_endpoints_and_peaks
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∀ fixture ∈ rawCases, fixture.Expected (step caller) regs ctx := by
  intro fixture member
  simp only [rawCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact raw_F01_expected caller regs ctx
  · exact raw_F02_expected caller regs ctx
  · exact raw_F03_expected caller regs ctx
  · exact raw_F04_expected caller regs ctx
  · exact raw_F05_expected caller regs ctx
  · exact raw_F06_expected caller regs ctx
  · exact raw_F07_expected caller regs ctx
  · exact raw_F08_expected caller regs ctx
  · exact raw_I01_expected caller regs ctx
  · exact raw_I02_expected caller regs ctx
  · exact raw_I03_expected caller regs ctx
  · exact raw_I04_expected caller regs ctx
  · exact raw_I05_expected caller regs ctx
  · exact raw_I06_expected caller regs ctx
  · exact raw_I07_expected caller regs ctx
  · exact raw_C01_expected caller regs ctx
  · exact raw_C02_expected caller regs ctx
  · exact raw_C03_expected caller regs ctx
  · exact raw_V01_expected caller regs ctx
  · exact raw_V02_expected caller regs ctx
  · exact raw_V03_expected caller regs ctx
  · exact raw_V04_expected caller regs ctx
  · exact raw_V05_expected caller regs ctx
  · exact raw_V06_expected caller regs ctx
  · exact raw_V07_expected caller regs ctx
  · exact raw_V08_expected caller regs ctx
  · exact raw_V09_expected caller regs ctx
  · exact raw_V10_expected caller regs ctx
  · exact raw_V11_expected caller regs ctx
  · exact raw_V12_expected caller regs ctx
  · exact raw_V13_expected caller regs ctx
  · exact raw_V14_expected caller regs ctx
  · exact raw_V15_expected caller regs ctx
  · exact raw_V16_expected caller regs ctx
  · exact raw_V17_expected caller regs ctx
  · exact raw_V18_expected caller regs ctx

end LiteralRawRuns

/-! The operational raw-case aggregate has no finite-context hypothesis. -/

theorem all_original_raw_rows_have_their_actual_first_halt
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (fixture : RawFixture) (member : fixture ∈ rawCases) :
    fixture.RunExpected (step caller) regs ctx := by
  simp only [rawCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact raw_F01_actual_first_halt caller regs ctx
  · exact raw_F02_actual_first_halt caller regs ctx
  · exact raw_F03_actual_first_halt caller regs ctx
  · exact raw_F04_actual_first_halt caller regs ctx
  · exact raw_F05_actual_first_halt caller regs ctx
  · exact raw_F06_actual_first_halt caller regs ctx
  · exact raw_F07_actual_first_halt caller regs ctx
  · exact raw_F08_actual_first_halt caller regs ctx
  · exact raw_I01_actual_first_halt caller regs ctx
  · exact raw_I02_actual_first_halt caller regs ctx
  · exact raw_I03_actual_first_halt caller regs ctx
  · exact raw_I04_actual_first_halt caller regs ctx
  · exact raw_I05_actual_first_halt caller regs ctx
  · exact raw_I06_actual_first_halt caller regs ctx
  · exact raw_I07_actual_first_halt caller regs ctx
  · exact raw_C01_actual_first_halt caller regs ctx
  · exact raw_C02_actual_first_halt caller regs ctx
  · exact raw_C03_actual_first_halt caller regs ctx
  · exact raw_V01_actual_first_halt caller regs ctx
  · exact raw_V02_actual_first_halt caller regs ctx
  · exact raw_V03_actual_first_halt caller regs ctx
  · exact raw_V04_actual_first_halt caller regs ctx
  · exact raw_V05_actual_first_halt caller regs ctx
  · exact raw_V06_actual_first_halt caller regs ctx
  · exact raw_V07_actual_first_halt caller regs ctx
  · exact raw_V08_actual_first_halt caller regs ctx
  · exact raw_V09_actual_first_halt caller regs ctx
  · exact raw_V10_actual_first_halt caller regs ctx
  · exact raw_V11_actual_first_halt caller regs ctx
  · exact raw_V12_actual_first_halt caller regs ctx
  · exact raw_V13_actual_first_halt caller regs ctx
  · exact raw_V14_actual_first_halt caller regs ctx
  · exact raw_V15_actual_first_halt caller regs ctx
  · exact raw_V16_actual_first_halt caller regs ctx
  · exact raw_V17_actual_first_halt caller regs ctx
  · exact raw_V18_actual_first_halt caller regs ctx


end Examples.RotationCertificateFrontEndStreamMachine
