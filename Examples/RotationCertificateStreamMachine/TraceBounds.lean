import Examples.RotationCertificateStreamMachine.TraceSteps

/-!
# RotationCertificateStreamMachine: TraceBounds
-/

namespace Examples.RotationCertificateStreamMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.StreamMachine

theorem traceA01_owned (n : Nat) (bound : n < 4) :
    (traceA01 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA01_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (traceA01 n).stores ≤ 0 := by
  interval_cases n <;> decide

theorem traceA02_owned (n : Nat) (bound : n < 4) :
    (traceA02 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA02_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (traceA02 n).stores ≤ 1 := by
  interval_cases n <;> decide

theorem traceA03_owned (n : Nat) (bound : n < 5) :
    (traceA03 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA03_cells (n : Nat) (bound : n ≤ 5) :
    fixtureCells (traceA03 n).stores ≤ 2 := by
  interval_cases n <;> decide

theorem traceA04_owned (n : Nat) (bound : n < 7) :
    (traceA04 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA04_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (traceA04 n).stores ≤ 7 := by
  interval_cases n <;> decide

theorem traceA05_owned (n : Nat) (bound : n < 9) :
    (traceA05 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA05_cells (n : Nat) (bound : n ≤ 9) :
    fixtureCells (traceA05 n).stores ≤ 12 := by
  interval_cases n <;> decide

theorem traceA06_owned (n : Nat) (bound : n < 4) :
    (traceA06 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA06_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (traceA06 n).stores ≤ 4 := by
  interval_cases n <;> decide

theorem traceA07_owned (n : Nat) (bound : n < 5) :
    (traceA07 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA07_cells (n : Nat) (bound : n ≤ 5) :
    fixtureCells (traceA07 n).stores ≤ 3 := by
  interval_cases n <;> decide

theorem traceA08_owned (n : Nat) (bound : n < 6) :
    (traceA08 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA08_cells (n : Nat) (bound : n ≤ 6) :
    fixtureCells (traceA08 n).stores ≤ 8 := by
  interval_cases n <;> decide

theorem traceA09_owned (n : Nat) (bound : n < 8) :
    (traceA09 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA09_cells (n : Nat) (bound : n ≤ 8) :
    fixtureCells (traceA09 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem traceA10_owned (n : Nat) (bound : n < 7) :
    (traceA10 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA10_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (traceA10 n).stores ≤ 12 := by
  interval_cases n <;> decide

theorem traceA11_owned (n : Nat) (bound : n < 11) :
    (traceA11 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA11_cells (n : Nat) (bound : n ≤ 11) :
    fixtureCells (traceA11 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem traceA12_owned (n : Nat) (bound : n < 25) :
    (traceA12 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA12_cells (n : Nat) (bound : n ≤ 25) :
    fixtureCells (traceA12 n).stores ≤ 13 := by
  interval_cases n <;> decide

theorem traceA13_owned (n : Nat) (bound : n < 24) :
    (traceA13 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA13_cells (n : Nat) (bound : n ≤ 24) :
    fixtureCells (traceA13 n).stores ≤ 13 := by
  interval_cases n <;> decide

theorem traceA14_owned (n : Nat) (bound : n < 13) :
    (traceA14 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA14_cells (n : Nat) (bound : n ≤ 13) :
    fixtureCells (traceA14 n).stores ≤ 5 := by
  interval_cases n <;> decide

theorem traceA15_owned (n : Nat) (bound : n < 16) :
    (traceA15 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA15_cells (n : Nat) (bound : n ≤ 16) :
    fixtureCells (traceA15 n).stores ≤ 7 := by
  interval_cases n <;> decide

theorem traceA16_owned (n : Nat) (bound : n < 31) :
    (traceA16 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA16_cells (n : Nat) (bound : n ≤ 31) :
    fixtureCells (traceA16 n).stores ≤ 18 := by
  interval_cases n <;> decide

theorem traceA17_owned (n : Nat) (bound : n < 33) :
    (traceA17 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA17_cells (n : Nat) (bound : n ≤ 33) :
    fixtureCells (traceA17 n).stores ≤ 18 := by
  interval_cases n <;> decide

theorem traceA18_owned (n : Nat) (bound : n < 42) :
    (traceA18 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA18_cells (n : Nat) (bound : n ≤ 42) :
    fixtureCells (traceA18 n).stores ≤ 16 := by
  interval_cases n <;> decide

theorem traceA19_owned (n : Nat) (bound : n < 22) :
    (traceA19 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA19_cells (n : Nat) (bound : n ≤ 22) :
    fixtureCells (traceA19 n).stores ≤ 15 := by
  interval_cases n <;> decide

theorem traceA20_owned (n : Nat) (bound : n < 25) :
    (traceA20 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA20_cells (n : Nat) (bound : n ≤ 25) :
    fixtureCells (traceA20 n).stores ≤ 15 := by
  interval_cases n <;> decide

theorem traceA21_owned (n : Nat) (bound : n < 24) :
    (traceA21 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceA21_cells (n : Nat) (bound : n ≤ 24) :
    fixtureCells (traceA21 n).stores ≤ 11 := by
  interval_cases n <;> decide

theorem traceD01_owned (n : Nat) (bound : n < 4) :
    (traceD01 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceD01_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (traceD01 n).stores ≤ 8 := by
  interval_cases n <;> decide

theorem traceD02_owned (n : Nat) (bound : n < 9) :
    (traceD02 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceD02_cells (n : Nat) (bound : n ≤ 9) :
    fixtureCells (traceD02 n).stores ≤ 11 := by
  interval_cases n <;> decide

theorem traceD03_owned (n : Nat) (bound : n < 6) :
    (traceD03 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceD03_cells (n : Nat) (bound : n ≤ 6) :
    fixtureCells (traceD03 n).stores ≤ 3 := by
  interval_cases n <;> decide

theorem traceD04_owned (n : Nat) (bound : n < 7) :
    (traceD04 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceD04_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (traceD04 n).stores ≤ 9 := by
  interval_cases n <;> decide

theorem traceD05_owned (n : Nat) (bound : n < 13) :
    (traceD05 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceD05_cells (n : Nat) (bound : n ≤ 13) :
    fixtureCells (traceD05 n).stores ≤ 11 := by
  interval_cases n <;> decide

theorem traceD06_owned (n : Nat) (bound : n < 30) :
    (traceD06 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceD06_cells (n : Nat) (bound : n ≤ 30) :
    fixtureCells (traceD06 n).stores ≤ 18 := by
  interval_cases n <;> decide

theorem traceD07_owned (n : Nat) (bound : n < 29) :
    (traceD07 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceD07_cells (n : Nat) (bound : n ≤ 29) :
    fixtureCells (traceD07 n).stores ≤ 18 := by
  interval_cases n <;> decide

theorem traceD08_owned (n : Nat) (bound : n < 7) :
    (traceD08 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceD08_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (traceD08 n).stores ≤ 6 := by
  interval_cases n <;> decide

theorem traceD09_owned (n : Nat) (bound : n < 5) :
    (traceD09 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceD09_cells (n : Nat) (bound : n ≤ 5) :
    fixtureCells (traceD09 n).stores ≤ 0 := by
  interval_cases n <;> decide

theorem traceD10_owned (n : Nat) (bound : n < 4) :
    (traceD10 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceD10_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (traceD10 n).stores ≤ 0 := by
  interval_cases n <;> decide

theorem traceD11_owned (n : Nat) (bound : n < 3) :
    (traceD11 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceD11_cells (n : Nat) (bound : n ≤ 3) :
    fixtureCells (traceD11 n).stores ≤ 1 := by
  interval_cases n <;> decide

theorem traceD12_owned (n : Nat) (bound : n < 2) :
    (traceD12 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceD12_cells (n : Nat) (bound : n ≤ 2) :
    fixtureCells (traceD12 n).stores ≤ 1 := by
  interval_cases n <;> decide

theorem traceD13_owned (n : Nat) (bound : n < 1) :
    (traceD13 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceD13_cells (n : Nat) (bound : n ≤ 1) :
    fixtureCells (traceD13 n).stores ≤ 3 := by
  interval_cases n <;> decide

theorem traceR01_owned (n : Nat) (bound : n < 7) :
    (traceR01 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceR01_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (traceR01 n).stores ≤ 13 := by
  interval_cases n <;> decide

theorem traceR02_owned (n : Nat) (bound : n < 4) :
    (traceR02 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceR02_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (traceR02 n).stores ≤ 15 := by
  interval_cases n <;> decide

theorem traceR03_owned (n : Nat) (bound : n < 17) :
    (traceR03 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceR03_cells (n : Nat) (bound : n ≤ 17) :
    fixtureCells (traceR03 n).stores ≤ 16 := by
  interval_cases n <;> decide

theorem traceR04_owned (n : Nat) (bound : n < 27) :
    (traceR04 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceR04_cells (n : Nat) (bound : n ≤ 27) :
    fixtureCells (traceR04 n).stores ≤ 15 := by
  interval_cases n <;> decide

theorem traceR05_owned (n : Nat) (bound : n < 6) :
    (traceR05 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceR05_cells (n : Nat) (bound : n ≤ 6) :
    fixtureCells (traceR05 n).stores ≤ 7 := by
  interval_cases n <;> decide

theorem traceR06_owned (n : Nat) (bound : n < 6) :
    (traceR06 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceR06_cells (n : Nat) (bound : n ≤ 6) :
    fixtureCells (traceR06 n).stores ≤ 7 := by
  interval_cases n <;> decide

theorem traceR07_owned (n : Nat) (bound : n < 22) :
    (traceR07 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceR07_cells (n : Nat) (bound : n ≤ 22) :
    fixtureCells (traceR07 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem traceR08_owned (n : Nat) (bound : n < 41) :
    (traceR08 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceR08_cells (n : Nat) (bound : n ≤ 41) :
    fixtureCells (traceR08 n).stores ≤ 17 := by
  interval_cases n <;> decide

theorem traceR09_owned (n : Nat) (bound : n < 40) :
    (traceR09 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceR09_cells (n : Nat) (bound : n ≤ 40) :
    fixtureCells (traceR09 n).stores ≤ 17 := by
  interval_cases n <;> decide

theorem traceR10_owned (n : Nat) (bound : n < 20) :
    (traceR10 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem traceR10_cells (n : Nat) (bound : n ≤ 20) :
    fixtureCells (traceR10 n).stores ≤ 15 := by
  interval_cases n <;> decide


theorem trace_point_with_phase_control_is_owned
    {K Λ R : Type} {Γ : K → Type} (p : TracePoint)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (phase : p.control.isLeft = true) : Owned (p.reached (Λ := Λ) regs ctx).l := by
  change Owned (some (boundaryLabel p.control))
  cases label : p.control with
  | inl q => exact owned_phase q
  | inr b => simp only [label, Sum.isLeft, Bool.false_eq_true] at phase

section TraceFirstConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem literal_trace_is_an_actual_first_run (c : RunFixture) (points : Nat → TracePoint)
    (first : (points 0).reached (Λ := Λ) regs ctx = c.start regs ctx)
    (last : (points c.ticks).reached (Λ := Λ) regs ctx = c.finish regs ctx)
    (adjacent : ∀ n, n < c.ticks →
      step caller ((points n).reached regs ctx) = some ((points (n + 1)).reached regs ctx))
    (owned : ∀ n, n < c.ticks → (points n).control.isLeft = true) :
    c.RunExpected (step caller) regs ctx := by
  refine ⟨?_, not_owned_result c.result, ?_⟩
  · simpa only [first, last] using
      finite_trace_actual_prefix caller regs ctx points c.ticks adjacent c.ticks (Nat.le_refl _)
  · intro n strict
    refine ⟨(points n).reached regs ctx, ?_, trace_point_with_phase_control_is_owned
      (points n) regs ctx (owned n strict)⟩
    simpa only [first] using
      finite_trace_actual_prefix caller regs ctx points c.ticks adjacent n (Nat.le_of_lt strict)

theorem literal_evaluation_follows_from_its_actual_first_run (c : RunFixture)
    (first : c.RunExpected (step caller) regs ctx) :
    evaluate c.phase c.before = ⟨c.result, c.after, c.ticks⟩ := by
  obtain ⟨clock, endpoint⟩ := first_return_unique caller c.phase c.before regs ctx
    c.ticks (c.finish regs ctx) first.1 first.2.1 first.2.2
  rcases actual : evaluate c.phase c.before with ⟨b, D, n⟩
  have exactClock : c.ticks = n := by simpa only [phaseSteps, actual] using clock
  have exactEndpoint : c.finish (Λ := Λ) regs ctx =
      cfg (some (resultLabel b)) (resetAll regs) D ctx := by
    simpa only [phaseResult, evaluationCfg, actual] using endpoint
  have exactWords : c.after = D := by
    simpa only [RunFixture.finish, dataOfCfg_cfg] using congrArg dataOfCfg exactEndpoint
  have exactResult : c.result = b := by
    have labels := congrArg Turing.TM2.Cfg.l exactEndpoint
    change some (resultLabel (Λ := Λ) c.result) = some (resultLabel b) at labels
    simpa only [resultLabel, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] using labels
  rw [← exactClock, ← exactWords, ← exactResult]

end TraceFirstConnections


end Examples.RotationCertificateStreamMachine
