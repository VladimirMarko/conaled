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

theorem trace_a01_owned (n : Nat) (bound : n < 4) :
    (trace_a01 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a01_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_a01 n).stores ≤ 0 := by
  interval_cases n <;> decide

theorem trace_a02_owned (n : Nat) (bound : n < 4) :
    (trace_a02 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a02_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_a02 n).stores ≤ 1 := by
  interval_cases n <;> decide

theorem trace_a03_owned (n : Nat) (bound : n < 5) :
    (trace_a03 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a03_cells (n : Nat) (bound : n ≤ 5) :
    fixtureCells (trace_a03 n).stores ≤ 2 := by
  interval_cases n <;> decide

theorem trace_a04_owned (n : Nat) (bound : n < 7) :
    (trace_a04 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a04_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (trace_a04 n).stores ≤ 7 := by
  interval_cases n <;> decide

theorem trace_a05_owned (n : Nat) (bound : n < 9) :
    (trace_a05 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a05_cells (n : Nat) (bound : n ≤ 9) :
    fixtureCells (trace_a05 n).stores ≤ 12 := by
  interval_cases n <;> decide

theorem trace_a06_owned (n : Nat) (bound : n < 4) :
    (trace_a06 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a06_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_a06 n).stores ≤ 4 := by
  interval_cases n <;> decide

theorem trace_a07_owned (n : Nat) (bound : n < 5) :
    (trace_a07 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a07_cells (n : Nat) (bound : n ≤ 5) :
    fixtureCells (trace_a07 n).stores ≤ 3 := by
  interval_cases n <;> decide

theorem trace_a08_owned (n : Nat) (bound : n < 6) :
    (trace_a08 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a08_cells (n : Nat) (bound : n ≤ 6) :
    fixtureCells (trace_a08 n).stores ≤ 8 := by
  interval_cases n <;> decide

theorem trace_a09_owned (n : Nat) (bound : n < 8) :
    (trace_a09 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a09_cells (n : Nat) (bound : n ≤ 8) :
    fixtureCells (trace_a09 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem trace_a10_owned (n : Nat) (bound : n < 7) :
    (trace_a10 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a10_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (trace_a10 n).stores ≤ 12 := by
  interval_cases n <;> decide

theorem trace_a11_owned (n : Nat) (bound : n < 11) :
    (trace_a11 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a11_cells (n : Nat) (bound : n ≤ 11) :
    fixtureCells (trace_a11 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem trace_a12_owned (n : Nat) (bound : n < 25) :
    (trace_a12 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a12_cells (n : Nat) (bound : n ≤ 25) :
    fixtureCells (trace_a12 n).stores ≤ 13 := by
  interval_cases n <;> decide

theorem trace_a13_owned (n : Nat) (bound : n < 24) :
    (trace_a13 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a13_cells (n : Nat) (bound : n ≤ 24) :
    fixtureCells (trace_a13 n).stores ≤ 13 := by
  interval_cases n <;> decide

theorem trace_a14_owned (n : Nat) (bound : n < 13) :
    (trace_a14 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a14_cells (n : Nat) (bound : n ≤ 13) :
    fixtureCells (trace_a14 n).stores ≤ 5 := by
  interval_cases n <;> decide

theorem trace_a15_owned (n : Nat) (bound : n < 16) :
    (trace_a15 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a15_cells (n : Nat) (bound : n ≤ 16) :
    fixtureCells (trace_a15 n).stores ≤ 7 := by
  interval_cases n <;> decide

theorem trace_a16_owned (n : Nat) (bound : n < 31) :
    (trace_a16 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a16_cells (n : Nat) (bound : n ≤ 31) :
    fixtureCells (trace_a16 n).stores ≤ 18 := by
  interval_cases n <;> decide

theorem trace_a17_owned (n : Nat) (bound : n < 33) :
    (trace_a17 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a17_cells (n : Nat) (bound : n ≤ 33) :
    fixtureCells (trace_a17 n).stores ≤ 18 := by
  interval_cases n <;> decide

theorem trace_a18_owned (n : Nat) (bound : n < 42) :
    (trace_a18 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a18_cells (n : Nat) (bound : n ≤ 42) :
    fixtureCells (trace_a18 n).stores ≤ 16 := by
  interval_cases n <;> decide

theorem trace_a19_owned (n : Nat) (bound : n < 22) :
    (trace_a19 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a19_cells (n : Nat) (bound : n ≤ 22) :
    fixtureCells (trace_a19 n).stores ≤ 15 := by
  interval_cases n <;> decide

theorem trace_a20_owned (n : Nat) (bound : n < 25) :
    (trace_a20 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a20_cells (n : Nat) (bound : n ≤ 25) :
    fixtureCells (trace_a20 n).stores ≤ 15 := by
  interval_cases n <;> decide

theorem trace_a21_owned (n : Nat) (bound : n < 24) :
    (trace_a21 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a21_cells (n : Nat) (bound : n ≤ 24) :
    fixtureCells (trace_a21 n).stores ≤ 11 := by
  interval_cases n <;> decide

theorem trace_d01_owned (n : Nat) (bound : n < 4) :
    (trace_d01 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d01_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_d01 n).stores ≤ 8 := by
  interval_cases n <;> decide

theorem trace_d02_owned (n : Nat) (bound : n < 9) :
    (trace_d02 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d02_cells (n : Nat) (bound : n ≤ 9) :
    fixtureCells (trace_d02 n).stores ≤ 11 := by
  interval_cases n <;> decide

theorem trace_d03_owned (n : Nat) (bound : n < 6) :
    (trace_d03 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d03_cells (n : Nat) (bound : n ≤ 6) :
    fixtureCells (trace_d03 n).stores ≤ 3 := by
  interval_cases n <;> decide

theorem trace_d04_owned (n : Nat) (bound : n < 7) :
    (trace_d04 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d04_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (trace_d04 n).stores ≤ 9 := by
  interval_cases n <;> decide

theorem trace_d05_owned (n : Nat) (bound : n < 13) :
    (trace_d05 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d05_cells (n : Nat) (bound : n ≤ 13) :
    fixtureCells (trace_d05 n).stores ≤ 11 := by
  interval_cases n <;> decide

theorem trace_d06_owned (n : Nat) (bound : n < 30) :
    (trace_d06 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d06_cells (n : Nat) (bound : n ≤ 30) :
    fixtureCells (trace_d06 n).stores ≤ 18 := by
  interval_cases n <;> decide

theorem trace_d07_owned (n : Nat) (bound : n < 29) :
    (trace_d07 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d07_cells (n : Nat) (bound : n ≤ 29) :
    fixtureCells (trace_d07 n).stores ≤ 18 := by
  interval_cases n <;> decide

theorem trace_d08_owned (n : Nat) (bound : n < 7) :
    (trace_d08 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d08_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (trace_d08 n).stores ≤ 6 := by
  interval_cases n <;> decide

theorem trace_d09_owned (n : Nat) (bound : n < 5) :
    (trace_d09 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d09_cells (n : Nat) (bound : n ≤ 5) :
    fixtureCells (trace_d09 n).stores ≤ 0 := by
  interval_cases n <;> decide

theorem trace_d10_owned (n : Nat) (bound : n < 4) :
    (trace_d10 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d10_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_d10 n).stores ≤ 0 := by
  interval_cases n <;> decide

theorem trace_d11_owned (n : Nat) (bound : n < 3) :
    (trace_d11 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d11_cells (n : Nat) (bound : n ≤ 3) :
    fixtureCells (trace_d11 n).stores ≤ 1 := by
  interval_cases n <;> decide

theorem trace_d12_owned (n : Nat) (bound : n < 2) :
    (trace_d12 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d12_cells (n : Nat) (bound : n ≤ 2) :
    fixtureCells (trace_d12 n).stores ≤ 1 := by
  interval_cases n <;> decide

theorem trace_d13_owned (n : Nat) (bound : n < 1) :
    (trace_d13 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d13_cells (n : Nat) (bound : n ≤ 1) :
    fixtureCells (trace_d13 n).stores ≤ 3 := by
  interval_cases n <;> decide

theorem trace_r01_owned (n : Nat) (bound : n < 7) :
    (trace_r01 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r01_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (trace_r01 n).stores ≤ 13 := by
  interval_cases n <;> decide

theorem trace_r02_owned (n : Nat) (bound : n < 4) :
    (trace_r02 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r02_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_r02 n).stores ≤ 15 := by
  interval_cases n <;> decide

theorem trace_r03_owned (n : Nat) (bound : n < 17) :
    (trace_r03 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r03_cells (n : Nat) (bound : n ≤ 17) :
    fixtureCells (trace_r03 n).stores ≤ 16 := by
  interval_cases n <;> decide

theorem trace_r04_owned (n : Nat) (bound : n < 27) :
    (trace_r04 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r04_cells (n : Nat) (bound : n ≤ 27) :
    fixtureCells (trace_r04 n).stores ≤ 15 := by
  interval_cases n <;> decide

theorem trace_r05_owned (n : Nat) (bound : n < 6) :
    (trace_r05 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r05_cells (n : Nat) (bound : n ≤ 6) :
    fixtureCells (trace_r05 n).stores ≤ 7 := by
  interval_cases n <;> decide

theorem trace_r06_owned (n : Nat) (bound : n < 6) :
    (trace_r06 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r06_cells (n : Nat) (bound : n ≤ 6) :
    fixtureCells (trace_r06 n).stores ≤ 7 := by
  interval_cases n <;> decide

theorem trace_r07_owned (n : Nat) (bound : n < 22) :
    (trace_r07 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r07_cells (n : Nat) (bound : n ≤ 22) :
    fixtureCells (trace_r07 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem trace_r08_owned (n : Nat) (bound : n < 41) :
    (trace_r08 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r08_cells (n : Nat) (bound : n ≤ 41) :
    fixtureCells (trace_r08 n).stores ≤ 17 := by
  interval_cases n <;> decide

theorem trace_r09_owned (n : Nat) (bound : n < 40) :
    (trace_r09 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r09_cells (n : Nat) (bound : n ≤ 40) :
    fixtureCells (trace_r09 n).stores ≤ 17 := by
  interval_cases n <;> decide

theorem trace_r10_owned (n : Nat) (bound : n < 20) :
    (trace_r10 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r10_cells (n : Nat) (bound : n ≤ 20) :
    fixtureCells (trace_r10 n).stores ≤ 15 := by
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
