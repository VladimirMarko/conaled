import Applications.FRP.RegionalMigrationIO

/-! Independent fixtures for real cut changes and quiescent lifecycle controls. -/
namespace FRPSpec.Regional.Reconfiguration
open Progress Progress.Feedback Selection

def switched : List Command :=
  [.input fixtureA,.prepare (both .fused) (both .split) roomy true true,.commit,
   .input fixtureB,.prepare (both .split) (both .checked) roomy true true,.commit,
   .input fixtureC]

theorem switched_outputs : (execute (initial (both .fused)) switched).2 =
    [(true,true),(false,true),(true,false)] := by
  have h := (execute_refines (initial (both .fused)) switched).1
  exact h

theorem switched_state : observation (execute (initial (both .fused)) switched).1.active =
    (false,true) := (execute_refines (initial (both .fused)) switched).2

/-- Unequal state detects a conversion that swaps independent delays. -/
theorem unequal_transfer :
    observation (transfer ⟨both .split,resume (both .split) (true,false)⟩ (both .checked)) =
      (true,false) := transfer_observation _ _

theorem swapped_is_wrong :
    observation (transfer ⟨both .split,resume (both .split) (true,false)⟩ (both .checked)) ≠
      observation ⟨both .checked,resume (both .checked) (false,true)⟩ := by decide

example : (prepare (initial (both .fused)) (both .fused) (both .split) roomy true true).status =
    .prepared := by decide
example : (prepare (initial (both .fused)) (both .fused) (both .split) roomy false true).status =
    .allocation := by decide
example : (prepare (initial (both .fused)) (both .fused) (both .split) roomy true false).status =
    .validation := by decide
example : (prepare (initial (both .fused)) (both .checked) (both .split) roomy true true).status =
    .stale := by decide

/-- Passing target steady-state selection does not discharge migration controls. -/
theorem steady_not_transfer :
    eligible roomy (both .split) ∧
    (prepare ⟨(initial (both .fused)).active,none,false⟩ (both .fused) (both .split)
      roomy true true).status = .throttled := by decide

example : (prepare (initial (both .fused)) (both .fused) (both .split)
    ⟨0,1,true,true⟩ true true).status = .unsupported := by decide
example : (prepare (initial (both .fused)) (both .fused) (both .split)
    ⟨(both .split).plan.storage,1,true,true⟩ true true).status = .capacity := by decide

example : bill (prepare (initial (both .fused)) (both .fused) (both .split)
    roomy true true).events = 12 := by decide
example : bill (prepare (initial (both .fused)) (both .fused) (both .split)
    roomy true false).events = 14 := by decide
example : transferPeak (initial (both .fused)).active (both .split) = 14 := by decide

end FRPSpec.Regional.Reconfiguration
