import Examples.RotationCertificateStreamMachine.Traces

/-!
# RotationCertificateStreamMachine: TraceSteps
-/

namespace Examples.RotationCertificateStreamMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.StreamMachine

section LiteralTraceEdges
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem traceA01_steps (n : Nat) (bound : n < 4) :
    step caller ((traceA01 n).reached regs ctx) =
      some ((traceA01 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (traceA01 0).stores rfl ((traceA01 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceA01 1).stores ((traceA01 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceA01 2).stores ((traceA01 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceA01 2).stage.apply regs)) (equalityContext (traceA01 2).stores ctx))
  · exact equality_join_step caller .equal (traceA01 3).stores ((traceA01 3).stage.apply regs) ctx

theorem traceA02_steps (n : Nat) (bound : n < 4) :
    step caller ((traceA02 n).reached regs ctx) =
      some ((traceA02 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceA02 0).stores 15 [] rfl ((traceA02 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA02 1).stores ((traceA02 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((traceA02 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA02 1).stores.certificate) (fuelContext (traceA02 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceA02 2).stores ((traceA02 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA02 2).stage.apply regs) (FuelDispatchMachine.stores ((traceA02 2).stores.certificate) (fuelContext (traceA02 2).stores ctx)))
  · exact fuel_join_step caller .zero (traceA02 3).stores ((traceA02 3).stage.apply regs) ctx

theorem traceA03_steps (n : Nat) (bound : n < 5) :
    step caller ((traceA03 n).reached regs ctx) =
      some ((traceA03 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (traceA03 0).stores rfl ((traceA03 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceA03 1).stores ((traceA03 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceA03 2).stores ((traceA03 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((traceA03 2).stage.apply regs)) (equalityContext (traceA03 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA03 3).stores ((traceA03 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceA03 3).stage.apply regs)) (equalityContext (traceA03 3).stores ctx))
  · exact equality_join_step caller .equal (traceA03 4).stores ((traceA03 4).stage.apply regs) ctx

theorem traceA04_steps (n : Nat) (bound : n < 7) :
    step caller ((traceA04 n).reached regs ctx) =
      some ((traceA04 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (traceA04 0).stores rfl ((traceA04 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceA04 1).stores ((traceA04 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceA04 2).stores ((traceA04 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((traceA04 2).stage.apply regs)) (equalityContext (traceA04 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA04 3).stores ((traceA04 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((traceA04 3).stage.apply regs)) (equalityContext (traceA04 3).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA04 4).stores ((traceA04 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((traceA04 4).stage.apply regs)) (equalityContext (traceA04 4).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA04 5).stores ((traceA04 5).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceA04 5).stage.apply regs)) (equalityContext (traceA04 5).stores ctx))
  · exact equality_join_step caller .equal (traceA04 6).stores ((traceA04 6).stage.apply regs) ctx

theorem traceA05_steps (n : Nat) (bound : n < 9) :
    step caller ((traceA05 n).reached regs ctx) =
      some ((traceA05 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (traceA05 0).stores rfl ((traceA05 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceA05 1).stores ((traceA05 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceA05 2).stores ((traceA05 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 1, 0, 0] [0, 1, 0, 0] (equalityRegisterEquiv.symm ((traceA05 2).stage.apply regs)) (equalityContext (traceA05 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA05 3).stores ((traceA05 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [1, 0, 0] [1, 0, 0] (equalityRegisterEquiv.symm ((traceA05 3).stage.apply regs)) (equalityContext (traceA05 3).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA05 4).stores ((traceA05 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((traceA05 4).stage.apply regs)) (equalityContext (traceA05 4).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA05 5).stores ((traceA05 5).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((traceA05 5).stage.apply regs)) (equalityContext (traceA05 5).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA05 6).stores ((traceA05 6).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((traceA05 6).stage.apply regs)) (equalityContext (traceA05 6).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA05 7).stores ((traceA05 7).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceA05 7).stage.apply regs)) (equalityContext (traceA05 7).stores ctx))
  · exact equality_join_step caller .equal (traceA05 8).stores ((traceA05 8).stage.apply regs) ctx

theorem traceA06_steps (n : Nat) (bound : n < 4) :
    step caller ((traceA06 n).reached regs ctx) =
      some ((traceA06 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (traceA06 0).stores rfl ((traceA06 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceA06 1).stores ((traceA06 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceA06 2).stores ((traceA06 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_different (fun _ => .halt) 1 0 [0, 0] [] (equalityRegisterEquiv.symm ((traceA06 2).stage.apply regs)) (equalityContext (traceA06 2).stores ctx) (by decide))
  · exact equality_join_step caller .different (traceA06 3).stores ((traceA06 3).stage.apply regs) ctx

theorem traceA07_steps (n : Nat) (bound : n < 5) :
    step caller ((traceA07 n).reached regs ctx) =
      some ((traceA07 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (traceA07 0).stores rfl ((traceA07 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceA07 1).stores ((traceA07 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceA07 2).stores ((traceA07 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 15 [] [] (equalityRegisterEquiv.symm ((traceA07 2).stage.apply regs)) (equalityContext (traceA07 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA07 3).stores ((traceA07 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceA07 3).stage.apply regs)) (equalityContext (traceA07 3).stores ctx))
  · exact equality_join_step caller .equal (traceA07 4).stores ((traceA07 4).stage.apply regs) ctx

theorem traceA08_steps (n : Nat) (bound : n < 6) :
    step caller ((traceA08 n).reached regs ctx) =
      some ((traceA08 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (traceA08 0).stores rfl ((traceA08 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceA08 1).stores ((traceA08 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceA08 2).stores ((traceA08 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 15, 2] [0, 3, 11] (equalityRegisterEquiv.symm ((traceA08 2).stage.apply regs)) (equalityContext (traceA08 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA08 3).stores ((traceA08 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [15, 2] [3, 11] (equalityRegisterEquiv.symm ((traceA08 3).stage.apply regs)) (equalityContext (traceA08 3).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA08 4).stores ((traceA08 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_different (fun _ => .halt) 15 3 [2] [11] (equalityRegisterEquiv.symm ((traceA08 4).stage.apply regs)) (equalityContext (traceA08 4).stores ctx) (by decide))
  · exact equality_join_step caller .different (traceA08 5).stores ((traceA08 5).stage.apply regs) ctx

theorem traceA09_steps (n : Nat) (bound : n < 8) :
    step caller ((traceA09 n).reached regs ctx) =
      some ((traceA09 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceA09 0).stores 6 [10] rfl ((traceA09 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA09 1).stores ((traceA09 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA09 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA09 1).stores.certificate) (fuelContext (traceA09 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA09 2).stores ((traceA09 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA09 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceA09 2).stores.certificate) (fuelContext (traceA09 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA09 3).stores ((traceA09 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((traceA09 3).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((traceA09 3).stores.certificate) (fuelContext (traceA09 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceA09 4).stores ((traceA09 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA09 4).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceA09 4).stores.certificate) (fuelContext (traceA09 4).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceA09 5).stores ((traceA09 5).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA09 5).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA09 5).stores.certificate) (fuelContext (traceA09 5).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceA09 6).stores ((traceA09 6).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((traceA09 6).stage.apply regs) (FuelDispatchMachine.stores ((traceA09 6).stores.certificate) (fuelContext (traceA09 6).stores ctx)))
  · exact fuel_join_step caller .zero (traceA09 7).stores ((traceA09 7).stage.apply regs) ctx

theorem traceA10_steps (n : Nat) (bound : n < 7) :
    step caller ((traceA10 n).reached regs ctx) =
      some ((traceA10 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceA10 0).stores 15 [] rfl ((traceA10 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA10 1).stores ((traceA10 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA10 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA10 1).stores.certificate) (fuelContext (traceA10 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceA10 2).stores ((traceA10 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA10 2).stage.apply regs) (FuelDispatchMachine.stores ((traceA10 2).stores.certificate) (fuelContext (traceA10 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceA10 3).stores ((traceA10 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceA10 4).stores ((traceA10 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA10 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA10 4).stores) (applyContext (traceA10 4).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (traceA10 5).stores ((traceA10 5).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (traceA10 5).stores)
        (applyRegisterEquiv.symm ((traceA10 5).stage.apply regs)) (applyContext (traceA10 5).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (traceA10 6).stores ((traceA10 6).stage.apply regs) ctx

theorem traceA11_steps (n : Nat) (bound : n < 11) :
    step caller ((traceA11 n).reached regs ctx) =
      some ((traceA11 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceA11 0).stores 6 [8, 15] rfl ((traceA11 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA11 1).stores ((traceA11 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA11 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA11 1).stores.certificate) (fuelContext (traceA11 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceA11 2).stores ((traceA11 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA11 2).stage.apply regs) (FuelDispatchMachine.stores ((traceA11 2).stores.certificate) (fuelContext (traceA11 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceA11 3).stores ((traceA11 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceA11 4).stores ((traceA11 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [8, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA11 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA11 4).stores) (applyContext (traceA11 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceA11 5).stores ((traceA11 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA11 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA11 5).stores) (applyContext (traceA11 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceA11 6).stores ((traceA11 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_foreign (fun _ => .halt) .left 15 [] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA11 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA11 6).stores) (applyContext (traceA11 6).stores ctx)) (by decide) (by decide) (by decide))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (traceA11 7).stores ((traceA11 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_cons (fun _ => .halt) .left .left [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA11 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA11 7).stores) (applyContext (traceA11 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (traceA11 8).stores ((traceA11 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_nil (fun _ => .halt) .left [8, 15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA11 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA11 8).stores) (applyContext (traceA11 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (traceA11 9).stores ((traceA11 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (traceA11 9).stores)
        (applyRegisterEquiv.symm ((traceA11 9).stage.apply regs)) (applyContext (traceA11 9).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (traceA11 10).stores ((traceA11 10).stage.apply regs) ctx

theorem traceA12_steps (n : Nat) (bound : n < 25) :
    step caller ((traceA12 n).reached regs ctx) =
      some ((traceA12 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceA12 0).stores 6 [10] rfl ((traceA12 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA12 1).stores ((traceA12 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA12 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA12 1).stores.certificate) (fuelContext (traceA12 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceA12 2).stores ((traceA12 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA12 2).stage.apply regs) (FuelDispatchMachine.stores ((traceA12 2).stores.certificate) (fuelContext (traceA12 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceA12 3).stores ((traceA12 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceA12 4).stores ((traceA12 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA12 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA12 4).stores) (applyContext (traceA12 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceA12 5).stores ((traceA12 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA12 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA12 5).stores) (applyContext (traceA12 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceA12 6).stores ((traceA12 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA12 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA12 6).stores) (applyContext (traceA12 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceA12 7).stores ((traceA12 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceA12 7).stores)
        (applyRegisterEquiv.symm ((traceA12 7).stage.apply regs)) (applyContext (traceA12 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceA12 8).stores ((traceA12 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceA12 9).stores ((traceA12 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (traceA12 10).stores ((traceA12 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (traceA12 11).stores ((traceA12 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceA12 12).stores ((traceA12 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceA12 13).stores ((traceA12 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceA12 14).stores ((traceA12 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceA12 15).stores ((traceA12 15).stage.apply regs) ctx
  · exact inspect_step_nil caller (traceA12 16).stores rfl ((traceA12 16).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceA12 17).stores ((traceA12 17).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceA12 18).stores ((traceA12 18).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0] [1, 0, 0, 0] (equalityRegisterEquiv.symm ((traceA12 18).stage.apply regs)) (equalityContext (traceA12 18).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA12 19).stores ((traceA12 19).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((traceA12 19).stage.apply regs)) (equalityContext (traceA12 19).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA12 20).stores ((traceA12 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((traceA12 20).stage.apply regs)) (equalityContext (traceA12 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA12 21).stores ((traceA12 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((traceA12 21).stage.apply regs)) (equalityContext (traceA12 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA12 22).stores ((traceA12 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((traceA12 22).stage.apply regs)) (equalityContext (traceA12 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA12 23).stores ((traceA12 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceA12 23).stage.apply regs)) (equalityContext (traceA12 23).stores ctx))
  · exact equality_join_step caller .equal (traceA12 24).stores ((traceA12 24).stage.apply regs) ctx

theorem traceA13_steps (n : Nat) (bound : n < 24) :
    step caller ((traceA13 n).reached regs ctx) =
      some ((traceA13 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceA13 0).stores 7 [10] rfl ((traceA13 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA13 1).stores ((traceA13 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA13 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA13 1).stores.certificate) (fuelContext (traceA13 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceA13 2).stores ((traceA13 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA13 2).stage.apply regs) (FuelDispatchMachine.stores ((traceA13 2).stores.certificate) (fuelContext (traceA13 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceA13 3).stores ((traceA13 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceA13 4).stores ((traceA13 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .right [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA13 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA13 4).stores) (applyContext (traceA13 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .right) (traceA13 5).stores ((traceA13 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .right [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA13 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA13 5).stores) (applyContext (traceA13 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .right) (traceA13 6).stores ((traceA13 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .right [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA13 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA13 6).stores) (applyContext (traceA13 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .right)) (traceA13 7).stores ((traceA13 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .right) (applyData (traceA13 7).stores)
        (applyRegisterEquiv.symm ((traceA13 7).stage.apply regs)) (applyContext (traceA13 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .right) (traceA13 8).stores ((traceA13 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .right) (traceA13 9).stores ((traceA13 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .right) (traceA13 10).stores ((traceA13 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (traceA13 11).stores ((traceA13 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (traceA13 12).stores ((traceA13 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceA13 13).stores ((traceA13 13).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceA13 14).stores ((traceA13 14).stage.apply regs) ctx
  · exact inspect_step_nil caller (traceA13 15).stores rfl ((traceA13 15).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceA13 16).stores ((traceA13 16).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceA13 17).stores ((traceA13 17).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 1, 0, 0] [0, 1, 0, 0] (equalityRegisterEquiv.symm ((traceA13 17).stage.apply regs)) (equalityContext (traceA13 17).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA13 18).stores ((traceA13 18).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [1, 0, 0] [1, 0, 0] (equalityRegisterEquiv.symm ((traceA13 18).stage.apply regs)) (equalityContext (traceA13 18).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA13 19).stores ((traceA13 19).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((traceA13 19).stage.apply regs)) (equalityContext (traceA13 19).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA13 20).stores ((traceA13 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((traceA13 20).stage.apply regs)) (equalityContext (traceA13 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA13 21).stores ((traceA13 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((traceA13 21).stage.apply regs)) (equalityContext (traceA13 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA13 22).stores ((traceA13 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceA13 22).stage.apply regs)) (equalityContext (traceA13 22).stores ctx))
  · exact equality_join_step caller .equal (traceA13 23).stores ((traceA13 23).stage.apply regs) ctx

theorem traceA14_steps (n : Nat) (bound : n < 13) :
    step caller ((traceA14 n).reached regs ctx) =
      some ((traceA14 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceA14 0).stores 6 [10] rfl ((traceA14 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA14 1).stores ((traceA14 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA14 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA14 1).stores.certificate) (fuelContext (traceA14 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceA14 2).stores ((traceA14 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA14 2).stage.apply regs) (FuelDispatchMachine.stores ((traceA14 2).stores.certificate) (fuelContext (traceA14 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceA14 3).stores ((traceA14 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceA14 4).stores ((traceA14 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA14 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA14 4).stores) (applyContext (traceA14 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceA14 5).stores ((traceA14 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA14 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA14 5).stores) (applyContext (traceA14 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceA14 6).stores ((traceA14 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA14 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA14 6).stores) (applyContext (traceA14 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceA14 7).stores ((traceA14 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceA14 7).stores)
        (applyRegisterEquiv.symm ((traceA14 7).stage.apply regs)) (applyContext (traceA14 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceA14 8).stores ((traceA14 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceA14 9).stores ((traceA14 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (traceA14 10).stores ((traceA14 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (traceA14 11).stores ((traceA14 11).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (traceA14 12).stores ((traceA14 12).stage.apply regs) ctx

theorem traceA15_steps (n : Nat) (bound : n < 16) :
    step caller ((traceA15 n).reached regs ctx) =
      some ((traceA15 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceA15 0).stores 6 [8, 8, 10] rfl ((traceA15 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA15 1).stores ((traceA15 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA15 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA15 1).stores.certificate) (fuelContext (traceA15 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceA15 2).stores ((traceA15 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA15 2).stage.apply regs) (FuelDispatchMachine.stores ((traceA15 2).stores.certificate) (fuelContext (traceA15 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceA15 3).stores ((traceA15 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceA15 4).stores ((traceA15 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [8, 8, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA15 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA15 4).stores) (applyContext (traceA15 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceA15 5).stores ((traceA15 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [8, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA15 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA15 5).stores) (applyContext (traceA15 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceA15 6).stores ((traceA15 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [10] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA15 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA15 6).stores) (applyContext (traceA15 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceA15 7).stores ((traceA15 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.left, .left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA15 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA15 7).stores) (applyContext (traceA15 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceA15 8).stores ((traceA15 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA15 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA15 8).stores) (applyContext (traceA15 8).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceA15 9).stores ((traceA15 9).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA15 9).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA15 9).stores) (applyContext (traceA15 9).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceA15 10).stores ((traceA15 10).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left, .left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA15 10).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA15 10).stores) (applyContext (traceA15 10).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceA15 11).stores ((traceA15 11).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceA15 11).stores)
        (applyRegisterEquiv.symm ((traceA15 11).stage.apply regs)) (applyContext (traceA15 11).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceA15 12).stores ((traceA15 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (traceA15 13).stores ((traceA15 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (traceA15 14).stores ((traceA15 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (traceA15 15).stores ((traceA15 15).stage.apply regs) ctx

theorem traceA16_steps (n : Nat) (bound : n < 31) :
    step caller ((traceA16 n).reached regs ctx) =
      some ((traceA16 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceA16 0).stores 6 [8, 10] rfl ((traceA16 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA16 1).stores ((traceA16 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA16 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA16 1).stores.certificate) (fuelContext (traceA16 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceA16 2).stores ((traceA16 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA16 2).stage.apply regs) (FuelDispatchMachine.stores ((traceA16 2).stores.certificate) (fuelContext (traceA16 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceA16 3).stores ((traceA16 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceA16 4).stores ((traceA16 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [8, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA16 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA16 4).stores) (applyContext (traceA16 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceA16 5).stores ((traceA16 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA16 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA16 5).stores) (applyContext (traceA16 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceA16 6).stores ((traceA16 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA16 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA16 6).stores) (applyContext (traceA16 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceA16 7).stores ((traceA16 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA16 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA16 7).stores) (applyContext (traceA16 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceA16 8).stores ((traceA16 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA16 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA16 8).stores) (applyContext (traceA16 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceA16 9).stores ((traceA16 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceA16 9).stores)
        (applyRegisterEquiv.symm ((traceA16 9).stage.apply regs)) (applyContext (traceA16 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceA16 10).stores ((traceA16 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (traceA16 11).stores ((traceA16 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceA16 12).stores ((traceA16 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (traceA16 13).stores ((traceA16 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (traceA16 14).stores ((traceA16 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceA16 15).stores ((traceA16 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceA16 16).stores ((traceA16 16).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceA16 17).stores ((traceA16 17).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceA16 18).stores ((traceA16 18).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceA16 19).stores ((traceA16 19).stage.apply regs) ctx
  · exact inspect_step_nil caller (traceA16 20).stores rfl ((traceA16 20).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceA16 21).stores ((traceA16 21).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceA16 22).stores ((traceA16 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 1, 0, 0, 0, 0] [1, 1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((traceA16 22).stage.apply regs)) (equalityContext (traceA16 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA16 23).stores ((traceA16 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0, 0] [1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((traceA16 23).stage.apply regs)) (equalityContext (traceA16 23).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA16 24).stores ((traceA16 24).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0, 0] [0, 0, 0, 0] (equalityRegisterEquiv.symm ((traceA16 24).stage.apply regs)) (equalityContext (traceA16 24).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA16 25).stores ((traceA16 25).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((traceA16 25).stage.apply regs)) (equalityContext (traceA16 25).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA16 26).stores ((traceA16 26).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((traceA16 26).stage.apply regs)) (equalityContext (traceA16 26).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA16 27).stores ((traceA16 27).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((traceA16 27).stage.apply regs)) (equalityContext (traceA16 27).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA16 28).stores ((traceA16 28).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((traceA16 28).stage.apply regs)) (equalityContext (traceA16 28).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA16 29).stores ((traceA16 29).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceA16 29).stage.apply regs)) (equalityContext (traceA16 29).stores ctx))
  · exact equality_join_step caller .equal (traceA16 30).stores ((traceA16 30).stage.apply regs) ctx

theorem traceA17_steps (n : Nat) (bound : n < 33) :
    step caller ((traceA17 n).reached regs ctx) =
      some ((traceA17 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceA17 0).stores 6 [9, 10] rfl ((traceA17 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA17 1).stores ((traceA17 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA17 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA17 1).stores.certificate) (fuelContext (traceA17 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceA17 2).stores ((traceA17 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA17 2).stage.apply regs) (FuelDispatchMachine.stores ((traceA17 2).stores.certificate) (fuelContext (traceA17 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceA17 3).stores ((traceA17 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceA17 4).stores ((traceA17 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [9, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA17 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA17 4).stores) (applyContext (traceA17 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceA17 5).stores ((traceA17 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .right [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA17 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA17 5).stores) (applyContext (traceA17 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceA17 6).stores ((traceA17 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.right] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA17 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA17 6).stores) (applyContext (traceA17 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceA17 7).stores ((traceA17 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .right [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA17 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA17 7).stores) (applyContext (traceA17 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceA17 8).stores ((traceA17 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA17 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA17 8).stores) (applyContext (traceA17 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceA17 9).stores ((traceA17 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceA17 9).stores)
        (applyRegisterEquiv.symm ((traceA17 9).stage.apply regs)) (applyContext (traceA17 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceA17 10).stores ((traceA17 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanPrefix .left) (traceA17 11).stores ((traceA17 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (traceA17 12).stores ((traceA17 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceA17 13).stores ((traceA17 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (traceA17 14).stores ((traceA17 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (traceA17 15).stores ((traceA17 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceA17 16).stores ((traceA17 16).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceA17 17).stores ((traceA17 17).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceA17 18).stores ((traceA17 18).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceA17 19).stores ((traceA17 19).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceA17 20).stores ((traceA17 20).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceA17 21).stores ((traceA17 21).stage.apply regs) ctx
  · exact inspect_step_nil caller (traceA17 22).stores rfl ((traceA17 22).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceA17 23).stores ((traceA17 23).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceA17 24).stores ((traceA17 24).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 1, 1, 0, 0, 0] [0, 1, 1, 0, 0, 0] (equalityRegisterEquiv.symm ((traceA17 24).stage.apply regs)) (equalityContext (traceA17 24).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA17 25).stores ((traceA17 25).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [1, 1, 0, 0, 0] [1, 1, 0, 0, 0] (equalityRegisterEquiv.symm ((traceA17 25).stage.apply regs)) (equalityContext (traceA17 25).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA17 26).stores ((traceA17 26).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0] [1, 0, 0, 0] (equalityRegisterEquiv.symm ((traceA17 26).stage.apply regs)) (equalityContext (traceA17 26).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA17 27).stores ((traceA17 27).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((traceA17 27).stage.apply regs)) (equalityContext (traceA17 27).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA17 28).stores ((traceA17 28).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((traceA17 28).stage.apply regs)) (equalityContext (traceA17 28).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA17 29).stores ((traceA17 29).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((traceA17 29).stage.apply regs)) (equalityContext (traceA17 29).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA17 30).stores ((traceA17 30).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((traceA17 30).stage.apply regs)) (equalityContext (traceA17 30).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA17 31).stores ((traceA17 31).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceA17 31).stage.apply regs)) (equalityContext (traceA17 31).stores ctx))
  · exact equality_join_step caller .equal (traceA17 32).stores ((traceA17 32).stage.apply regs) ctx

theorem traceA18_steps (n : Nat) (bound : n < 42) :
    step caller ((traceA18 n).reached regs ctx) =
      some ((traceA18 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceA18 0).stores 6 [10, 7, 10] rfl ((traceA18 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA18 1).stores ((traceA18 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((traceA18 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA18 1).stores.certificate) (fuelContext (traceA18 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA18 2).stores ((traceA18 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA18 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceA18 2).stores.certificate) (fuelContext (traceA18 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceA18 3).stores ((traceA18 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA18 3).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA18 3).stores.certificate) (fuelContext (traceA18 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceA18 4).stores ((traceA18 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((traceA18 4).stage.apply regs) (FuelDispatchMachine.stores ((traceA18 4).stores.certificate) (fuelContext (traceA18 4).stores ctx)))
  · exact fuel_join_step caller .positive (traceA18 5).stores ((traceA18 5).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceA18 6).stores ((traceA18 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 7, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA18 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA18 6).stores) (applyContext (traceA18 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceA18 7).stores ((traceA18 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [7, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA18 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA18 7).stores) (applyContext (traceA18 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceA18 8).stores ((traceA18 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [7, 10] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA18 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA18 8).stores) (applyContext (traceA18 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceA18 9).stores ((traceA18 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceA18 9).stores)
        (applyRegisterEquiv.symm ((traceA18 9).stage.apply regs)) (applyContext (traceA18 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceA18 10).stores ((traceA18 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceA18 11).stores ((traceA18 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (traceA18 12).stores ((traceA18 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (traceA18 13).stores ((traceA18 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceA18 14).stores ((traceA18 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceA18 15).stores ((traceA18 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceA18 16).stores ((traceA18 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceA18 17).stores ((traceA18 17).stage.apply regs) ctx
  · exact inspect_step_cons caller (traceA18 18).stores 7 [10] rfl ((traceA18 18).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA18 19).stores ((traceA18 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA18 19).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA18 19).stores.certificate) (fuelContext (traceA18 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceA18 20).stores ((traceA18 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((traceA18 20).stage.apply regs) (FuelDispatchMachine.stores ((traceA18 20).stores.certificate) (fuelContext (traceA18 20).stores ctx)))
  · exact fuel_join_step caller .positive (traceA18 21).stores ((traceA18 21).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceA18 22).stores ((traceA18 22).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .right [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA18 22).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA18 22).stores) (applyContext (traceA18 22).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .right) (traceA18 23).stores ((traceA18 23).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .right [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA18 23).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA18 23).stores) (applyContext (traceA18 23).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .right) (traceA18 24).stores ((traceA18 24).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .right [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA18 24).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA18 24).stores) (applyContext (traceA18 24).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .right)) (traceA18 25).stores ((traceA18 25).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .right) (applyData (traceA18 25).stores)
        (applyRegisterEquiv.symm ((traceA18 25).stage.apply regs)) (applyContext (traceA18 25).stores ctx))
  · exact apply_position_advance_step caller (.seek .right) (traceA18 26).stores ((traceA18 26).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .right) (traceA18 27).stores ((traceA18 27).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .right) (traceA18 28).stores ((traceA18 28).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (traceA18 29).stores ((traceA18 29).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (traceA18 30).stores ((traceA18 30).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceA18 31).stores ((traceA18 31).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceA18 32).stores ((traceA18 32).stage.apply regs) ctx
  · exact inspect_step_nil caller (traceA18 33).stores rfl ((traceA18 33).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceA18 34).stores ((traceA18 34).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceA18 35).stores ((traceA18 35).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 1, 0, 0] [0, 1, 0, 0] (equalityRegisterEquiv.symm ((traceA18 35).stage.apply regs)) (equalityContext (traceA18 35).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA18 36).stores ((traceA18 36).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [1, 0, 0] [1, 0, 0] (equalityRegisterEquiv.symm ((traceA18 36).stage.apply regs)) (equalityContext (traceA18 36).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA18 37).stores ((traceA18 37).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((traceA18 37).stage.apply regs)) (equalityContext (traceA18 37).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA18 38).stores ((traceA18 38).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((traceA18 38).stage.apply regs)) (equalityContext (traceA18 38).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA18 39).stores ((traceA18 39).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((traceA18 39).stage.apply regs)) (equalityContext (traceA18 39).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA18 40).stores ((traceA18 40).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceA18 40).stage.apply regs)) (equalityContext (traceA18 40).stores ctx))
  · exact equality_join_step caller .equal (traceA18 41).stores ((traceA18 41).stage.apply regs) ctx

theorem traceA19_steps (n : Nat) (bound : n < 22) :
    step caller ((traceA19 n).reached regs ctx) =
      some ((traceA19 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceA19 0).stores 6 [10, 7, 10] rfl ((traceA19 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA19 1).stores ((traceA19 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA19 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA19 1).stores.certificate) (fuelContext (traceA19 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceA19 2).stores ((traceA19 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA19 2).stage.apply regs) (FuelDispatchMachine.stores ((traceA19 2).stores.certificate) (fuelContext (traceA19 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceA19 3).stores ((traceA19 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceA19 4).stores ((traceA19 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 7, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA19 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA19 4).stores) (applyContext (traceA19 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceA19 5).stores ((traceA19 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [7, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA19 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA19 5).stores) (applyContext (traceA19 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceA19 6).stores ((traceA19 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [7, 10] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA19 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA19 6).stores) (applyContext (traceA19 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceA19 7).stores ((traceA19 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceA19 7).stores)
        (applyRegisterEquiv.symm ((traceA19 7).stage.apply regs)) (applyContext (traceA19 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceA19 8).stores ((traceA19 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceA19 9).stores ((traceA19 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (traceA19 10).stores ((traceA19 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (traceA19 11).stores ((traceA19 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceA19 12).stores ((traceA19 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceA19 13).stores ((traceA19 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceA19 14).stores ((traceA19 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceA19 15).stores ((traceA19 15).stage.apply regs) ctx
  · exact inspect_step_cons caller (traceA19 16).stores 7 [10] rfl ((traceA19 16).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA19 17).stores ((traceA19 17).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA19 17).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA19 17).stores.certificate) (fuelContext (traceA19 17).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA19 18).stores ((traceA19 18).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((traceA19 18).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceA19 18).stores.certificate) (fuelContext (traceA19 18).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceA19 19).stores ((traceA19 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA19 19).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA19 19).stores.certificate) (fuelContext (traceA19 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceA19 20).stores ((traceA19 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA19 20).stage.apply regs) (FuelDispatchMachine.stores ((traceA19 20).stores.certificate) (fuelContext (traceA19 20).stores ctx)))
  · exact fuel_join_step caller .zero (traceA19 21).stores ((traceA19 21).stage.apply regs) ctx

theorem traceA20_steps (n : Nat) (bound : n < 25) :
    step caller ((traceA20 n).reached regs ctx) =
      some ((traceA20 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceA20 0).stores 6 [10, 15] rfl ((traceA20 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA20 1).stores ((traceA20 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((traceA20 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA20 1).stores.certificate) (fuelContext (traceA20 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA20 2).stores ((traceA20 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA20 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceA20 2).stores.certificate) (fuelContext (traceA20 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceA20 3).stores ((traceA20 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA20 3).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA20 3).stores.certificate) (fuelContext (traceA20 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceA20 4).stores ((traceA20 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((traceA20 4).stage.apply regs) (FuelDispatchMachine.stores ((traceA20 4).stores.certificate) (fuelContext (traceA20 4).stores ctx)))
  · exact fuel_join_step caller .positive (traceA20 5).stores ((traceA20 5).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceA20 6).stores ((traceA20 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA20 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA20 6).stores) (applyContext (traceA20 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceA20 7).stores ((traceA20 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA20 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA20 7).stores) (applyContext (traceA20 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceA20 8).stores ((traceA20 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA20 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA20 8).stores) (applyContext (traceA20 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceA20 9).stores ((traceA20 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceA20 9).stores)
        (applyRegisterEquiv.symm ((traceA20 9).stage.apply regs)) (applyContext (traceA20 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceA20 10).stores ((traceA20 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceA20 11).stores ((traceA20 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (traceA20 12).stores ((traceA20 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (traceA20 13).stores ((traceA20 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceA20 14).stores ((traceA20 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceA20 15).stores ((traceA20 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceA20 16).stores ((traceA20 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceA20 17).stores ((traceA20 17).stage.apply regs) ctx
  · exact inspect_step_cons caller (traceA20 18).stores 15 [] rfl ((traceA20 18).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA20 19).stores ((traceA20 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA20 19).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA20 19).stores.certificate) (fuelContext (traceA20 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceA20 20).stores ((traceA20 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((traceA20 20).stage.apply regs) (FuelDispatchMachine.stores ((traceA20 20).stores.certificate) (fuelContext (traceA20 20).stores ctx)))
  · exact fuel_join_step caller .positive (traceA20 21).stores ((traceA20 21).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceA20 22).stores ((traceA20 22).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA20 22).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA20 22).stores) (applyContext (traceA20 22).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (traceA20 23).stores ((traceA20 23).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (traceA20 23).stores)
        (applyRegisterEquiv.symm ((traceA20 23).stage.apply regs)) (applyContext (traceA20 23).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (traceA20 24).stores ((traceA20 24).stage.apply regs) ctx

theorem traceA21_steps (n : Nat) (bound : n < 24) :
    step caller ((traceA21 n).reached regs ctx) =
      some ((traceA21 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceA21 0).stores 6 [10] rfl ((traceA21 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceA21 1).stores ((traceA21 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceA21 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceA21 1).stores.certificate) (fuelContext (traceA21 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceA21 2).stores ((traceA21 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceA21 2).stage.apply regs) (FuelDispatchMachine.stores ((traceA21 2).stores.certificate) (fuelContext (traceA21 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceA21 3).stores ((traceA21 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceA21 4).stores ((traceA21 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA21 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA21 4).stores) (applyContext (traceA21 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceA21 5).stores ((traceA21 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA21 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA21 5).stores) (applyContext (traceA21 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceA21 6).stores ((traceA21 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceA21 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceA21 6).stores) (applyContext (traceA21 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceA21 7).stores ((traceA21 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceA21 7).stores)
        (applyRegisterEquiv.symm ((traceA21 7).stage.apply regs)) (applyContext (traceA21 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceA21 8).stores ((traceA21 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceA21 9).stores ((traceA21 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (traceA21 10).stores ((traceA21 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (traceA21 11).stores ((traceA21 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceA21 12).stores ((traceA21 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceA21 13).stores ((traceA21 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceA21 14).stores ((traceA21 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceA21 15).stores ((traceA21 15).stage.apply regs) ctx
  · exact inspect_step_nil caller (traceA21 16).stores rfl ((traceA21 16).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceA21 17).stores ((traceA21 17).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceA21 18).stores ((traceA21 18).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 15] [1, 0, 15] (equalityRegisterEquiv.symm ((traceA21 18).stage.apply regs)) (equalityContext (traceA21 18).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA21 19).stores ((traceA21 19).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 15] [0, 15] (equalityRegisterEquiv.symm ((traceA21 19).stage.apply regs)) (equalityContext (traceA21 19).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA21 20).stores ((traceA21 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [15] [15] (equalityRegisterEquiv.symm ((traceA21 20).stage.apply regs)) (equalityContext (traceA21 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA21 21).stores ((traceA21 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 15 [] [] (equalityRegisterEquiv.symm ((traceA21 21).stage.apply regs)) (equalityContext (traceA21 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceA21 22).stores ((traceA21 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceA21 22).stage.apply regs)) (equalityContext (traceA21 22).stores ctx))
  · exact equality_join_step caller .equal (traceA21 23).stores ((traceA21 23).stage.apply regs) ctx

theorem traceD01_steps (n : Nat) (bound : n < 4) :
    step caller ((traceD01 n).reached regs ctx) =
      some ((traceD01 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (traceD01 0).stores rfl ((traceD01 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceD01 1).stores ((traceD01 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceD01 2).stores ((traceD01 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceD01 2).stage.apply regs)) (equalityContext (traceD01 2).stores ctx))
  · exact equality_join_step caller .equal (traceD01 3).stores ((traceD01 3).stage.apply regs) ctx

theorem traceD02_steps (n : Nat) (bound : n < 9) :
    step caller ((traceD02 n).reached regs ctx) =
      some ((traceD02 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceD02 0).stores 15 [] rfl ((traceD02 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceD02 1).stores ((traceD02 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceD02 1).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((traceD02 1).stores.certificate) (fuelContext (traceD02 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceD02 2).stores ((traceD02 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceD02 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceD02 2).stores.certificate) (fuelContext (traceD02 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceD02 3).stores ((traceD02 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((traceD02 3).stage.apply regs) [] (FuelDispatchMachine.stores ((traceD02 3).stores.certificate) (fuelContext (traceD02 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceD02 4).stores ((traceD02 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, true, false] ((traceD02 4).stage.apply regs) (FuelDispatchMachine.stores ((traceD02 4).stores.certificate) (fuelContext (traceD02 4).stores ctx)))
  · exact fuel_join_step caller .positive (traceD02 5).stores ((traceD02 5).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceD02 6).stores ((traceD02 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [.right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD02 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD02 6).stores) (applyContext (traceD02 6).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (traceD02 7).stores ((traceD02 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (traceD02 7).stores)
        (applyRegisterEquiv.symm ((traceD02 7).stage.apply regs)) (applyContext (traceD02 7).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (traceD02 8).stores ((traceD02 8).stage.apply regs) ctx

theorem traceD03_steps (n : Nat) (bound : n < 6) :
    step caller ((traceD03 n).reached regs ctx) =
      some ((traceD03 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceD03 0).stores 15 [] rfl ((traceD03 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceD03 1).stores ((traceD03 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((traceD03 1).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((traceD03 1).stores.certificate) (fuelContext (traceD03 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceD03 2).stores ((traceD03 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceD03 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceD03 2).stores.certificate) (fuelContext (traceD03 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceD03 3).stores ((traceD03 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceD03 3).stage.apply regs) [] (FuelDispatchMachine.stores ((traceD03 3).stores.certificate) (fuelContext (traceD03 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceD03 4).stores ((traceD03 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((traceD03 4).stage.apply regs) (FuelDispatchMachine.stores ((traceD03 4).stores.certificate) (fuelContext (traceD03 4).stores ctx)))
  · exact fuel_join_step caller .zero (traceD03 5).stores ((traceD03 5).stage.apply regs) ctx

theorem traceD04_steps (n : Nat) (bound : n < 7) :
    step caller ((traceD04 n).reached regs ctx) =
      some ((traceD04 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceD04 0).stores 15 [] rfl ((traceD04 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceD04 1).stores ((traceD04 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceD04 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceD04 1).stores.certificate) (fuelContext (traceD04 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceD04 2).stores ((traceD04 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceD04 2).stage.apply regs) (FuelDispatchMachine.stores ((traceD04 2).stores.certificate) (fuelContext (traceD04 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceD04 3).stores ((traceD04 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceD04 4).stores ((traceD04 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [.right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD04 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD04 4).stores) (applyContext (traceD04 4).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (traceD04 5).stores ((traceD04 5).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (traceD04 5).stores)
        (applyRegisterEquiv.symm ((traceD04 5).stage.apply regs)) (applyContext (traceD04 5).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (traceD04 6).stores ((traceD04 6).stage.apply regs) ctx

theorem traceD05_steps (n : Nat) (bound : n < 13) :
    step caller ((traceD05 n).reached regs ctx) =
      some ((traceD05 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceD05 0).stores 6 [8, 15] rfl ((traceD05 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceD05 1).stores ((traceD05 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceD05 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceD05 1).stores.certificate) (fuelContext (traceD05 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceD05 2).stores ((traceD05 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceD05 2).stage.apply regs) (FuelDispatchMachine.stores ((traceD05 2).stores.certificate) (fuelContext (traceD05 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceD05 3).stores ((traceD05 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceD05 4).stores ((traceD05 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [8, 15] [.right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD05 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD05 4).stores) (applyContext (traceD05 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceD05 5).stores ((traceD05 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [15] [.right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD05 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD05 5).stores) (applyContext (traceD05 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceD05 6).stores ((traceD05 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_foreign (fun _ => .halt) .left 15 [] [.left, .right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD05 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD05 6).stores) (applyContext (traceD05 6).stores ctx)) (by decide) (by decide) (by decide))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (traceD05 7).stores ((traceD05 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_cons (fun _ => .halt) .left .left [15] [.right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD05 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD05 7).stores) (applyContext (traceD05 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (traceD05 8).stores ((traceD05 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_cons (fun _ => .halt) .left .right [8, 15] [.left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD05 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD05 8).stores) (applyContext (traceD05 8).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (traceD05 9).stores ((traceD05 9).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_cons (fun _ => .halt) .left .left [9, 8, 15] [] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD05 9).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD05 9).stores) (applyContext (traceD05 9).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (traceD05 10).stores ((traceD05 10).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_nil (fun _ => .halt) .left [8, 9, 8, 15] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD05 10).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD05 10).stores) (applyContext (traceD05 10).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (traceD05 11).stores ((traceD05 11).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (traceD05 11).stores)
        (applyRegisterEquiv.symm ((traceD05 11).stage.apply regs)) (applyContext (traceD05 11).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (traceD05 12).stores ((traceD05 12).stage.apply regs) ctx

theorem traceD06_steps (n : Nat) (bound : n < 30) :
    step caller ((traceD06 n).reached regs ctx) =
      some ((traceD06 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceD06 0).stores 6 [10] rfl ((traceD06 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceD06 1).stores ((traceD06 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceD06 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceD06 1).stores.certificate) (fuelContext (traceD06 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceD06 2).stores ((traceD06 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceD06 2).stage.apply regs) (FuelDispatchMachine.stores ((traceD06 2).stores.certificate) (fuelContext (traceD06 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceD06 3).stores ((traceD06 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceD06 4).stores ((traceD06 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD06 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD06 4).stores) (applyContext (traceD06 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceD06 5).stores ((traceD06 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD06 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD06 5).stores) (applyContext (traceD06 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceD06 6).stores ((traceD06 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD06 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD06 6).stores) (applyContext (traceD06 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceD06 7).stores ((traceD06 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD06 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD06 7).stores) (applyContext (traceD06 7).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceD06 8).stores ((traceD06 8).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceD06 8).stores)
        (applyRegisterEquiv.symm ((traceD06 8).stage.apply regs)) (applyContext (traceD06 8).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceD06 9).stores ((traceD06 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (traceD06 10).stores ((traceD06 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceD06 11).stores ((traceD06 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (traceD06 12).stores ((traceD06 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (traceD06 13).stores ((traceD06 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceD06 14).stores ((traceD06 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceD06 15).stores ((traceD06 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceD06 16).stores ((traceD06 16).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceD06 17).stores ((traceD06 17).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceD06 18).stores ((traceD06 18).stage.apply regs) ctx
  · exact inspect_step_nil caller (traceD06 19).stores rfl ((traceD06 19).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceD06 20).stores ((traceD06 20).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceD06 21).stores ((traceD06 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 1, 0, 0, 0, 0] [1, 1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((traceD06 21).stage.apply regs)) (equalityContext (traceD06 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceD06 22).stores ((traceD06 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0, 0] [1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((traceD06 22).stage.apply regs)) (equalityContext (traceD06 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceD06 23).stores ((traceD06 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0, 0] [0, 0, 0, 0] (equalityRegisterEquiv.symm ((traceD06 23).stage.apply regs)) (equalityContext (traceD06 23).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceD06 24).stores ((traceD06 24).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((traceD06 24).stage.apply regs)) (equalityContext (traceD06 24).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceD06 25).stores ((traceD06 25).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((traceD06 25).stage.apply regs)) (equalityContext (traceD06 25).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceD06 26).stores ((traceD06 26).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((traceD06 26).stage.apply regs)) (equalityContext (traceD06 26).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceD06 27).stores ((traceD06 27).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((traceD06 27).stage.apply regs)) (equalityContext (traceD06 27).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceD06 28).stores ((traceD06 28).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceD06 28).stage.apply regs)) (equalityContext (traceD06 28).stores ctx))
  · exact equality_join_step caller .equal (traceD06 29).stores ((traceD06 29).stage.apply regs) ctx

theorem traceD07_steps (n : Nat) (bound : n < 29) :
    step caller ((traceD07 n).reached regs ctx) =
      some ((traceD07 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceD07 0).stores 6 [10] rfl ((traceD07 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceD07 1).stores ((traceD07 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceD07 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceD07 1).stores.certificate) (fuelContext (traceD07 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceD07 2).stores ((traceD07 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceD07 2).stage.apply regs) (FuelDispatchMachine.stores ((traceD07 2).stores.certificate) (fuelContext (traceD07 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceD07 3).stores ((traceD07 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceD07 4).stores ((traceD07 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD07 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD07 4).stores) (applyContext (traceD07 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceD07 5).stores ((traceD07 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD07 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD07 5).stores) (applyContext (traceD07 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceD07 6).stores ((traceD07 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD07 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD07 6).stores) (applyContext (traceD07 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceD07 7).stores ((traceD07 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceD07 7).stores)
        (applyRegisterEquiv.symm ((traceD07 7).stage.apply regs)) (applyContext (traceD07 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceD07 8).stores ((traceD07 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (traceD07 9).stores ((traceD07 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceD07 10).stores ((traceD07 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (traceD07 11).stores ((traceD07 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (traceD07 12).stores ((traceD07 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceD07 13).stores ((traceD07 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceD07 14).stores ((traceD07 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceD07 15).stores ((traceD07 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceD07 16).stores ((traceD07 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceD07 17).stores ((traceD07 17).stage.apply regs) ctx
  · exact inspect_step_nil caller (traceD07 18).stores rfl ((traceD07 18).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceD07 19).stores ((traceD07 19).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceD07 20).stores ((traceD07 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 1, 0, 0, 0, 0] [1, 1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((traceD07 20).stage.apply regs)) (equalityContext (traceD07 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceD07 21).stores ((traceD07 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0, 0] [1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((traceD07 21).stage.apply regs)) (equalityContext (traceD07 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceD07 22).stores ((traceD07 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0, 0] [0, 0, 0, 0] (equalityRegisterEquiv.symm ((traceD07 22).stage.apply regs)) (equalityContext (traceD07 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceD07 23).stores ((traceD07 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((traceD07 23).stage.apply regs)) (equalityContext (traceD07 23).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceD07 24).stores ((traceD07 24).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((traceD07 24).stage.apply regs)) (equalityContext (traceD07 24).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceD07 25).stores ((traceD07 25).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((traceD07 25).stage.apply regs)) (equalityContext (traceD07 25).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceD07 26).stores ((traceD07 26).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((traceD07 26).stage.apply regs)) (equalityContext (traceD07 26).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceD07 27).stores ((traceD07 27).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceD07 27).stage.apply regs)) (equalityContext (traceD07 27).stores ctx))
  · exact equality_join_step caller .equal (traceD07 28).stores ((traceD07 28).stage.apply regs) ctx

theorem traceD08_steps (n : Nat) (bound : n < 7) :
    step caller ((traceD08 n).reached regs ctx) =
      some ((traceD08 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceD08 0).stores ((traceD08 0).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceD08 1).stores ((traceD08 1).stage.apply regs) ctx
  · exact inspect_step_nil caller (traceD08 2).stores rfl ((traceD08 2).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceD08 3).stores ((traceD08 3).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceD08 4).stores ((traceD08 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((traceD08 4).stage.apply regs)) (equalityContext (traceD08 4).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceD08 5).stores ((traceD08 5).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceD08 5).stage.apply regs)) (equalityContext (traceD08 5).stores ctx))
  · exact equality_join_step caller .equal (traceD08 6).stores ((traceD08 6).stage.apply regs) ctx

theorem traceD09_steps (n : Nat) (bound : n < 5) :
    step caller ((traceD09 n).reached regs ctx) =
      some ((traceD09 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact apply_join_step caller MoveApplyMachine.success (traceD09 0).stores ((traceD09 0).stage.apply regs) ctx
  · exact inspect_step_nil caller (traceD09 1).stores rfl ((traceD09 1).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceD09 2).stores ((traceD09 2).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceD09 3).stores ((traceD09 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceD09 3).stage.apply regs)) (equalityContext (traceD09 3).stores ctx))
  · exact equality_join_step caller .equal (traceD09 4).stores ((traceD09 4).stage.apply regs) ctx

theorem traceD10_steps (n : Nat) (bound : n < 4) :
    step caller ((traceD10 n).reached regs ctx) =
      some ((traceD10 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact fuel_join_step caller .positive (traceD10 0).stores ((traceD10 0).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceD10 1).stores ((traceD10 1).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_nil (fun _ => .halt) [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceD10 1).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceD10 1).stores) (applyContext (traceD10 1).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (traceD10 2).stores ((traceD10 2).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (traceD10 2).stores)
        (applyRegisterEquiv.symm ((traceD10 2).stage.apply regs)) (applyContext (traceD10 2).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (traceD10 3).stores ((traceD10 3).stage.apply regs) ctx

theorem traceD11_steps (n : Nat) (bound : n < 3) :
    step caller ((traceD11 n).reached regs ctx) =
      some ((traceD11 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact fuel_join_step caller .atEnd (traceD11 0).stores ((traceD11 0).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceD11 1).stores ((traceD11 1).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceD11 1).stage.apply regs)) (equalityContext (traceD11 1).stores ctx))
  · exact equality_join_step caller .equal (traceD11 2).stores ((traceD11 2).stage.apply regs) ctx

theorem traceD12_steps (n : Nat) (bound : n < 2) :
    step caller ((traceD12 n).reached regs ctx) =
      some ((traceD12 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact equality_step_of_step caller (fun _ => .halt) (traceD12 0).stores ((traceD12 0).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceD12 0).stage.apply regs)) (equalityContext (traceD12 0).stores ctx))
  · exact equality_join_step caller .equal (traceD12 1).stores ((traceD12 1).stage.apply regs) ctx

theorem traceD13_steps (n : Nat) (bound : n < 1) :
    step caller ((traceD13 n).reached regs ctx) =
      some ((traceD13 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact equality_join_step caller .equal (traceD13 0).stores ((traceD13 0).stage.apply regs) ctx

theorem traceR01_steps (n : Nat) (bound : n < 7) :
    step caller ((traceR01 n).reached regs ctx) =
      some ((traceR01 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceR01 0).stores ((traceR01 0).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceR01 0).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceR01 0).stores.certificate) (fuelContext (traceR01 0).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceR01 1).stores ((traceR01 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((traceR01 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR01 1).stores.certificate) (fuelContext (traceR01 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceR01 2).stores ((traceR01 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, true] ((traceR01 2).stage.apply regs) (FuelDispatchMachine.stores ((traceR01 2).stores.certificate) (fuelContext (traceR01 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceR01 3).stores ((traceR01 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceR01 4).stores ((traceR01 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR01 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR01 4).stores) (applyContext (traceR01 4).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (traceR01 5).stores ((traceR01 5).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (traceR01 5).stores)
        (applyRegisterEquiv.symm ((traceR01 5).stage.apply regs)) (applyContext (traceR01 5).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (traceR01 6).stores ((traceR01 6).stage.apply regs) ctx

theorem traceR02_steps (n : Nat) (bound : n < 4) :
    step caller ((traceR02 n).reached regs ctx) =
      some ((traceR02 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceR02 0).stores ((traceR02 0).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((traceR02 0).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceR02 0).stores.certificate) (fuelContext (traceR02 0).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceR02 1).stores ((traceR02 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, true] ((traceR02 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR02 1).stores.certificate) (fuelContext (traceR02 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceR02 2).stores ((traceR02 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false, true] ((traceR02 2).stage.apply regs) (FuelDispatchMachine.stores ((traceR02 2).stores.certificate) (fuelContext (traceR02 2).stores ctx)))
  · exact fuel_join_step caller .zero (traceR02 3).stores ((traceR02 3).stage.apply regs) ctx

theorem traceR03_steps (n : Nat) (bound : n < 17) :
    step caller ((traceR03 n).reached regs ctx) =
      some ((traceR03 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceR03 0).stores ((traceR03 0).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR03 0).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR03 0).stores) (applyContext (traceR03 0).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceR03 1).stores ((traceR03 1).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [15] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR03 1).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR03 1).stores) (applyContext (traceR03 1).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceR03 2).stores ((traceR03 2).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceR03 2).stores)
        (applyRegisterEquiv.symm ((traceR03 2).stage.apply regs)) (applyContext (traceR03 2).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceR03 3).stores ((traceR03 3).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (traceR03 4).stores ((traceR03 4).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceR03 5).stores ((traceR03 5).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (traceR03 6).stores ((traceR03 6).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (traceR03 7).stores ((traceR03 7).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceR03 8).stores ((traceR03 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceR03 9).stores ((traceR03 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceR03 10).stores ((traceR03 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceR03 11).stores ((traceR03 11).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceR03 12).stores ((traceR03 12).stage.apply regs) ctx
  · exact inspect_step_cons caller (traceR03 13).stores 15 [] rfl ((traceR03 13).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR03 14).stores ((traceR03 14).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((traceR03 14).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR03 14).stores.certificate) (fuelContext (traceR03 14).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceR03 15).stores ((traceR03 15).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceR03 15).stage.apply regs) (FuelDispatchMachine.stores ((traceR03 15).stores.certificate) (fuelContext (traceR03 15).stores ctx)))
  · exact fuel_join_step caller .zero (traceR03 16).stores ((traceR03 16).stage.apply regs) ctx

theorem traceR04_steps (n : Nat) (bound : n < 27) :
    step caller ((traceR04 n).reached regs ctx) =
      some ((traceR04 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR04 0).stores ((traceR04 0).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((traceR04 0).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceR04 0).stores.certificate) (fuelContext (traceR04 0).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR04 1).stores ((traceR04 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceR04 1).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((traceR04 1).stores.certificate) (fuelContext (traceR04 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceR04 2).stores ((traceR04 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceR04 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceR04 2).stores.certificate) (fuelContext (traceR04 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceR04 3).stores ((traceR04 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((traceR04 3).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR04 3).stores.certificate) (fuelContext (traceR04 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceR04 4).stores ((traceR04 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, true, false] ((traceR04 4).stage.apply regs) (FuelDispatchMachine.stores ((traceR04 4).stores.certificate) (fuelContext (traceR04 4).stores ctx)))
  · exact fuel_join_step caller .positive (traceR04 5).stores ((traceR04 5).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceR04 6).stores ((traceR04 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR04 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR04 6).stores) (applyContext (traceR04 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceR04 7).stores ((traceR04 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR04 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR04 7).stores) (applyContext (traceR04 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceR04 8).stores ((traceR04 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR04 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR04 8).stores) (applyContext (traceR04 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceR04 9).stores ((traceR04 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceR04 9).stores)
        (applyRegisterEquiv.symm ((traceR04 9).stage.apply regs)) (applyContext (traceR04 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceR04 10).stores ((traceR04 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceR04 11).stores ((traceR04 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (traceR04 12).stores ((traceR04 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (traceR04 13).stores ((traceR04 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceR04 14).stores ((traceR04 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceR04 15).stores ((traceR04 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceR04 16).stores ((traceR04 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceR04 17).stores ((traceR04 17).stage.apply regs) ctx
  · exact inspect_step_nil caller (traceR04 18).stores rfl ((traceR04 18).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceR04 19).stores ((traceR04 19).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceR04 20).stores ((traceR04 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0] [1, 0, 0, 0] (equalityRegisterEquiv.symm ((traceR04 20).stage.apply regs)) (equalityContext (traceR04 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceR04 21).stores ((traceR04 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((traceR04 21).stage.apply regs)) (equalityContext (traceR04 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceR04 22).stores ((traceR04 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((traceR04 22).stage.apply regs)) (equalityContext (traceR04 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceR04 23).stores ((traceR04 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((traceR04 23).stage.apply regs)) (equalityContext (traceR04 23).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceR04 24).stores ((traceR04 24).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((traceR04 24).stage.apply regs)) (equalityContext (traceR04 24).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceR04 25).stores ((traceR04 25).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceR04 25).stage.apply regs)) (equalityContext (traceR04 25).stores ctx))
  · exact equality_join_step caller .equal (traceR04 26).stores ((traceR04 26).stage.apply regs) ctx

theorem traceR05_steps (n : Nat) (bound : n < 6) :
    step caller ((traceR05 n).reached regs ctx) =
      some ((traceR05 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (traceR05 0).stores rfl ((traceR05 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceR05 1).stores ((traceR05 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceR05 2).stores ((traceR05 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0] [0, 15, 2] (equalityRegisterEquiv.symm ((traceR05 2).stage.apply regs)) (equalityContext (traceR05 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceR05 3).stores ((traceR05 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [15, 2] (equalityRegisterEquiv.symm ((traceR05 3).stage.apply regs)) (equalityContext (traceR05 3).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceR05 4).stores ((traceR05 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_cons (fun _ => .halt) 15 [2] (equalityRegisterEquiv.symm ((traceR05 4).stage.apply regs)) (equalityContext (traceR05 4).stores ctx))
  · exact equality_join_step caller .different (traceR05 5).stores ((traceR05 5).stage.apply regs) ctx

theorem traceR06_steps (n : Nat) (bound : n < 6) :
    step caller ((traceR06 n).reached regs ctx) =
      some ((traceR06 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (traceR06 0).stores rfl ((traceR06 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceR06 1).stores ((traceR06 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceR06 2).stores ((traceR06 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 15, 2] [0] (equalityRegisterEquiv.symm ((traceR06 2).stage.apply regs)) (equalityContext (traceR06 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceR06 3).stores ((traceR06 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [15, 2] [] (equalityRegisterEquiv.symm ((traceR06 3).stage.apply regs)) (equalityContext (traceR06 3).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceR06 4).stores ((traceR06 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_cons_nil (fun _ => .halt) 15 [2] (equalityRegisterEquiv.symm ((traceR06 4).stage.apply regs)) (equalityContext (traceR06 4).stores ctx))
  · exact equality_join_step caller .different (traceR06 5).stores ((traceR06 5).stage.apply regs) ctx

theorem traceR07_steps (n : Nat) (bound : n < 22) :
    step caller ((traceR07 n).reached regs ctx) =
      some ((traceR07 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceR07 0).stores 6 [10, 15] rfl ((traceR07 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR07 1).stores ((traceR07 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceR07 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR07 1).stores.certificate) (fuelContext (traceR07 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceR07 2).stores ((traceR07 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceR07 2).stage.apply regs) (FuelDispatchMachine.stores ((traceR07 2).stores.certificate) (fuelContext (traceR07 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceR07 3).stores ((traceR07 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceR07 4).stores ((traceR07 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR07 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR07 4).stores) (applyContext (traceR07 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceR07 5).stores ((traceR07 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR07 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR07 5).stores) (applyContext (traceR07 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceR07 6).stores ((traceR07 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR07 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR07 6).stores) (applyContext (traceR07 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceR07 7).stores ((traceR07 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceR07 7).stores)
        (applyRegisterEquiv.symm ((traceR07 7).stage.apply regs)) (applyContext (traceR07 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceR07 8).stores ((traceR07 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceR07 9).stores ((traceR07 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (traceR07 10).stores ((traceR07 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (traceR07 11).stores ((traceR07 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceR07 12).stores ((traceR07 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceR07 13).stores ((traceR07 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceR07 14).stores ((traceR07 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceR07 15).stores ((traceR07 15).stage.apply regs) ctx
  · exact inspect_step_cons caller (traceR07 16).stores 15 [] rfl ((traceR07 16).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR07 17).stores ((traceR07 17).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceR07 17).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR07 17).stores.certificate) (fuelContext (traceR07 17).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR07 18).stores ((traceR07 18).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((traceR07 18).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceR07 18).stores.certificate) (fuelContext (traceR07 18).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceR07 19).stores ((traceR07 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceR07 19).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR07 19).stores.certificate) (fuelContext (traceR07 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceR07 20).stores ((traceR07 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceR07 20).stage.apply regs) (FuelDispatchMachine.stores ((traceR07 20).stores.certificate) (fuelContext (traceR07 20).stores ctx)))
  · exact fuel_join_step caller .zero (traceR07 21).stores ((traceR07 21).stage.apply regs) ctx

theorem traceR08_steps (n : Nat) (bound : n < 41) :
    step caller ((traceR08 n).reached regs ctx) =
      some ((traceR08 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceR08 0).stores 6 [10, 7, 10, 15] rfl ((traceR08 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR08 1).stores ((traceR08 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((traceR08 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR08 1).stores.certificate) (fuelContext (traceR08 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR08 2).stores ((traceR08 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceR08 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceR08 2).stores.certificate) (fuelContext (traceR08 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceR08 3).stores ((traceR08 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceR08 3).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR08 3).stores.certificate) (fuelContext (traceR08 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceR08 4).stores ((traceR08 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((traceR08 4).stage.apply regs) (FuelDispatchMachine.stores ((traceR08 4).stores.certificate) (fuelContext (traceR08 4).stores ctx)))
  · exact fuel_join_step caller .positive (traceR08 5).stores ((traceR08 5).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceR08 6).stores ((traceR08 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 7, 10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR08 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR08 6).stores) (applyContext (traceR08 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceR08 7).stores ((traceR08 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [7, 10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR08 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR08 7).stores) (applyContext (traceR08 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceR08 8).stores ((traceR08 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [7, 10, 15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR08 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR08 8).stores) (applyContext (traceR08 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceR08 9).stores ((traceR08 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceR08 9).stores)
        (applyRegisterEquiv.symm ((traceR08 9).stage.apply regs)) (applyContext (traceR08 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceR08 10).stores ((traceR08 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceR08 11).stores ((traceR08 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (traceR08 12).stores ((traceR08 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (traceR08 13).stores ((traceR08 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceR08 14).stores ((traceR08 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceR08 15).stores ((traceR08 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceR08 16).stores ((traceR08 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceR08 17).stores ((traceR08 17).stage.apply regs) ctx
  · exact inspect_step_cons caller (traceR08 18).stores 7 [10, 15] rfl ((traceR08 18).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR08 19).stores ((traceR08 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceR08 19).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR08 19).stores.certificate) (fuelContext (traceR08 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceR08 20).stores ((traceR08 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((traceR08 20).stage.apply regs) (FuelDispatchMachine.stores ((traceR08 20).stores.certificate) (fuelContext (traceR08 20).stores ctx)))
  · exact fuel_join_step caller .positive (traceR08 21).stores ((traceR08 21).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceR08 22).stores ((traceR08 22).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .right [10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR08 22).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR08 22).stores) (applyContext (traceR08 22).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .right) (traceR08 23).stores ((traceR08 23).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .right [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR08 23).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR08 23).stores) (applyContext (traceR08 23).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .right) (traceR08 24).stores ((traceR08 24).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .right [15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR08 24).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR08 24).stores) (applyContext (traceR08 24).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .right)) (traceR08 25).stores ((traceR08 25).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .right) (applyData (traceR08 25).stores)
        (applyRegisterEquiv.symm ((traceR08 25).stage.apply regs)) (applyContext (traceR08 25).stores ctx))
  · exact apply_position_advance_step caller (.seek .right) (traceR08 26).stores ((traceR08 26).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .right) (traceR08 27).stores ((traceR08 27).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .right) (traceR08 28).stores ((traceR08 28).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (traceR08 29).stores ((traceR08 29).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (traceR08 30).stores ((traceR08 30).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceR08 31).stores ((traceR08 31).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceR08 32).stores ((traceR08 32).stage.apply regs) ctx
  · exact inspect_step_cons caller (traceR08 33).stores 15 [] rfl ((traceR08 33).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR08 34).stores ((traceR08 34).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceR08 34).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR08 34).stores.certificate) (fuelContext (traceR08 34).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR08 35).stores ((traceR08 35).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceR08 35).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceR08 35).stores.certificate) (fuelContext (traceR08 35).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR08 36).stores ((traceR08 36).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((traceR08 36).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((traceR08 36).stores.certificate) (fuelContext (traceR08 36).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceR08 37).stores ((traceR08 37).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceR08 37).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceR08 37).stores.certificate) (fuelContext (traceR08 37).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceR08 38).stores ((traceR08 38).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceR08 38).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR08 38).stores.certificate) (fuelContext (traceR08 38).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceR08 39).stores ((traceR08 39).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((traceR08 39).stage.apply regs) (FuelDispatchMachine.stores ((traceR08 39).stores.certificate) (fuelContext (traceR08 39).stores ctx)))
  · exact fuel_join_step caller .zero (traceR08 40).stores ((traceR08 40).stage.apply regs) ctx

theorem traceR09_steps (n : Nat) (bound : n < 40) :
    step caller ((traceR09 n).reached regs ctx) =
      some ((traceR09 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceR09 0).stores 6 [10, 7, 10, 15] rfl ((traceR09 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR09 1).stores ((traceR09 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((traceR09 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR09 1).stores.certificate) (fuelContext (traceR09 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceR09 2).stores ((traceR09 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, true] ((traceR09 2).stage.apply regs) (FuelDispatchMachine.stores ((traceR09 2).stores.certificate) (fuelContext (traceR09 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceR09 3).stores ((traceR09 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceR09 4).stores ((traceR09 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 7, 10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR09 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR09 4).stores) (applyContext (traceR09 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceR09 5).stores ((traceR09 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [7, 10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR09 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR09 5).stores) (applyContext (traceR09 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceR09 6).stores ((traceR09 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [7, 10, 15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR09 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR09 6).stores) (applyContext (traceR09 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceR09 7).stores ((traceR09 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceR09 7).stores)
        (applyRegisterEquiv.symm ((traceR09 7).stage.apply regs)) (applyContext (traceR09 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceR09 8).stores ((traceR09 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceR09 9).stores ((traceR09 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (traceR09 10).stores ((traceR09 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (traceR09 11).stores ((traceR09 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceR09 12).stores ((traceR09 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceR09 13).stores ((traceR09 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceR09 14).stores ((traceR09 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceR09 15).stores ((traceR09 15).stage.apply regs) ctx
  · exact inspect_step_cons caller (traceR09 16).stores 7 [10, 15] rfl ((traceR09 16).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR09 17).stores ((traceR09 17).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((traceR09 17).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR09 17).stores.certificate) (fuelContext (traceR09 17).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR09 18).stores ((traceR09 18).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceR09 18).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceR09 18).stores.certificate) (fuelContext (traceR09 18).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceR09 19).stores ((traceR09 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceR09 19).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR09 19).stores.certificate) (fuelContext (traceR09 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceR09 20).stores ((traceR09 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((traceR09 20).stage.apply regs) (FuelDispatchMachine.stores ((traceR09 20).stores.certificate) (fuelContext (traceR09 20).stores ctx)))
  · exact fuel_join_step caller .positive (traceR09 21).stores ((traceR09 21).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceR09 22).stores ((traceR09 22).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .right [10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR09 22).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR09 22).stores) (applyContext (traceR09 22).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .right) (traceR09 23).stores ((traceR09 23).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .right [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR09 23).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR09 23).stores) (applyContext (traceR09 23).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .right) (traceR09 24).stores ((traceR09 24).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .right [15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR09 24).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR09 24).stores) (applyContext (traceR09 24).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .right)) (traceR09 25).stores ((traceR09 25).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .right) (applyData (traceR09 25).stores)
        (applyRegisterEquiv.symm ((traceR09 25).stage.apply regs)) (applyContext (traceR09 25).stores ctx))
  · exact apply_position_advance_step caller (.seek .right) (traceR09 26).stores ((traceR09 26).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .right) (traceR09 27).stores ((traceR09 27).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .right) (traceR09 28).stores ((traceR09 28).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (traceR09 29).stores ((traceR09 29).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (traceR09 30).stores ((traceR09 30).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceR09 31).stores ((traceR09 31).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceR09 32).stores ((traceR09 32).stage.apply regs) ctx
  · exact inspect_step_cons caller (traceR09 33).stores 15 [] rfl ((traceR09 33).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR09 34).stores ((traceR09 34).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceR09 34).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR09 34).stores.certificate) (fuelContext (traceR09 34).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceR09 35).stores ((traceR09 35).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((traceR09 35).stage.apply regs) (FuelDispatchMachine.stores ((traceR09 35).stores.certificate) (fuelContext (traceR09 35).stores ctx)))
  · exact fuel_join_step caller .positive (traceR09 36).stores ((traceR09 36).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceR09 37).stores ((traceR09 37).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR09 37).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR09 37).stores) (applyContext (traceR09 37).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (traceR09 38).stores ((traceR09 38).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (traceR09 38).stores)
        (applyRegisterEquiv.symm ((traceR09 38).stage.apply regs)) (applyContext (traceR09 38).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (traceR09 39).stores ((traceR09 39).stage.apply regs) ctx

theorem traceR10_steps (n : Nat) (bound : n < 20) :
    step caller ((traceR10 n).reached regs ctx) =
      some ((traceR10 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceR10 0).stores 6 [10] rfl ((traceR10 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceR10 1).stores ((traceR10 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceR10 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceR10 1).stores.certificate) (fuelContext (traceR10 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceR10 2).stores ((traceR10 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceR10 2).stage.apply regs) (FuelDispatchMachine.stores ((traceR10 2).stores.certificate) (fuelContext (traceR10 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceR10 3).stores ((traceR10 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceR10 4).stores ((traceR10 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [.right] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR10 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR10 4).stores) (applyContext (traceR10 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceR10 5).stores ((traceR10 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.right] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR10 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR10 5).stores) (applyContext (traceR10 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceR10 6).stores ((traceR10 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .right [] [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR10 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR10 6).stores) (applyContext (traceR10 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceR10 7).stores ((traceR10 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.right, .left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceR10 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceR10 7).stores) (applyContext (traceR10 7).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceR10 8).stores ((traceR10 8).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceR10 8).stores)
        (applyRegisterEquiv.symm ((traceR10 8).stage.apply regs)) (applyContext (traceR10 8).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceR10 9).stores ((traceR10 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanPrefix .left) (traceR10 10).stores ((traceR10 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (traceR10 11).stores ((traceR10 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (traceR10 12).stores ((traceR10 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceR10 13).stores ((traceR10 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (traceR10 14).stores ((traceR10 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (traceR10 15).stores ((traceR10 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (traceR10 16).stores ((traceR10 16).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (traceR10 17).stores ((traceR10 17).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (traceR10 18).stores ((traceR10 18).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (traceR10 19).stores ((traceR10 19).stage.apply regs) ctx

end LiteralTraceEdges


end Examples.RotationCertificateStreamMachine
