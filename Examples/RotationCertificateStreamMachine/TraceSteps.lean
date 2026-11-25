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

theorem trace_a01_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_a01 n).reached regs ctx) =
      some ((trace_a01 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_a01 0).stores rfl ((trace_a01 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a01 1).stores ((trace_a01 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a01 2).stores ((trace_a01 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a01 2).stage.apply regs)) (equalityContext (trace_a01 2).stores ctx))
  · exact equality_join_step caller .equal (trace_a01 3).stores ((trace_a01 3).stage.apply regs) ctx

theorem trace_a02_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_a02 n).reached regs ctx) =
      some ((trace_a02 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a02 0).stores 15 [] rfl ((trace_a02 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a02 1).stores ((trace_a02 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_a02 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a02 1).stores.certificate) (fuelContext (trace_a02 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_a02 2).stores ((trace_a02 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a02 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a02 2).stores.certificate) (fuelContext (trace_a02 2).stores ctx)))
  · exact fuel_join_step caller .zero (trace_a02 3).stores ((trace_a02 3).stage.apply regs) ctx

theorem trace_a03_steps (n : Nat) (bound : n < 5) :
    step caller ((trace_a03 n).reached regs ctx) =
      some ((trace_a03 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_a03 0).stores rfl ((trace_a03 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a03 1).stores ((trace_a03 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a03 2).stores ((trace_a03 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_a03 2).stage.apply regs)) (equalityContext (trace_a03 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a03 3).stores ((trace_a03 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a03 3).stage.apply regs)) (equalityContext (trace_a03 3).stores ctx))
  · exact equality_join_step caller .equal (trace_a03 4).stores ((trace_a03 4).stage.apply regs) ctx

theorem trace_a04_steps (n : Nat) (bound : n < 7) :
    step caller ((trace_a04 n).reached regs ctx) =
      some ((trace_a04 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_a04 0).stores rfl ((trace_a04 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a04 1).stores ((trace_a04 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a04 2).stores ((trace_a04 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_a04 2).stage.apply regs)) (equalityContext (trace_a04 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a04 3).stores ((trace_a04 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_a04 3).stage.apply regs)) (equalityContext (trace_a04 3).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a04 4).stores ((trace_a04 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_a04 4).stage.apply regs)) (equalityContext (trace_a04 4).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a04 5).stores ((trace_a04 5).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a04 5).stage.apply regs)) (equalityContext (trace_a04 5).stores ctx))
  · exact equality_join_step caller .equal (trace_a04 6).stores ((trace_a04 6).stage.apply regs) ctx

theorem trace_a05_steps (n : Nat) (bound : n < 9) :
    step caller ((trace_a05 n).reached regs ctx) =
      some ((trace_a05 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_a05 0).stores rfl ((trace_a05 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a05 1).stores ((trace_a05 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a05 2).stores ((trace_a05 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 1, 0, 0] [0, 1, 0, 0] (equalityRegisterEquiv.symm ((trace_a05 2).stage.apply regs)) (equalityContext (trace_a05 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a05 3).stores ((trace_a05 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [1, 0, 0] [1, 0, 0] (equalityRegisterEquiv.symm ((trace_a05 3).stage.apply regs)) (equalityContext (trace_a05 3).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a05 4).stores ((trace_a05 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_a05 4).stage.apply regs)) (equalityContext (trace_a05 4).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a05 5).stores ((trace_a05 5).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_a05 5).stage.apply regs)) (equalityContext (trace_a05 5).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a05 6).stores ((trace_a05 6).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_a05 6).stage.apply regs)) (equalityContext (trace_a05 6).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a05 7).stores ((trace_a05 7).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a05 7).stage.apply regs)) (equalityContext (trace_a05 7).stores ctx))
  · exact equality_join_step caller .equal (trace_a05 8).stores ((trace_a05 8).stage.apply regs) ctx

theorem trace_a06_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_a06 n).reached regs ctx) =
      some ((trace_a06 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_a06 0).stores rfl ((trace_a06 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a06 1).stores ((trace_a06 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a06 2).stores ((trace_a06 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_different (fun _ => .halt) 1 0 [0, 0] [] (equalityRegisterEquiv.symm ((trace_a06 2).stage.apply regs)) (equalityContext (trace_a06 2).stores ctx) (by decide))
  · exact equality_join_step caller .different (trace_a06 3).stores ((trace_a06 3).stage.apply regs) ctx

theorem trace_a07_steps (n : Nat) (bound : n < 5) :
    step caller ((trace_a07 n).reached regs ctx) =
      some ((trace_a07 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_a07 0).stores rfl ((trace_a07 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a07 1).stores ((trace_a07 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a07 2).stores ((trace_a07 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 15 [] [] (equalityRegisterEquiv.symm ((trace_a07 2).stage.apply regs)) (equalityContext (trace_a07 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a07 3).stores ((trace_a07 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a07 3).stage.apply regs)) (equalityContext (trace_a07 3).stores ctx))
  · exact equality_join_step caller .equal (trace_a07 4).stores ((trace_a07 4).stage.apply regs) ctx

theorem trace_a08_steps (n : Nat) (bound : n < 6) :
    step caller ((trace_a08 n).reached regs ctx) =
      some ((trace_a08 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_a08 0).stores rfl ((trace_a08 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a08 1).stores ((trace_a08 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a08 2).stores ((trace_a08 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 15, 2] [0, 3, 11] (equalityRegisterEquiv.symm ((trace_a08 2).stage.apply regs)) (equalityContext (trace_a08 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a08 3).stores ((trace_a08 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [15, 2] [3, 11] (equalityRegisterEquiv.symm ((trace_a08 3).stage.apply regs)) (equalityContext (trace_a08 3).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a08 4).stores ((trace_a08 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_different (fun _ => .halt) 15 3 [2] [11] (equalityRegisterEquiv.symm ((trace_a08 4).stage.apply regs)) (equalityContext (trace_a08 4).stores ctx) (by decide))
  · exact equality_join_step caller .different (trace_a08 5).stores ((trace_a08 5).stage.apply regs) ctx

theorem trace_a09_steps (n : Nat) (bound : n < 8) :
    step caller ((trace_a09 n).reached regs ctx) =
      some ((trace_a09 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a09 0).stores 6 [10] rfl ((trace_a09 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a09 1).stores ((trace_a09 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a09 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a09 1).stores.certificate) (fuelContext (trace_a09 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a09 2).stores ((trace_a09 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a09 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_a09 2).stores.certificate) (fuelContext (trace_a09 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a09 3).stores ((trace_a09 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_a09 3).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((trace_a09 3).stores.certificate) (fuelContext (trace_a09 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_a09 4).stores ((trace_a09 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a09 4).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_a09 4).stores.certificate) (fuelContext (trace_a09 4).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_a09 5).stores ((trace_a09 5).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a09 5).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a09 5).stores.certificate) (fuelContext (trace_a09 5).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_a09 6).stores ((trace_a09 6).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_a09 6).stage.apply regs) (FuelDispatchMachine.stores ((trace_a09 6).stores.certificate) (fuelContext (trace_a09 6).stores ctx)))
  · exact fuel_join_step caller .zero (trace_a09 7).stores ((trace_a09 7).stage.apply regs) ctx

theorem trace_a10_steps (n : Nat) (bound : n < 7) :
    step caller ((trace_a10 n).reached regs ctx) =
      some ((trace_a10 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a10 0).stores 15 [] rfl ((trace_a10 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a10 1).stores ((trace_a10 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a10 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a10 1).stores.certificate) (fuelContext (trace_a10 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a10 2).stores ((trace_a10 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a10 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a10 2).stores.certificate) (fuelContext (trace_a10 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a10 3).stores ((trace_a10 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a10 4).stores ((trace_a10 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a10 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a10 4).stores) (applyContext (trace_a10 4).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_a10 5).stores ((trace_a10 5).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_a10 5).stores)
        (applyRegisterEquiv.symm ((trace_a10 5).stage.apply regs)) (applyContext (trace_a10 5).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_a10 6).stores ((trace_a10 6).stage.apply regs) ctx

theorem trace_a11_steps (n : Nat) (bound : n < 11) :
    step caller ((trace_a11 n).reached regs ctx) =
      some ((trace_a11 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a11 0).stores 6 [8, 15] rfl ((trace_a11 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a11 1).stores ((trace_a11 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a11 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a11 1).stores.certificate) (fuelContext (trace_a11 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a11 2).stores ((trace_a11 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a11 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a11 2).stores.certificate) (fuelContext (trace_a11 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a11 3).stores ((trace_a11 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a11 4).stores ((trace_a11 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [8, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a11 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a11 4).stores) (applyContext (trace_a11 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a11 5).stores ((trace_a11 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a11 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a11 5).stores) (applyContext (trace_a11 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a11 6).stores ((trace_a11 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_foreign (fun _ => .halt) .left 15 [] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a11 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a11 6).stores) (applyContext (trace_a11 6).stores ctx)) (by decide) (by decide) (by decide))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (trace_a11 7).stores ((trace_a11 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_cons (fun _ => .halt) .left .left [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a11 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a11 7).stores) (applyContext (trace_a11 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (trace_a11 8).stores ((trace_a11 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_nil (fun _ => .halt) .left [8, 15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a11 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a11 8).stores) (applyContext (trace_a11 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_a11 9).stores ((trace_a11 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_a11 9).stores)
        (applyRegisterEquiv.symm ((trace_a11 9).stage.apply regs)) (applyContext (trace_a11 9).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_a11 10).stores ((trace_a11 10).stage.apply regs) ctx

theorem trace_a12_steps (n : Nat) (bound : n < 25) :
    step caller ((trace_a12 n).reached regs ctx) =
      some ((trace_a12 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a12 0).stores 6 [10] rfl ((trace_a12 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a12 1).stores ((trace_a12 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a12 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a12 1).stores.certificate) (fuelContext (trace_a12 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a12 2).stores ((trace_a12 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a12 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a12 2).stores.certificate) (fuelContext (trace_a12 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a12 3).stores ((trace_a12 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a12 4).stores ((trace_a12 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a12 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a12 4).stores) (applyContext (trace_a12 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a12 5).stores ((trace_a12 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a12 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a12 5).stores) (applyContext (trace_a12 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a12 6).stores ((trace_a12 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a12 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a12 6).stores) (applyContext (trace_a12 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a12 7).stores ((trace_a12 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a12 7).stores)
        (applyRegisterEquiv.symm ((trace_a12 7).stage.apply regs)) (applyContext (trace_a12 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a12 8).stores ((trace_a12 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_a12 9).stores ((trace_a12 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_a12 10).stores ((trace_a12 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_a12 11).stores ((trace_a12 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a12 12).stores ((trace_a12 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a12 13).stores ((trace_a12 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a12 14).stores ((trace_a12 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a12 15).stores ((trace_a12 15).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_a12 16).stores rfl ((trace_a12 16).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a12 17).stores ((trace_a12 17).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a12 18).stores ((trace_a12 18).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0] [1, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_a12 18).stage.apply regs)) (equalityContext (trace_a12 18).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a12 19).stores ((trace_a12 19).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((trace_a12 19).stage.apply regs)) (equalityContext (trace_a12 19).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a12 20).stores ((trace_a12 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_a12 20).stage.apply regs)) (equalityContext (trace_a12 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a12 21).stores ((trace_a12 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_a12 21).stage.apply regs)) (equalityContext (trace_a12 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a12 22).stores ((trace_a12 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_a12 22).stage.apply regs)) (equalityContext (trace_a12 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a12 23).stores ((trace_a12 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a12 23).stage.apply regs)) (equalityContext (trace_a12 23).stores ctx))
  · exact equality_join_step caller .equal (trace_a12 24).stores ((trace_a12 24).stage.apply regs) ctx

theorem trace_a13_steps (n : Nat) (bound : n < 24) :
    step caller ((trace_a13 n).reached regs ctx) =
      some ((trace_a13 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a13 0).stores 7 [10] rfl ((trace_a13 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a13 1).stores ((trace_a13 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a13 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a13 1).stores.certificate) (fuelContext (trace_a13 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a13 2).stores ((trace_a13 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a13 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a13 2).stores.certificate) (fuelContext (trace_a13 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a13 3).stores ((trace_a13 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a13 4).stores ((trace_a13 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .right [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a13 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a13 4).stores) (applyContext (trace_a13 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .right) (trace_a13 5).stores ((trace_a13 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .right [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a13 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a13 5).stores) (applyContext (trace_a13 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .right) (trace_a13 6).stores ((trace_a13 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .right [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a13 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a13 6).stores) (applyContext (trace_a13 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .right)) (trace_a13 7).stores ((trace_a13 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .right) (applyData (trace_a13 7).stores)
        (applyRegisterEquiv.symm ((trace_a13 7).stage.apply regs)) (applyContext (trace_a13 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .right) (trace_a13 8).stores ((trace_a13 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .right) (trace_a13 9).stores ((trace_a13 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .right) (trace_a13 10).stores ((trace_a13 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (trace_a13 11).stores ((trace_a13 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (trace_a13 12).stores ((trace_a13 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a13 13).stores ((trace_a13 13).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a13 14).stores ((trace_a13 14).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_a13 15).stores rfl ((trace_a13 15).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a13 16).stores ((trace_a13 16).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a13 17).stores ((trace_a13 17).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 1, 0, 0] [0, 1, 0, 0] (equalityRegisterEquiv.symm ((trace_a13 17).stage.apply regs)) (equalityContext (trace_a13 17).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a13 18).stores ((trace_a13 18).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [1, 0, 0] [1, 0, 0] (equalityRegisterEquiv.symm ((trace_a13 18).stage.apply regs)) (equalityContext (trace_a13 18).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a13 19).stores ((trace_a13 19).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_a13 19).stage.apply regs)) (equalityContext (trace_a13 19).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a13 20).stores ((trace_a13 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_a13 20).stage.apply regs)) (equalityContext (trace_a13 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a13 21).stores ((trace_a13 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_a13 21).stage.apply regs)) (equalityContext (trace_a13 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a13 22).stores ((trace_a13 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a13 22).stage.apply regs)) (equalityContext (trace_a13 22).stores ctx))
  · exact equality_join_step caller .equal (trace_a13 23).stores ((trace_a13 23).stage.apply regs) ctx

theorem trace_a14_steps (n : Nat) (bound : n < 13) :
    step caller ((trace_a14 n).reached regs ctx) =
      some ((trace_a14 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a14 0).stores 6 [10] rfl ((trace_a14 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a14 1).stores ((trace_a14 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a14 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a14 1).stores.certificate) (fuelContext (trace_a14 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a14 2).stores ((trace_a14 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a14 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a14 2).stores.certificate) (fuelContext (trace_a14 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a14 3).stores ((trace_a14 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a14 4).stores ((trace_a14 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a14 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a14 4).stores) (applyContext (trace_a14 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a14 5).stores ((trace_a14 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a14 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a14 5).stores) (applyContext (trace_a14 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a14 6).stores ((trace_a14 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a14 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a14 6).stores) (applyContext (trace_a14 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a14 7).stores ((trace_a14 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a14 7).stores)
        (applyRegisterEquiv.symm ((trace_a14 7).stage.apply regs)) (applyContext (trace_a14 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a14 8).stores ((trace_a14 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_a14 9).stores ((trace_a14 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (trace_a14 10).stores ((trace_a14 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_a14 11).stores ((trace_a14 11).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (trace_a14 12).stores ((trace_a14 12).stage.apply regs) ctx

theorem trace_a15_steps (n : Nat) (bound : n < 16) :
    step caller ((trace_a15 n).reached regs ctx) =
      some ((trace_a15 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a15 0).stores 6 [8, 8, 10] rfl ((trace_a15 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a15 1).stores ((trace_a15 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a15 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a15 1).stores.certificate) (fuelContext (trace_a15 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a15 2).stores ((trace_a15 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a15 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a15 2).stores.certificate) (fuelContext (trace_a15 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a15 3).stores ((trace_a15 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a15 4).stores ((trace_a15 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [8, 8, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a15 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a15 4).stores) (applyContext (trace_a15 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a15 5).stores ((trace_a15 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [8, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a15 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a15 5).stores) (applyContext (trace_a15 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a15 6).stores ((trace_a15 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [10] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a15 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a15 6).stores) (applyContext (trace_a15 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a15 7).stores ((trace_a15 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.left, .left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a15 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a15 7).stores) (applyContext (trace_a15 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a15 8).stores ((trace_a15 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a15 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a15 8).stores) (applyContext (trace_a15 8).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a15 9).stores ((trace_a15 9).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a15 9).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a15 9).stores) (applyContext (trace_a15 9).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a15 10).stores ((trace_a15 10).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left, .left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a15 10).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a15 10).stores) (applyContext (trace_a15 10).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a15 11).stores ((trace_a15 11).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a15 11).stores)
        (applyRegisterEquiv.symm ((trace_a15 11).stage.apply regs)) (applyContext (trace_a15 11).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a15 12).stores ((trace_a15 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (trace_a15 13).stores ((trace_a15 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_a15 14).stores ((trace_a15 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (trace_a15 15).stores ((trace_a15 15).stage.apply regs) ctx

theorem trace_a16_steps (n : Nat) (bound : n < 31) :
    step caller ((trace_a16 n).reached regs ctx) =
      some ((trace_a16 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a16 0).stores 6 [8, 10] rfl ((trace_a16 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a16 1).stores ((trace_a16 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a16 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a16 1).stores.certificate) (fuelContext (trace_a16 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a16 2).stores ((trace_a16 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a16 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a16 2).stores.certificate) (fuelContext (trace_a16 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a16 3).stores ((trace_a16 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a16 4).stores ((trace_a16 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [8, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a16 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a16 4).stores) (applyContext (trace_a16 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a16 5).stores ((trace_a16 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a16 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a16 5).stores) (applyContext (trace_a16 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a16 6).stores ((trace_a16 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a16 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a16 6).stores) (applyContext (trace_a16 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a16 7).stores ((trace_a16 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a16 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a16 7).stores) (applyContext (trace_a16 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a16 8).stores ((trace_a16 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a16 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a16 8).stores) (applyContext (trace_a16 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a16 9).stores ((trace_a16 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a16 9).stores)
        (applyRegisterEquiv.symm ((trace_a16 9).stage.apply regs)) (applyContext (trace_a16 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a16 10).stores ((trace_a16 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_a16 11).stores ((trace_a16 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_a16 12).stores ((trace_a16 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_a16 13).stores ((trace_a16 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_a16 14).stores ((trace_a16 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a16 15).stores ((trace_a16 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a16 16).stores ((trace_a16 16).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a16 17).stores ((trace_a16 17).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a16 18).stores ((trace_a16 18).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a16 19).stores ((trace_a16 19).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_a16 20).stores rfl ((trace_a16 20).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a16 21).stores ((trace_a16 21).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a16 22).stores ((trace_a16 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 1, 0, 0, 0, 0] [1, 1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_a16 22).stage.apply regs)) (equalityContext (trace_a16 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a16 23).stores ((trace_a16 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0, 0] [1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_a16 23).stage.apply regs)) (equalityContext (trace_a16 23).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a16 24).stores ((trace_a16 24).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0, 0] [0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_a16 24).stage.apply regs)) (equalityContext (trace_a16 24).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a16 25).stores ((trace_a16 25).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((trace_a16 25).stage.apply regs)) (equalityContext (trace_a16 25).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a16 26).stores ((trace_a16 26).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_a16 26).stage.apply regs)) (equalityContext (trace_a16 26).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a16 27).stores ((trace_a16 27).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_a16 27).stage.apply regs)) (equalityContext (trace_a16 27).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a16 28).stores ((trace_a16 28).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_a16 28).stage.apply regs)) (equalityContext (trace_a16 28).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a16 29).stores ((trace_a16 29).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a16 29).stage.apply regs)) (equalityContext (trace_a16 29).stores ctx))
  · exact equality_join_step caller .equal (trace_a16 30).stores ((trace_a16 30).stage.apply regs) ctx

theorem trace_a17_steps (n : Nat) (bound : n < 33) :
    step caller ((trace_a17 n).reached regs ctx) =
      some ((trace_a17 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a17 0).stores 6 [9, 10] rfl ((trace_a17 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a17 1).stores ((trace_a17 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a17 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a17 1).stores.certificate) (fuelContext (trace_a17 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a17 2).stores ((trace_a17 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a17 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a17 2).stores.certificate) (fuelContext (trace_a17 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a17 3).stores ((trace_a17 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a17 4).stores ((trace_a17 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [9, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a17 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a17 4).stores) (applyContext (trace_a17 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a17 5).stores ((trace_a17 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .right [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a17 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a17 5).stores) (applyContext (trace_a17 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a17 6).stores ((trace_a17 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.right] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a17 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a17 6).stores) (applyContext (trace_a17 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a17 7).stores ((trace_a17 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .right [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a17 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a17 7).stores) (applyContext (trace_a17 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a17 8).stores ((trace_a17 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a17 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a17 8).stores) (applyContext (trace_a17 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a17 9).stores ((trace_a17 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a17 9).stores)
        (applyRegisterEquiv.symm ((trace_a17 9).stage.apply regs)) (applyContext (trace_a17 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a17 10).stores ((trace_a17 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanPrefix .left) (trace_a17 11).stores ((trace_a17 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_a17 12).stores ((trace_a17 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_a17 13).stores ((trace_a17 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_a17 14).stores ((trace_a17 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_a17 15).stores ((trace_a17 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a17 16).stores ((trace_a17 16).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a17 17).stores ((trace_a17 17).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a17 18).stores ((trace_a17 18).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a17 19).stores ((trace_a17 19).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a17 20).stores ((trace_a17 20).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a17 21).stores ((trace_a17 21).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_a17 22).stores rfl ((trace_a17 22).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a17 23).stores ((trace_a17 23).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a17 24).stores ((trace_a17 24).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 1, 1, 0, 0, 0] [0, 1, 1, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_a17 24).stage.apply regs)) (equalityContext (trace_a17 24).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a17 25).stores ((trace_a17 25).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [1, 1, 0, 0, 0] [1, 1, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_a17 25).stage.apply regs)) (equalityContext (trace_a17 25).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a17 26).stores ((trace_a17 26).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0] [1, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_a17 26).stage.apply regs)) (equalityContext (trace_a17 26).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a17 27).stores ((trace_a17 27).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((trace_a17 27).stage.apply regs)) (equalityContext (trace_a17 27).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a17 28).stores ((trace_a17 28).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_a17 28).stage.apply regs)) (equalityContext (trace_a17 28).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a17 29).stores ((trace_a17 29).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_a17 29).stage.apply regs)) (equalityContext (trace_a17 29).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a17 30).stores ((trace_a17 30).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_a17 30).stage.apply regs)) (equalityContext (trace_a17 30).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a17 31).stores ((trace_a17 31).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a17 31).stage.apply regs)) (equalityContext (trace_a17 31).stores ctx))
  · exact equality_join_step caller .equal (trace_a17 32).stores ((trace_a17 32).stage.apply regs) ctx

theorem trace_a18_steps (n : Nat) (bound : n < 42) :
    step caller ((trace_a18 n).reached regs ctx) =
      some ((trace_a18 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a18 0).stores 6 [10, 7, 10] rfl ((trace_a18 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a18 1).stores ((trace_a18 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((trace_a18 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a18 1).stores.certificate) (fuelContext (trace_a18 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a18 2).stores ((trace_a18 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a18 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_a18 2).stores.certificate) (fuelContext (trace_a18 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a18 3).stores ((trace_a18 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a18 3).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a18 3).stores.certificate) (fuelContext (trace_a18 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a18 4).stores ((trace_a18 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((trace_a18 4).stage.apply regs) (FuelDispatchMachine.stores ((trace_a18 4).stores.certificate) (fuelContext (trace_a18 4).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a18 5).stores ((trace_a18 5).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a18 6).stores ((trace_a18 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 7, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a18 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a18 6).stores) (applyContext (trace_a18 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a18 7).stores ((trace_a18 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [7, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a18 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a18 7).stores) (applyContext (trace_a18 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a18 8).stores ((trace_a18 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [7, 10] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a18 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a18 8).stores) (applyContext (trace_a18 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a18 9).stores ((trace_a18 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a18 9).stores)
        (applyRegisterEquiv.symm ((trace_a18 9).stage.apply regs)) (applyContext (trace_a18 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a18 10).stores ((trace_a18 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_a18 11).stores ((trace_a18 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_a18 12).stores ((trace_a18 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_a18 13).stores ((trace_a18 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a18 14).stores ((trace_a18 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a18 15).stores ((trace_a18 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a18 16).stores ((trace_a18 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a18 17).stores ((trace_a18 17).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_a18 18).stores 7 [10] rfl ((trace_a18 18).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a18 19).stores ((trace_a18 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a18 19).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a18 19).stores.certificate) (fuelContext (trace_a18 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a18 20).stores ((trace_a18 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_a18 20).stage.apply regs) (FuelDispatchMachine.stores ((trace_a18 20).stores.certificate) (fuelContext (trace_a18 20).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a18 21).stores ((trace_a18 21).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a18 22).stores ((trace_a18 22).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .right [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a18 22).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a18 22).stores) (applyContext (trace_a18 22).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .right) (trace_a18 23).stores ((trace_a18 23).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .right [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a18 23).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a18 23).stores) (applyContext (trace_a18 23).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .right) (trace_a18 24).stores ((trace_a18 24).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .right [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a18 24).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a18 24).stores) (applyContext (trace_a18 24).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .right)) (trace_a18 25).stores ((trace_a18 25).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .right) (applyData (trace_a18 25).stores)
        (applyRegisterEquiv.symm ((trace_a18 25).stage.apply regs)) (applyContext (trace_a18 25).stores ctx))
  · exact apply_position_advance_step caller (.seek .right) (trace_a18 26).stores ((trace_a18 26).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .right) (trace_a18 27).stores ((trace_a18 27).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .right) (trace_a18 28).stores ((trace_a18 28).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (trace_a18 29).stores ((trace_a18 29).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (trace_a18 30).stores ((trace_a18 30).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a18 31).stores ((trace_a18 31).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a18 32).stores ((trace_a18 32).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_a18 33).stores rfl ((trace_a18 33).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a18 34).stores ((trace_a18 34).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a18 35).stores ((trace_a18 35).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 1, 0, 0] [0, 1, 0, 0] (equalityRegisterEquiv.symm ((trace_a18 35).stage.apply regs)) (equalityContext (trace_a18 35).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a18 36).stores ((trace_a18 36).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [1, 0, 0] [1, 0, 0] (equalityRegisterEquiv.symm ((trace_a18 36).stage.apply regs)) (equalityContext (trace_a18 36).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a18 37).stores ((trace_a18 37).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_a18 37).stage.apply regs)) (equalityContext (trace_a18 37).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a18 38).stores ((trace_a18 38).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_a18 38).stage.apply regs)) (equalityContext (trace_a18 38).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a18 39).stores ((trace_a18 39).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_a18 39).stage.apply regs)) (equalityContext (trace_a18 39).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a18 40).stores ((trace_a18 40).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a18 40).stage.apply regs)) (equalityContext (trace_a18 40).stores ctx))
  · exact equality_join_step caller .equal (trace_a18 41).stores ((trace_a18 41).stage.apply regs) ctx

theorem trace_a19_steps (n : Nat) (bound : n < 22) :
    step caller ((trace_a19 n).reached regs ctx) =
      some ((trace_a19 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a19 0).stores 6 [10, 7, 10] rfl ((trace_a19 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a19 1).stores ((trace_a19 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a19 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a19 1).stores.certificate) (fuelContext (trace_a19 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a19 2).stores ((trace_a19 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a19 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a19 2).stores.certificate) (fuelContext (trace_a19 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a19 3).stores ((trace_a19 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a19 4).stores ((trace_a19 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 7, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a19 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a19 4).stores) (applyContext (trace_a19 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a19 5).stores ((trace_a19 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [7, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a19 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a19 5).stores) (applyContext (trace_a19 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a19 6).stores ((trace_a19 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [7, 10] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a19 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a19 6).stores) (applyContext (trace_a19 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a19 7).stores ((trace_a19 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a19 7).stores)
        (applyRegisterEquiv.symm ((trace_a19 7).stage.apply regs)) (applyContext (trace_a19 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a19 8).stores ((trace_a19 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_a19 9).stores ((trace_a19 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_a19 10).stores ((trace_a19 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_a19 11).stores ((trace_a19 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a19 12).stores ((trace_a19 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a19 13).stores ((trace_a19 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a19 14).stores ((trace_a19 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a19 15).stores ((trace_a19 15).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_a19 16).stores 7 [10] rfl ((trace_a19 16).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a19 17).stores ((trace_a19 17).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a19 17).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a19 17).stores.certificate) (fuelContext (trace_a19 17).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a19 18).stores ((trace_a19 18).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_a19 18).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_a19 18).stores.certificate) (fuelContext (trace_a19 18).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_a19 19).stores ((trace_a19 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a19 19).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a19 19).stores.certificate) (fuelContext (trace_a19 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_a19 20).stores ((trace_a19 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a19 20).stage.apply regs) (FuelDispatchMachine.stores ((trace_a19 20).stores.certificate) (fuelContext (trace_a19 20).stores ctx)))
  · exact fuel_join_step caller .zero (trace_a19 21).stores ((trace_a19 21).stage.apply regs) ctx

theorem trace_a20_steps (n : Nat) (bound : n < 25) :
    step caller ((trace_a20 n).reached regs ctx) =
      some ((trace_a20 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a20 0).stores 6 [10, 15] rfl ((trace_a20 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a20 1).stores ((trace_a20 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((trace_a20 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a20 1).stores.certificate) (fuelContext (trace_a20 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a20 2).stores ((trace_a20 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a20 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_a20 2).stores.certificate) (fuelContext (trace_a20 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a20 3).stores ((trace_a20 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a20 3).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a20 3).stores.certificate) (fuelContext (trace_a20 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a20 4).stores ((trace_a20 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((trace_a20 4).stage.apply regs) (FuelDispatchMachine.stores ((trace_a20 4).stores.certificate) (fuelContext (trace_a20 4).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a20 5).stores ((trace_a20 5).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a20 6).stores ((trace_a20 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a20 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a20 6).stores) (applyContext (trace_a20 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a20 7).stores ((trace_a20 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a20 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a20 7).stores) (applyContext (trace_a20 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a20 8).stores ((trace_a20 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a20 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a20 8).stores) (applyContext (trace_a20 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a20 9).stores ((trace_a20 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a20 9).stores)
        (applyRegisterEquiv.symm ((trace_a20 9).stage.apply regs)) (applyContext (trace_a20 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a20 10).stores ((trace_a20 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_a20 11).stores ((trace_a20 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_a20 12).stores ((trace_a20 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_a20 13).stores ((trace_a20 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a20 14).stores ((trace_a20 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a20 15).stores ((trace_a20 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a20 16).stores ((trace_a20 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a20 17).stores ((trace_a20 17).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_a20 18).stores 15 [] rfl ((trace_a20 18).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a20 19).stores ((trace_a20 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a20 19).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a20 19).stores.certificate) (fuelContext (trace_a20 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a20 20).stores ((trace_a20 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_a20 20).stage.apply regs) (FuelDispatchMachine.stores ((trace_a20 20).stores.certificate) (fuelContext (trace_a20 20).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a20 21).stores ((trace_a20 21).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a20 22).stores ((trace_a20 22).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a20 22).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a20 22).stores) (applyContext (trace_a20 22).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_a20 23).stores ((trace_a20 23).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_a20 23).stores)
        (applyRegisterEquiv.symm ((trace_a20 23).stage.apply regs)) (applyContext (trace_a20 23).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_a20 24).stores ((trace_a20 24).stage.apply regs) ctx

theorem trace_a21_steps (n : Nat) (bound : n < 24) :
    step caller ((trace_a21 n).reached regs ctx) =
      some ((trace_a21 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a21 0).stores 6 [10] rfl ((trace_a21 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a21 1).stores ((trace_a21 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a21 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a21 1).stores.certificate) (fuelContext (trace_a21 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a21 2).stores ((trace_a21 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a21 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a21 2).stores.certificate) (fuelContext (trace_a21 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a21 3).stores ((trace_a21 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a21 4).stores ((trace_a21 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a21 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a21 4).stores) (applyContext (trace_a21 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a21 5).stores ((trace_a21 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a21 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a21 5).stores) (applyContext (trace_a21 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a21 6).stores ((trace_a21 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a21 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a21 6).stores) (applyContext (trace_a21 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a21 7).stores ((trace_a21 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a21 7).stores)
        (applyRegisterEquiv.symm ((trace_a21 7).stage.apply regs)) (applyContext (trace_a21 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a21 8).stores ((trace_a21 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_a21 9).stores ((trace_a21 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_a21 10).stores ((trace_a21 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_a21 11).stores ((trace_a21 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a21 12).stores ((trace_a21 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a21 13).stores ((trace_a21 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a21 14).stores ((trace_a21 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a21 15).stores ((trace_a21 15).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_a21 16).stores rfl ((trace_a21 16).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a21 17).stores ((trace_a21 17).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a21 18).stores ((trace_a21 18).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 15] [1, 0, 15] (equalityRegisterEquiv.symm ((trace_a21 18).stage.apply regs)) (equalityContext (trace_a21 18).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a21 19).stores ((trace_a21 19).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 15] [0, 15] (equalityRegisterEquiv.symm ((trace_a21 19).stage.apply regs)) (equalityContext (trace_a21 19).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a21 20).stores ((trace_a21 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [15] [15] (equalityRegisterEquiv.symm ((trace_a21 20).stage.apply regs)) (equalityContext (trace_a21 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a21 21).stores ((trace_a21 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 15 [] [] (equalityRegisterEquiv.symm ((trace_a21 21).stage.apply regs)) (equalityContext (trace_a21 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a21 22).stores ((trace_a21 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a21 22).stage.apply regs)) (equalityContext (trace_a21 22).stores ctx))
  · exact equality_join_step caller .equal (trace_a21 23).stores ((trace_a21 23).stage.apply regs) ctx

theorem trace_d01_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_d01 n).reached regs ctx) =
      some ((trace_d01 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_d01 0).stores rfl ((trace_d01 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_d01 1).stores ((trace_d01 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d01 2).stores ((trace_d01 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_d01 2).stage.apply regs)) (equalityContext (trace_d01 2).stores ctx))
  · exact equality_join_step caller .equal (trace_d01 3).stores ((trace_d01 3).stage.apply regs) ctx

theorem trace_d02_steps (n : Nat) (bound : n < 9) :
    step caller ((trace_d02 n).reached regs ctx) =
      some ((trace_d02 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_d02 0).stores 15 [] rfl ((trace_d02 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_d02 1).stores ((trace_d02 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_d02 1).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((trace_d02 1).stores.certificate) (fuelContext (trace_d02 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_d02 2).stores ((trace_d02 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_d02 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_d02 2).stores.certificate) (fuelContext (trace_d02 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_d02 3).stores ((trace_d02 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((trace_d02 3).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_d02 3).stores.certificate) (fuelContext (trace_d02 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_d02 4).stores ((trace_d02 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, true, false] ((trace_d02 4).stage.apply regs) (FuelDispatchMachine.stores ((trace_d02 4).stores.certificate) (fuelContext (trace_d02 4).stores ctx)))
  · exact fuel_join_step caller .positive (trace_d02 5).stores ((trace_d02 5).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_d02 6).stores ((trace_d02 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [.right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d02 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d02 6).stores) (applyContext (trace_d02 6).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_d02 7).stores ((trace_d02 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_d02 7).stores)
        (applyRegisterEquiv.symm ((trace_d02 7).stage.apply regs)) (applyContext (trace_d02 7).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_d02 8).stores ((trace_d02 8).stage.apply regs) ctx

theorem trace_d03_steps (n : Nat) (bound : n < 6) :
    step caller ((trace_d03 n).reached regs ctx) =
      some ((trace_d03 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_d03 0).stores 15 [] rfl ((trace_d03 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_d03 1).stores ((trace_d03 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_d03 1).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((trace_d03 1).stores.certificate) (fuelContext (trace_d03 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_d03 2).stores ((trace_d03 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_d03 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_d03 2).stores.certificate) (fuelContext (trace_d03 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_d03 3).stores ((trace_d03 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_d03 3).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_d03 3).stores.certificate) (fuelContext (trace_d03 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_d03 4).stores ((trace_d03 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_d03 4).stage.apply regs) (FuelDispatchMachine.stores ((trace_d03 4).stores.certificate) (fuelContext (trace_d03 4).stores ctx)))
  · exact fuel_join_step caller .zero (trace_d03 5).stores ((trace_d03 5).stage.apply regs) ctx

theorem trace_d04_steps (n : Nat) (bound : n < 7) :
    step caller ((trace_d04 n).reached regs ctx) =
      some ((trace_d04 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_d04 0).stores 15 [] rfl ((trace_d04 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_d04 1).stores ((trace_d04 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_d04 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_d04 1).stores.certificate) (fuelContext (trace_d04 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_d04 2).stores ((trace_d04 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_d04 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_d04 2).stores.certificate) (fuelContext (trace_d04 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_d04 3).stores ((trace_d04 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_d04 4).stores ((trace_d04 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [.right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d04 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d04 4).stores) (applyContext (trace_d04 4).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_d04 5).stores ((trace_d04 5).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_d04 5).stores)
        (applyRegisterEquiv.symm ((trace_d04 5).stage.apply regs)) (applyContext (trace_d04 5).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_d04 6).stores ((trace_d04 6).stage.apply regs) ctx

theorem trace_d05_steps (n : Nat) (bound : n < 13) :
    step caller ((trace_d05 n).reached regs ctx) =
      some ((trace_d05 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_d05 0).stores 6 [8, 15] rfl ((trace_d05 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_d05 1).stores ((trace_d05 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_d05 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_d05 1).stores.certificate) (fuelContext (trace_d05 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_d05 2).stores ((trace_d05 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_d05 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_d05 2).stores.certificate) (fuelContext (trace_d05 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_d05 3).stores ((trace_d05 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_d05 4).stores ((trace_d05 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [8, 15] [.right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d05 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d05 4).stores) (applyContext (trace_d05 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_d05 5).stores ((trace_d05 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [15] [.right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d05 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d05 5).stores) (applyContext (trace_d05 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_d05 6).stores ((trace_d05 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_foreign (fun _ => .halt) .left 15 [] [.left, .right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d05 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d05 6).stores) (applyContext (trace_d05 6).stores ctx)) (by decide) (by decide) (by decide))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (trace_d05 7).stores ((trace_d05 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_cons (fun _ => .halt) .left .left [15] [.right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d05 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d05 7).stores) (applyContext (trace_d05 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (trace_d05 8).stores ((trace_d05 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_cons (fun _ => .halt) .left .right [8, 15] [.left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d05 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d05 8).stores) (applyContext (trace_d05 8).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (trace_d05 9).stores ((trace_d05 9).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_cons (fun _ => .halt) .left .left [9, 8, 15] [] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d05 9).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d05 9).stores) (applyContext (trace_d05 9).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (trace_d05 10).stores ((trace_d05 10).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_nil (fun _ => .halt) .left [8, 9, 8, 15] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d05 10).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d05 10).stores) (applyContext (trace_d05 10).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_d05 11).stores ((trace_d05 11).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_d05 11).stores)
        (applyRegisterEquiv.symm ((trace_d05 11).stage.apply regs)) (applyContext (trace_d05 11).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_d05 12).stores ((trace_d05 12).stage.apply regs) ctx

theorem trace_d06_steps (n : Nat) (bound : n < 30) :
    step caller ((trace_d06 n).reached regs ctx) =
      some ((trace_d06 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_d06 0).stores 6 [10] rfl ((trace_d06 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_d06 1).stores ((trace_d06 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_d06 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_d06 1).stores.certificate) (fuelContext (trace_d06 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_d06 2).stores ((trace_d06 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_d06 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_d06 2).stores.certificate) (fuelContext (trace_d06 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_d06 3).stores ((trace_d06 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_d06 4).stores ((trace_d06 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d06 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d06 4).stores) (applyContext (trace_d06 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_d06 5).stores ((trace_d06 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d06 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d06 5).stores) (applyContext (trace_d06 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_d06 6).stores ((trace_d06 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d06 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d06 6).stores) (applyContext (trace_d06 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_d06 7).stores ((trace_d06 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d06 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d06 7).stores) (applyContext (trace_d06 7).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_d06 8).stores ((trace_d06 8).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_d06 8).stores)
        (applyRegisterEquiv.symm ((trace_d06 8).stage.apply regs)) (applyContext (trace_d06 8).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_d06 9).stores ((trace_d06 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_d06 10).stores ((trace_d06 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_d06 11).stores ((trace_d06 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_d06 12).stores ((trace_d06 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_d06 13).stores ((trace_d06 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_d06 14).stores ((trace_d06 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_d06 15).stores ((trace_d06 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_d06 16).stores ((trace_d06 16).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_d06 17).stores ((trace_d06 17).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_d06 18).stores ((trace_d06 18).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_d06 19).stores rfl ((trace_d06 19).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_d06 20).stores ((trace_d06 20).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d06 21).stores ((trace_d06 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 1, 0, 0, 0, 0] [1, 1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_d06 21).stage.apply regs)) (equalityContext (trace_d06 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d06 22).stores ((trace_d06 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0, 0] [1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_d06 22).stage.apply regs)) (equalityContext (trace_d06 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d06 23).stores ((trace_d06 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0, 0] [0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_d06 23).stage.apply regs)) (equalityContext (trace_d06 23).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d06 24).stores ((trace_d06 24).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((trace_d06 24).stage.apply regs)) (equalityContext (trace_d06 24).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d06 25).stores ((trace_d06 25).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_d06 25).stage.apply regs)) (equalityContext (trace_d06 25).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d06 26).stores ((trace_d06 26).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_d06 26).stage.apply regs)) (equalityContext (trace_d06 26).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d06 27).stores ((trace_d06 27).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_d06 27).stage.apply regs)) (equalityContext (trace_d06 27).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d06 28).stores ((trace_d06 28).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_d06 28).stage.apply regs)) (equalityContext (trace_d06 28).stores ctx))
  · exact equality_join_step caller .equal (trace_d06 29).stores ((trace_d06 29).stage.apply regs) ctx

theorem trace_d07_steps (n : Nat) (bound : n < 29) :
    step caller ((trace_d07 n).reached regs ctx) =
      some ((trace_d07 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_d07 0).stores 6 [10] rfl ((trace_d07 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_d07 1).stores ((trace_d07 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_d07 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_d07 1).stores.certificate) (fuelContext (trace_d07 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_d07 2).stores ((trace_d07 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_d07 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_d07 2).stores.certificate) (fuelContext (trace_d07 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_d07 3).stores ((trace_d07 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_d07 4).stores ((trace_d07 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d07 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d07 4).stores) (applyContext (trace_d07 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_d07 5).stores ((trace_d07 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d07 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d07 5).stores) (applyContext (trace_d07 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_d07 6).stores ((trace_d07 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d07 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d07 6).stores) (applyContext (trace_d07 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_d07 7).stores ((trace_d07 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_d07 7).stores)
        (applyRegisterEquiv.symm ((trace_d07 7).stage.apply regs)) (applyContext (trace_d07 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_d07 8).stores ((trace_d07 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_d07 9).stores ((trace_d07 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_d07 10).stores ((trace_d07 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_d07 11).stores ((trace_d07 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_d07 12).stores ((trace_d07 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_d07 13).stores ((trace_d07 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_d07 14).stores ((trace_d07 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_d07 15).stores ((trace_d07 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_d07 16).stores ((trace_d07 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_d07 17).stores ((trace_d07 17).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_d07 18).stores rfl ((trace_d07 18).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_d07 19).stores ((trace_d07 19).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d07 20).stores ((trace_d07 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 1, 0, 0, 0, 0] [1, 1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_d07 20).stage.apply regs)) (equalityContext (trace_d07 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d07 21).stores ((trace_d07 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0, 0] [1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_d07 21).stage.apply regs)) (equalityContext (trace_d07 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d07 22).stores ((trace_d07 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0, 0] [0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_d07 22).stage.apply regs)) (equalityContext (trace_d07 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d07 23).stores ((trace_d07 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((trace_d07 23).stage.apply regs)) (equalityContext (trace_d07 23).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d07 24).stores ((trace_d07 24).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_d07 24).stage.apply regs)) (equalityContext (trace_d07 24).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d07 25).stores ((trace_d07 25).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_d07 25).stage.apply regs)) (equalityContext (trace_d07 25).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d07 26).stores ((trace_d07 26).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_d07 26).stage.apply regs)) (equalityContext (trace_d07 26).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d07 27).stores ((trace_d07 27).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_d07 27).stage.apply regs)) (equalityContext (trace_d07 27).stores ctx))
  · exact equality_join_step caller .equal (trace_d07 28).stores ((trace_d07 28).stage.apply regs) ctx

theorem trace_d08_steps (n : Nat) (bound : n < 7) :
    step caller ((trace_d08 n).reached regs ctx) =
      some ((trace_d08 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_d08 0).stores ((trace_d08 0).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_d08 1).stores ((trace_d08 1).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_d08 2).stores rfl ((trace_d08 2).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_d08 3).stores ((trace_d08 3).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d08 4).stores ((trace_d08 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_d08 4).stage.apply regs)) (equalityContext (trace_d08 4).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d08 5).stores ((trace_d08 5).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_d08 5).stage.apply regs)) (equalityContext (trace_d08 5).stores ctx))
  · exact equality_join_step caller .equal (trace_d08 6).stores ((trace_d08 6).stage.apply regs) ctx

theorem trace_d09_steps (n : Nat) (bound : n < 5) :
    step caller ((trace_d09 n).reached regs ctx) =
      some ((trace_d09 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact apply_join_step caller MoveApplyMachine.success (trace_d09 0).stores ((trace_d09 0).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_d09 1).stores rfl ((trace_d09 1).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_d09 2).stores ((trace_d09 2).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d09 3).stores ((trace_d09 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_d09 3).stage.apply regs)) (equalityContext (trace_d09 3).stores ctx))
  · exact equality_join_step caller .equal (trace_d09 4).stores ((trace_d09 4).stage.apply regs) ctx

theorem trace_d10_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_d10 n).reached regs ctx) =
      some ((trace_d10 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact fuel_join_step caller .positive (trace_d10 0).stores ((trace_d10 0).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_d10 1).stores ((trace_d10 1).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_nil (fun _ => .halt) [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d10 1).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d10 1).stores) (applyContext (trace_d10 1).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_d10 2).stores ((trace_d10 2).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_d10 2).stores)
        (applyRegisterEquiv.symm ((trace_d10 2).stage.apply regs)) (applyContext (trace_d10 2).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_d10 3).stores ((trace_d10 3).stage.apply regs) ctx

theorem trace_d11_steps (n : Nat) (bound : n < 3) :
    step caller ((trace_d11 n).reached regs ctx) =
      some ((trace_d11 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact fuel_join_step caller .atEnd (trace_d11 0).stores ((trace_d11 0).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d11 1).stores ((trace_d11 1).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_d11 1).stage.apply regs)) (equalityContext (trace_d11 1).stores ctx))
  · exact equality_join_step caller .equal (trace_d11 2).stores ((trace_d11 2).stage.apply regs) ctx

theorem trace_d12_steps (n : Nat) (bound : n < 2) :
    step caller ((trace_d12 n).reached regs ctx) =
      some ((trace_d12 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d12 0).stores ((trace_d12 0).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_d12 0).stage.apply regs)) (equalityContext (trace_d12 0).stores ctx))
  · exact equality_join_step caller .equal (trace_d12 1).stores ((trace_d12 1).stage.apply regs) ctx

theorem trace_d13_steps (n : Nat) (bound : n < 1) :
    step caller ((trace_d13 n).reached regs ctx) =
      some ((trace_d13 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact equality_join_step caller .equal (trace_d13 0).stores ((trace_d13 0).stage.apply regs) ctx

theorem trace_r01_steps (n : Nat) (bound : n < 7) :
    step caller ((trace_r01 n).reached regs ctx) =
      some ((trace_r01 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r01 0).stores ((trace_r01 0).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r01 0).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r01 0).stores.certificate) (fuelContext (trace_r01 0).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r01 1).stores ((trace_r01 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((trace_r01 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r01 1).stores.certificate) (fuelContext (trace_r01 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r01 2).stores ((trace_r01 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, true] ((trace_r01 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_r01 2).stores.certificate) (fuelContext (trace_r01 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r01 3).stores ((trace_r01 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r01 4).stores ((trace_r01 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r01 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r01 4).stores) (applyContext (trace_r01 4).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_r01 5).stores ((trace_r01 5).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_r01 5).stores)
        (applyRegisterEquiv.symm ((trace_r01 5).stage.apply regs)) (applyContext (trace_r01 5).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_r01 6).stores ((trace_r01 6).stage.apply regs) ctx

theorem trace_r02_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_r02 n).reached regs ctx) =
      some ((trace_r02 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r02 0).stores ((trace_r02 0).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((trace_r02 0).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r02 0).stores.certificate) (fuelContext (trace_r02 0).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r02 1).stores ((trace_r02 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, true] ((trace_r02 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r02 1).stores.certificate) (fuelContext (trace_r02 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r02 2).stores ((trace_r02 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false, true] ((trace_r02 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_r02 2).stores.certificate) (fuelContext (trace_r02 2).stores ctx)))
  · exact fuel_join_step caller .zero (trace_r02 3).stores ((trace_r02 3).stage.apply regs) ctx

theorem trace_r03_steps (n : Nat) (bound : n < 17) :
    step caller ((trace_r03 n).reached regs ctx) =
      some ((trace_r03 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_r03 0).stores ((trace_r03 0).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r03 0).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r03 0).stores) (applyContext (trace_r03 0).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_r03 1).stores ((trace_r03 1).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [15] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r03 1).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r03 1).stores) (applyContext (trace_r03 1).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_r03 2).stores ((trace_r03 2).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_r03 2).stores)
        (applyRegisterEquiv.symm ((trace_r03 2).stage.apply regs)) (applyContext (trace_r03 2).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_r03 3).stores ((trace_r03 3).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_r03 4).stores ((trace_r03 4).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_r03 5).stores ((trace_r03 5).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_r03 6).stores ((trace_r03 6).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_r03 7).stores ((trace_r03 7).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r03 8).stores ((trace_r03 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r03 9).stores ((trace_r03 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_r03 10).stores ((trace_r03 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_r03 11).stores ((trace_r03 11).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_r03 12).stores ((trace_r03 12).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_r03 13).stores 15 [] rfl ((trace_r03 13).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r03 14).stores ((trace_r03 14).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_r03 14).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r03 14).stores.certificate) (fuelContext (trace_r03 14).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r03 15).stores ((trace_r03 15).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r03 15).stage.apply regs) (FuelDispatchMachine.stores ((trace_r03 15).stores.certificate) (fuelContext (trace_r03 15).stores ctx)))
  · exact fuel_join_step caller .zero (trace_r03 16).stores ((trace_r03 16).stage.apply regs) ctx

theorem trace_r04_steps (n : Nat) (bound : n < 27) :
    step caller ((trace_r04 n).reached regs ctx) =
      some ((trace_r04 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r04 0).stores ((trace_r04 0).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((trace_r04 0).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r04 0).stores.certificate) (fuelContext (trace_r04 0).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r04 1).stores ((trace_r04 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r04 1).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((trace_r04 1).stores.certificate) (fuelContext (trace_r04 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r04 2).stores ((trace_r04 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r04 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r04 2).stores.certificate) (fuelContext (trace_r04 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r04 3).stores ((trace_r04 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((trace_r04 3).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r04 3).stores.certificate) (fuelContext (trace_r04 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r04 4).stores ((trace_r04 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, true, false] ((trace_r04 4).stage.apply regs) (FuelDispatchMachine.stores ((trace_r04 4).stores.certificate) (fuelContext (trace_r04 4).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r04 5).stores ((trace_r04 5).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r04 6).stores ((trace_r04 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r04 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r04 6).stores) (applyContext (trace_r04 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_r04 7).stores ((trace_r04 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r04 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r04 7).stores) (applyContext (trace_r04 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_r04 8).stores ((trace_r04 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r04 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r04 8).stores) (applyContext (trace_r04 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_r04 9).stores ((trace_r04 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_r04 9).stores)
        (applyRegisterEquiv.symm ((trace_r04 9).stage.apply regs)) (applyContext (trace_r04 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_r04 10).stores ((trace_r04 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_r04 11).stores ((trace_r04 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_r04 12).stores ((trace_r04 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_r04 13).stores ((trace_r04 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r04 14).stores ((trace_r04 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r04 15).stores ((trace_r04 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_r04 16).stores ((trace_r04 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_r04 17).stores ((trace_r04 17).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_r04 18).stores rfl ((trace_r04 18).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_r04 19).stores ((trace_r04 19).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r04 20).stores ((trace_r04 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0] [1, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_r04 20).stage.apply regs)) (equalityContext (trace_r04 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r04 21).stores ((trace_r04 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((trace_r04 21).stage.apply regs)) (equalityContext (trace_r04 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r04 22).stores ((trace_r04 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_r04 22).stage.apply regs)) (equalityContext (trace_r04 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r04 23).stores ((trace_r04 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_r04 23).stage.apply regs)) (equalityContext (trace_r04 23).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r04 24).stores ((trace_r04 24).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_r04 24).stage.apply regs)) (equalityContext (trace_r04 24).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r04 25).stores ((trace_r04 25).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_r04 25).stage.apply regs)) (equalityContext (trace_r04 25).stores ctx))
  · exact equality_join_step caller .equal (trace_r04 26).stores ((trace_r04 26).stage.apply regs) ctx

theorem trace_r05_steps (n : Nat) (bound : n < 6) :
    step caller ((trace_r05 n).reached regs ctx) =
      some ((trace_r05 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_r05 0).stores rfl ((trace_r05 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_r05 1).stores ((trace_r05 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r05 2).stores ((trace_r05 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0] [0, 15, 2] (equalityRegisterEquiv.symm ((trace_r05 2).stage.apply regs)) (equalityContext (trace_r05 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r05 3).stores ((trace_r05 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [15, 2] (equalityRegisterEquiv.symm ((trace_r05 3).stage.apply regs)) (equalityContext (trace_r05 3).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r05 4).stores ((trace_r05 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_cons (fun _ => .halt) 15 [2] (equalityRegisterEquiv.symm ((trace_r05 4).stage.apply regs)) (equalityContext (trace_r05 4).stores ctx))
  · exact equality_join_step caller .different (trace_r05 5).stores ((trace_r05 5).stage.apply regs) ctx

theorem trace_r06_steps (n : Nat) (bound : n < 6) :
    step caller ((trace_r06 n).reached regs ctx) =
      some ((trace_r06 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_r06 0).stores rfl ((trace_r06 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_r06 1).stores ((trace_r06 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r06 2).stores ((trace_r06 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 15, 2] [0] (equalityRegisterEquiv.symm ((trace_r06 2).stage.apply regs)) (equalityContext (trace_r06 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r06 3).stores ((trace_r06 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [15, 2] [] (equalityRegisterEquiv.symm ((trace_r06 3).stage.apply regs)) (equalityContext (trace_r06 3).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r06 4).stores ((trace_r06 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_cons_nil (fun _ => .halt) 15 [2] (equalityRegisterEquiv.symm ((trace_r06 4).stage.apply regs)) (equalityContext (trace_r06 4).stores ctx))
  · exact equality_join_step caller .different (trace_r06 5).stores ((trace_r06 5).stage.apply regs) ctx

theorem trace_r07_steps (n : Nat) (bound : n < 22) :
    step caller ((trace_r07 n).reached regs ctx) =
      some ((trace_r07 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_r07 0).stores 6 [10, 15] rfl ((trace_r07 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r07 1).stores ((trace_r07 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r07 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r07 1).stores.certificate) (fuelContext (trace_r07 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r07 2).stores ((trace_r07 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r07 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_r07 2).stores.certificate) (fuelContext (trace_r07 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r07 3).stores ((trace_r07 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r07 4).stores ((trace_r07 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r07 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r07 4).stores) (applyContext (trace_r07 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_r07 5).stores ((trace_r07 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r07 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r07 5).stores) (applyContext (trace_r07 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_r07 6).stores ((trace_r07 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r07 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r07 6).stores) (applyContext (trace_r07 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_r07 7).stores ((trace_r07 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_r07 7).stores)
        (applyRegisterEquiv.symm ((trace_r07 7).stage.apply regs)) (applyContext (trace_r07 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_r07 8).stores ((trace_r07 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_r07 9).stores ((trace_r07 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_r07 10).stores ((trace_r07 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_r07 11).stores ((trace_r07 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r07 12).stores ((trace_r07 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r07 13).stores ((trace_r07 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_r07 14).stores ((trace_r07 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_r07 15).stores ((trace_r07 15).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_r07 16).stores 15 [] rfl ((trace_r07 16).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r07 17).stores ((trace_r07 17).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r07 17).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r07 17).stores.certificate) (fuelContext (trace_r07 17).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r07 18).stores ((trace_r07 18).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_r07 18).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r07 18).stores.certificate) (fuelContext (trace_r07 18).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r07 19).stores ((trace_r07 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r07 19).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r07 19).stores.certificate) (fuelContext (trace_r07 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r07 20).stores ((trace_r07 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r07 20).stage.apply regs) (FuelDispatchMachine.stores ((trace_r07 20).stores.certificate) (fuelContext (trace_r07 20).stores ctx)))
  · exact fuel_join_step caller .zero (trace_r07 21).stores ((trace_r07 21).stage.apply regs) ctx

theorem trace_r08_steps (n : Nat) (bound : n < 41) :
    step caller ((trace_r08 n).reached regs ctx) =
      some ((trace_r08 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_r08 0).stores 6 [10, 7, 10, 15] rfl ((trace_r08 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r08 1).stores ((trace_r08 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((trace_r08 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r08 1).stores.certificate) (fuelContext (trace_r08 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r08 2).stores ((trace_r08 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r08 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r08 2).stores.certificate) (fuelContext (trace_r08 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r08 3).stores ((trace_r08 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r08 3).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r08 3).stores.certificate) (fuelContext (trace_r08 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r08 4).stores ((trace_r08 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((trace_r08 4).stage.apply regs) (FuelDispatchMachine.stores ((trace_r08 4).stores.certificate) (fuelContext (trace_r08 4).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r08 5).stores ((trace_r08 5).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r08 6).stores ((trace_r08 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 7, 10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r08 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r08 6).stores) (applyContext (trace_r08 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_r08 7).stores ((trace_r08 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [7, 10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r08 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r08 7).stores) (applyContext (trace_r08 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_r08 8).stores ((trace_r08 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [7, 10, 15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r08 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r08 8).stores) (applyContext (trace_r08 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_r08 9).stores ((trace_r08 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_r08 9).stores)
        (applyRegisterEquiv.symm ((trace_r08 9).stage.apply regs)) (applyContext (trace_r08 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_r08 10).stores ((trace_r08 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_r08 11).stores ((trace_r08 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_r08 12).stores ((trace_r08 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_r08 13).stores ((trace_r08 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r08 14).stores ((trace_r08 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r08 15).stores ((trace_r08 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_r08 16).stores ((trace_r08 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_r08 17).stores ((trace_r08 17).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_r08 18).stores 7 [10, 15] rfl ((trace_r08 18).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r08 19).stores ((trace_r08 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r08 19).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r08 19).stores.certificate) (fuelContext (trace_r08 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r08 20).stores ((trace_r08 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_r08 20).stage.apply regs) (FuelDispatchMachine.stores ((trace_r08 20).stores.certificate) (fuelContext (trace_r08 20).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r08 21).stores ((trace_r08 21).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r08 22).stores ((trace_r08 22).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .right [10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r08 22).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r08 22).stores) (applyContext (trace_r08 22).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .right) (trace_r08 23).stores ((trace_r08 23).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .right [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r08 23).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r08 23).stores) (applyContext (trace_r08 23).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .right) (trace_r08 24).stores ((trace_r08 24).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .right [15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r08 24).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r08 24).stores) (applyContext (trace_r08 24).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .right)) (trace_r08 25).stores ((trace_r08 25).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .right) (applyData (trace_r08 25).stores)
        (applyRegisterEquiv.symm ((trace_r08 25).stage.apply regs)) (applyContext (trace_r08 25).stores ctx))
  · exact apply_position_advance_step caller (.seek .right) (trace_r08 26).stores ((trace_r08 26).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .right) (trace_r08 27).stores ((trace_r08 27).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .right) (trace_r08 28).stores ((trace_r08 28).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (trace_r08 29).stores ((trace_r08 29).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (trace_r08 30).stores ((trace_r08 30).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_r08 31).stores ((trace_r08 31).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_r08 32).stores ((trace_r08 32).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_r08 33).stores 15 [] rfl ((trace_r08 33).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r08 34).stores ((trace_r08 34).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r08 34).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r08 34).stores.certificate) (fuelContext (trace_r08 34).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r08 35).stores ((trace_r08 35).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r08 35).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r08 35).stores.certificate) (fuelContext (trace_r08 35).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r08 36).stores ((trace_r08 36).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_r08 36).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((trace_r08 36).stores.certificate) (fuelContext (trace_r08 36).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r08 37).stores ((trace_r08 37).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r08 37).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r08 37).stores.certificate) (fuelContext (trace_r08 37).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r08 38).stores ((trace_r08 38).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r08 38).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r08 38).stores.certificate) (fuelContext (trace_r08 38).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r08 39).stores ((trace_r08 39).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_r08 39).stage.apply regs) (FuelDispatchMachine.stores ((trace_r08 39).stores.certificate) (fuelContext (trace_r08 39).stores ctx)))
  · exact fuel_join_step caller .zero (trace_r08 40).stores ((trace_r08 40).stage.apply regs) ctx

theorem trace_r09_steps (n : Nat) (bound : n < 40) :
    step caller ((trace_r09 n).reached regs ctx) =
      some ((trace_r09 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_r09 0).stores 6 [10, 7, 10, 15] rfl ((trace_r09 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r09 1).stores ((trace_r09 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((trace_r09 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r09 1).stores.certificate) (fuelContext (trace_r09 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r09 2).stores ((trace_r09 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, true] ((trace_r09 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_r09 2).stores.certificate) (fuelContext (trace_r09 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r09 3).stores ((trace_r09 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r09 4).stores ((trace_r09 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 7, 10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r09 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r09 4).stores) (applyContext (trace_r09 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_r09 5).stores ((trace_r09 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [7, 10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r09 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r09 5).stores) (applyContext (trace_r09 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_r09 6).stores ((trace_r09 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [7, 10, 15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r09 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r09 6).stores) (applyContext (trace_r09 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_r09 7).stores ((trace_r09 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_r09 7).stores)
        (applyRegisterEquiv.symm ((trace_r09 7).stage.apply regs)) (applyContext (trace_r09 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_r09 8).stores ((trace_r09 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_r09 9).stores ((trace_r09 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_r09 10).stores ((trace_r09 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_r09 11).stores ((trace_r09 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r09 12).stores ((trace_r09 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r09 13).stores ((trace_r09 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_r09 14).stores ((trace_r09 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_r09 15).stores ((trace_r09 15).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_r09 16).stores 7 [10, 15] rfl ((trace_r09 16).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r09 17).stores ((trace_r09 17).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((trace_r09 17).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r09 17).stores.certificate) (fuelContext (trace_r09 17).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r09 18).stores ((trace_r09 18).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r09 18).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r09 18).stores.certificate) (fuelContext (trace_r09 18).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r09 19).stores ((trace_r09 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r09 19).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r09 19).stores.certificate) (fuelContext (trace_r09 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r09 20).stores ((trace_r09 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((trace_r09 20).stage.apply regs) (FuelDispatchMachine.stores ((trace_r09 20).stores.certificate) (fuelContext (trace_r09 20).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r09 21).stores ((trace_r09 21).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r09 22).stores ((trace_r09 22).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .right [10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r09 22).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r09 22).stores) (applyContext (trace_r09 22).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .right) (trace_r09 23).stores ((trace_r09 23).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .right [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r09 23).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r09 23).stores) (applyContext (trace_r09 23).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .right) (trace_r09 24).stores ((trace_r09 24).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .right [15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r09 24).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r09 24).stores) (applyContext (trace_r09 24).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .right)) (trace_r09 25).stores ((trace_r09 25).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .right) (applyData (trace_r09 25).stores)
        (applyRegisterEquiv.symm ((trace_r09 25).stage.apply regs)) (applyContext (trace_r09 25).stores ctx))
  · exact apply_position_advance_step caller (.seek .right) (trace_r09 26).stores ((trace_r09 26).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .right) (trace_r09 27).stores ((trace_r09 27).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .right) (trace_r09 28).stores ((trace_r09 28).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (trace_r09 29).stores ((trace_r09 29).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (trace_r09 30).stores ((trace_r09 30).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_r09 31).stores ((trace_r09 31).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_r09 32).stores ((trace_r09 32).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_r09 33).stores 15 [] rfl ((trace_r09 33).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r09 34).stores ((trace_r09 34).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r09 34).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r09 34).stores.certificate) (fuelContext (trace_r09 34).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r09 35).stores ((trace_r09 35).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_r09 35).stage.apply regs) (FuelDispatchMachine.stores ((trace_r09 35).stores.certificate) (fuelContext (trace_r09 35).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r09 36).stores ((trace_r09 36).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r09 37).stores ((trace_r09 37).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r09 37).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r09 37).stores) (applyContext (trace_r09 37).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_r09 38).stores ((trace_r09 38).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_r09 38).stores)
        (applyRegisterEquiv.symm ((trace_r09 38).stage.apply regs)) (applyContext (trace_r09 38).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_r09 39).stores ((trace_r09 39).stage.apply regs) ctx

theorem trace_r10_steps (n : Nat) (bound : n < 20) :
    step caller ((trace_r10 n).reached regs ctx) =
      some ((trace_r10 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_r10 0).stores 6 [10] rfl ((trace_r10 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r10 1).stores ((trace_r10 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r10 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r10 1).stores.certificate) (fuelContext (trace_r10 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r10 2).stores ((trace_r10 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r10 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_r10 2).stores.certificate) (fuelContext (trace_r10 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r10 3).stores ((trace_r10 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r10 4).stores ((trace_r10 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [.right] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r10 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r10 4).stores) (applyContext (trace_r10 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_r10 5).stores ((trace_r10 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.right] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r10 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r10 5).stores) (applyContext (trace_r10 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_r10 6).stores ((trace_r10 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .right [] [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r10 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r10 6).stores) (applyContext (trace_r10 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_r10 7).stores ((trace_r10 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.right, .left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r10 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r10 7).stores) (applyContext (trace_r10 7).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_r10 8).stores ((trace_r10 8).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_r10 8).stores)
        (applyRegisterEquiv.symm ((trace_r10 8).stage.apply regs)) (applyContext (trace_r10 8).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_r10 9).stores ((trace_r10 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanPrefix .left) (trace_r10 10).stores ((trace_r10 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_r10 11).stores ((trace_r10 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_r10 12).stores ((trace_r10 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_r10 13).stores ((trace_r10 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (trace_r10 14).stores ((trace_r10 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_r10 15).stores ((trace_r10 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_r10 16).stores ((trace_r10 16).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_r10 17).stores ((trace_r10 17).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_r10 18).stores ((trace_r10 18).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (trace_r10 19).stores ((trace_r10 19).stage.apply regs) ctx

end LiteralTraceEdges


end Examples.RotationCertificateStreamMachine
