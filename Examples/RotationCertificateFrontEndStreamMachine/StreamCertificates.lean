import Examples.RotationCertificateFrontEndStreamMachine.Boundaries

/-!
# RotationCertificateFrontEndStreamMachine: StreamCertificates
-/


namespace Examples.RotationCertificateFrontEndStreamMachine.StreamCertificates

open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.StreamMachine
open Examples.RotationCertificateStreamMachine

/-! Small Stream certificates for fixed closed-controller segments.
Each adjacent configuration is checked against the actual existing S program.
The expected endpoints and peaks were fixed before this certificate derivation. -/

def segment_v02 : RunFixture where
  name := "closed-controller/segment_v02"
  phase := inspectPhase
  before := data [] [] [] [0] [] [] [] [] [1, 0, 0]
  result := false
  after := data [] [] [] [] [] [] [] [] [0, 0]
  ticks := 4
  peak := 4

def trace_segment_v02 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [0] [] [] [] [] [1, 0, 0], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [0] [] [] [] [] [1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [] [1, 0, 0], .complete⟩
  | 3 => ⟨.inl (equalityJoinPhase .different), data [] [] [] [] [] [] [] [] [0, 0], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [] [] [] [] [] [0, 0], .complete⟩

def segment_v07 : RunFixture where
  name := "closed-controller/segment_v07"
  phase := inspectPhase
  before := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0]
  result := false
  after := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0]
  ticks := 8
  peak := 14

def trace_segment_v07 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 0, 1, 0, 0], .fuel⟩
  | 5 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 6 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .fuel⟩
  | 7 => ⟨.inl (fuelJoinPhase .zero), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .fuel⟩
  | _ => ⟨.inr false, data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩

def segment_v08 : RunFixture where
  name := "closed-controller/segment_v08"
  phase := inspectPhase
  before := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false, false] [1, 1, 0, 0, 0]
  result := true
  after := data [] [] [] [] [] [] [] [false, false, false] []
  ticks := 25
  peak := 15

def trace_segment_v08 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false, false] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false, false] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [] [] [] [0, 1, 0, 0] [] [] [()] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [] [] [] [1, 0, 0] [] [0] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0] [] [0] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (inspectPhase), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0, 0] [] [] [] [false, false, false] [1, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0] [] [] [] [false, false, false] [0, 0, 0], .complete⟩
  | 21 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false, false, false] [0, 0], .complete⟩
  | 22 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false, false, false] [0], .complete⟩
  | 23 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false, false, false] [], .complete⟩
  | 24 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false, false, false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false, false, false] [], .complete⟩

def segment_v09 : RunFixture where
  name := "closed-controller/segment_v09"
  phase := inspectPhase
  before := data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0]
  result := false
  after := data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0]
  ticks := 9
  peak := 12

def trace_segment_v09 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.undo .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩

def segment_v10 : RunFixture where
  name := "closed-controller/segment_v10"
  phase := inspectPhase
  before := data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0]
  result := false
  after := data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0]
  ticks := 9
  peak := 14

def trace_segment_v10 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.undo .left))), data [15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩

def segment_v11 : RunFixture where
  name := "closed-controller/segment_v11"
  phase := inspectPhase
  before := data [6, 8, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0]
  result := false
  after := data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0]
  ticks := 17
  peak := 14

def trace_segment_v11 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 8, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 8, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 8, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 8, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 8, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [8, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [.left] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.left] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [0, 1, 0, 0] [1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [0, 1, 0, 0] [1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .dropPending)), data [] [] [] [0, 1, 0, 0] [1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [] [0, 1, 0, 0] [1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyJoinPhase MoveApplyMachine.rotationFailure), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩

def segment_v12 : RunFixture where
  name := "closed-controller/segment_v12"
  phase := inspectPhase
  before := data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0]
  result := false
  after := data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0]
  ticks := 13
  peak := 13

def trace_segment_v12 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .right))), data [10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .right))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .right))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .right))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .right))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .dropPending)), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyJoinPhase MoveApplyMachine.rotationFailure), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩

def segment_v15 : RunFixture where
  name := "closed-controller/segment_v15"
  phase := inspectPhase
  before := data [] [] [] [0] [] [] [] [false, false] [0]
  result := true
  after := data [] [] [] [] [] [] [] [false, false] []
  ticks := 5
  peak := 4

def trace_segment_v15 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [0] [] [] [] [false, false] [0], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [0] [] [] [] [false, false] [0], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false, false] [0], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false, false] [], .complete⟩
  | 4 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false, false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false, false] [], .complete⟩

def segment_v16 : RunFixture where
  name := "closed-controller/segment_v16"
  phase := inspectPhase
  before := data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0]
  result := false
  after := data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0]
  ticks := 7
  peak := 12

def trace_segment_v16 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩

def segment_v18 : RunFixture where
  name := "closed-controller/segment_v18"
  phase := inspectPhase
  before := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0]
  result := false
  after := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0]
  ticks := 4
  peak := 12

def trace_segment_v18 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .zero), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0], .fuel⟩
  | _ => ⟨.inr false, data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0], .complete⟩

def segment_j03 : RunFixture where
  name := "closed-controller/segment_j03"
  phase := inspectPhase
  before := data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] []
  result := true
  after := data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] []
  ticks := 4
  peak := 8

def trace_segment_j03 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .complete⟩
  | 3 => ⟨.inl (equalityJoinPhase .equal), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .complete⟩
  | _ => ⟨.inr true, data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .complete⟩

def segment_d02 : RunFixture where
  name := "closed-controller/segment_d02"
  phase := inspectPhase
  before := data [6, 9, 10] [.right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 1, 0, 0, 0]
  result := false
  after := data [] [] [.right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0]
  ticks := 18
  peak := 22

def trace_segment_d02 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 9, 10] [.right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 9, 10] [.right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 9, 10] [.right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 9, 10] [.right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 9, 10] [.right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [9, 10] [.right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [.right, .right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.right, .right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.right, .left] [.right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.left] [.right, .right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [.left, .right, .right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [.left, .right, .right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.left, .right, .right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.right, .right, .left, .right] [0, 1, 0, 1, 0, 0] [1] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .dropPending)), data [] [] [.right, .left, .right] [0, 1, 0, 1, 0, 0] [1] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [.right, .left, .right] [0, 1, 0, 1, 0, 0] [1] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [.right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyJoinPhase MoveApplyMachine.rotationFailure), data [] [] [.right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [] [] [.right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩

section ActualEdges
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem trace_segment_v02_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_segment_v02 n).reached regs ctx) =
      some ((trace_segment_v02 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_segment_v02 0).stores rfl ((trace_segment_v02 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_segment_v02 1).stores ((trace_segment_v02 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v02 2).stores ((trace_segment_v02 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_different (fun _ => .halt) 0 1 [] [0, 0] (equalityRegisterEquiv.symm ((trace_segment_v02 2).stage.apply regs)) (equalityContext (trace_segment_v02 2).stores ctx) (by decide))
  · exact equality_join_step caller .different (trace_segment_v02 3).stores ((trace_segment_v02 3).stage.apply regs) ctx

theorem trace_segment_v07_steps (n : Nat) (bound : n < 8) :
    step caller ((trace_segment_v07 n).reached regs ctx) =
      some ((trace_segment_v07 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_v07 0).stores 6 [10] rfl ((trace_segment_v07 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v07 1).stores ((trace_segment_v07 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_segment_v07 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v07 1).stores.certificate) (fuelContext (trace_segment_v07 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v07 2).stores ((trace_segment_v07 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_v07 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_segment_v07 2).stores.certificate) (fuelContext (trace_segment_v07 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v07 3).stores ((trace_segment_v07 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_segment_v07 3).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((trace_segment_v07 3).stores.certificate) (fuelContext (trace_segment_v07 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_segment_v07 4).stores ((trace_segment_v07 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_v07 4).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_segment_v07 4).stores.certificate) (fuelContext (trace_segment_v07 4).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_segment_v07 5).stores ((trace_segment_v07 5).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_segment_v07 5).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v07 5).stores.certificate) (fuelContext (trace_segment_v07 5).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_segment_v07 6).stores ((trace_segment_v07 6).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_segment_v07 6).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_v07 6).stores.certificate) (fuelContext (trace_segment_v07 6).stores ctx)))
  · exact fuel_join_step caller .zero (trace_segment_v07 7).stores ((trace_segment_v07 7).stage.apply regs) ctx

theorem trace_segment_v08_steps (n : Nat) (bound : n < 25) :
    step caller ((trace_segment_v08 n).reached regs ctx) =
      some ((trace_segment_v08 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_v08 0).stores 6 [10] rfl ((trace_segment_v08 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v08 1).stores ((trace_segment_v08 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_segment_v08 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v08 1).stores.certificate) (fuelContext (trace_segment_v08 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_segment_v08 2).stores ((trace_segment_v08 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false, false] ((trace_segment_v08 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_v08 2).stores.certificate) (fuelContext (trace_segment_v08 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_segment_v08 3).stores ((trace_segment_v08 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_segment_v08 4).stores ((trace_segment_v08 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v08 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v08 4).stores) (applyContext (trace_segment_v08 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_segment_v08 5).stores ((trace_segment_v08 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v08 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v08 5).stores) (applyContext (trace_segment_v08 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_segment_v08 6).stores ((trace_segment_v08 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v08 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v08 6).stores) (applyContext (trace_segment_v08 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_segment_v08 7).stores ((trace_segment_v08 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_segment_v08 7).stores)
        (applyRegisterEquiv.symm ((trace_segment_v08 7).stage.apply regs)) (applyContext (trace_segment_v08 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_segment_v08 8).stores ((trace_segment_v08 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_segment_v08 9).stores ((trace_segment_v08 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_segment_v08 10).stores ((trace_segment_v08 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_segment_v08 11).stores ((trace_segment_v08 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_segment_v08 12).stores ((trace_segment_v08 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_segment_v08 13).stores ((trace_segment_v08 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_segment_v08 14).stores ((trace_segment_v08 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_segment_v08 15).stores ((trace_segment_v08 15).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_segment_v08 16).stores rfl ((trace_segment_v08 16).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_segment_v08 17).stores ((trace_segment_v08 17).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v08 18).stores ((trace_segment_v08 18).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0] [1, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_segment_v08 18).stage.apply regs)) (equalityContext (trace_segment_v08 18).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v08 19).stores ((trace_segment_v08 19).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((trace_segment_v08 19).stage.apply regs)) (equalityContext (trace_segment_v08 19).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v08 20).stores ((trace_segment_v08 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_segment_v08 20).stage.apply regs)) (equalityContext (trace_segment_v08 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v08 21).stores ((trace_segment_v08 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_segment_v08 21).stage.apply regs)) (equalityContext (trace_segment_v08 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v08 22).stores ((trace_segment_v08 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_segment_v08 22).stage.apply regs)) (equalityContext (trace_segment_v08 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v08 23).stores ((trace_segment_v08 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_segment_v08 23).stage.apply regs)) (equalityContext (trace_segment_v08 23).stores ctx))
  · exact equality_join_step caller .equal (trace_segment_v08 24).stores ((trace_segment_v08 24).stage.apply regs) ctx

theorem trace_segment_v09_steps (n : Nat) (bound : n < 9) :
    step caller ((trace_segment_v09 n).reached regs ctx) =
      some ((trace_segment_v09 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_v09 0).stores 6 [] rfl ((trace_segment_v09 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v09 1).stores ((trace_segment_v09 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_v09 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v09 1).stores.certificate) (fuelContext (trace_segment_v09 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_segment_v09 2).stores ((trace_segment_v09 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_segment_v09 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_v09 2).stores.certificate) (fuelContext (trace_segment_v09 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_segment_v09 3).stores ((trace_segment_v09 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_segment_v09 4).stores ((trace_segment_v09 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v09 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v09 4).stores) (applyContext (trace_segment_v09 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_segment_v09 5).stores ((trace_segment_v09 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v09 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v09 5).stores) (applyContext (trace_segment_v09 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (trace_segment_v09 6).stores ((trace_segment_v09 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v09 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v09 6).stores) (applyContext (trace_segment_v09 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_segment_v09 7).stores ((trace_segment_v09 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_segment_v09 7).stores)
        (applyRegisterEquiv.symm ((trace_segment_v09 7).stage.apply regs)) (applyContext (trace_segment_v09 7).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_segment_v09 8).stores ((trace_segment_v09 8).stage.apply regs) ctx

theorem trace_segment_v10_steps (n : Nat) (bound : n < 9) :
    step caller ((trace_segment_v10 n).reached regs ctx) =
      some ((trace_segment_v10 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_v10 0).stores 6 [15, 10] rfl ((trace_segment_v10 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v10 1).stores ((trace_segment_v10 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_v10 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v10 1).stores.certificate) (fuelContext (trace_segment_v10 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_segment_v10 2).stores ((trace_segment_v10 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_segment_v10 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_v10 2).stores.certificate) (fuelContext (trace_segment_v10 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_segment_v10 3).stores ((trace_segment_v10 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_segment_v10 4).stores ((trace_segment_v10 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [15, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v10 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v10 4).stores) (applyContext (trace_segment_v10 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_segment_v10 5).stores ((trace_segment_v10 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_foreign (fun _ => .halt) .left 15 [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v10 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v10 5).stores) (applyContext (trace_segment_v10 5).stores ctx)) (by decide) (by decide) (by decide))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (trace_segment_v10 6).stores ((trace_segment_v10 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_nil (fun _ => .halt) .left [15, 10] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v10 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v10 6).stores) (applyContext (trace_segment_v10 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_segment_v10 7).stores ((trace_segment_v10 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_segment_v10 7).stores)
        (applyRegisterEquiv.symm ((trace_segment_v10 7).stage.apply regs)) (applyContext (trace_segment_v10 7).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_segment_v10 8).stores ((trace_segment_v10 8).stage.apply regs) ctx

theorem trace_segment_v11_steps (n : Nat) (bound : n < 17) :
    step caller ((trace_segment_v11 n).reached regs ctx) =
      some ((trace_segment_v11 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_v11 0).stores 6 [8, 10] rfl ((trace_segment_v11 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v11 1).stores ((trace_segment_v11 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_v11 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v11 1).stores.certificate) (fuelContext (trace_segment_v11 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_segment_v11 2).stores ((trace_segment_v11 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_segment_v11 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_v11 2).stores.certificate) (fuelContext (trace_segment_v11 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_segment_v11 3).stores ((trace_segment_v11 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_segment_v11 4).stores ((trace_segment_v11 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [8, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v11 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v11 4).stores) (applyContext (trace_segment_v11 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_segment_v11 5).stores ((trace_segment_v11 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v11 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v11 5).stores) (applyContext (trace_segment_v11 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_segment_v11 6).stores ((trace_segment_v11 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v11 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v11 6).stores) (applyContext (trace_segment_v11 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_segment_v11 7).stores ((trace_segment_v11 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v11 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v11 7).stores) (applyContext (trace_segment_v11 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_segment_v11 8).stores ((trace_segment_v11 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v11 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v11 8).stores) (applyContext (trace_segment_v11 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_segment_v11 9).stores ((trace_segment_v11 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_segment_v11 9).stores)
        (applyRegisterEquiv.symm ((trace_segment_v11 9).stage.apply regs)) (applyContext (trace_segment_v11 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_segment_v11 10).stores ((trace_segment_v11 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_segment_v11 11).stores ((trace_segment_v11 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_segment_v11 12).stores ((trace_segment_v11 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (trace_segment_v11 13).stores ((trace_segment_v11 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_segment_v11 14).stores ((trace_segment_v11 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_segment_v11 15).stores ((trace_segment_v11 15).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (trace_segment_v11 16).stores ((trace_segment_v11 16).stage.apply regs) ctx

theorem trace_segment_v12_steps (n : Nat) (bound : n < 13) :
    step caller ((trace_segment_v12 n).reached regs ctx) =
      some ((trace_segment_v12 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_v12 0).stores 7 [10] rfl ((trace_segment_v12 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v12 1).stores ((trace_segment_v12 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_v12 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v12 1).stores.certificate) (fuelContext (trace_segment_v12 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_segment_v12 2).stores ((trace_segment_v12 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_segment_v12 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_v12 2).stores.certificate) (fuelContext (trace_segment_v12 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_segment_v12 3).stores ((trace_segment_v12 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_segment_v12 4).stores ((trace_segment_v12 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .right [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v12 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v12 4).stores) (applyContext (trace_segment_v12 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .right) (trace_segment_v12 5).stores ((trace_segment_v12 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .right [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v12 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v12 5).stores) (applyContext (trace_segment_v12 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .right) (trace_segment_v12 6).stores ((trace_segment_v12 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .right [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v12 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v12 6).stores) (applyContext (trace_segment_v12 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .right)) (trace_segment_v12 7).stores ((trace_segment_v12 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .right) (applyData (trace_segment_v12 7).stores)
        (applyRegisterEquiv.symm ((trace_segment_v12 7).stage.apply regs)) (applyContext (trace_segment_v12 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .right) (trace_segment_v12 8).stores ((trace_segment_v12 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .right) (trace_segment_v12 9).stores ((trace_segment_v12 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (trace_segment_v12 10).stores ((trace_segment_v12 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_segment_v12 11).stores ((trace_segment_v12 11).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (trace_segment_v12 12).stores ((trace_segment_v12 12).stage.apply regs) ctx

theorem trace_segment_v15_steps (n : Nat) (bound : n < 5) :
    step caller ((trace_segment_v15 n).reached regs ctx) =
      some ((trace_segment_v15 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_segment_v15 0).stores rfl ((trace_segment_v15 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_segment_v15 1).stores ((trace_segment_v15 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v15 2).stores ((trace_segment_v15 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_segment_v15 2).stage.apply regs)) (equalityContext (trace_segment_v15 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v15 3).stores ((trace_segment_v15 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_segment_v15 3).stage.apply regs)) (equalityContext (trace_segment_v15 3).stores ctx))
  · exact equality_join_step caller .equal (trace_segment_v15 4).stores ((trace_segment_v15 4).stage.apply regs) ctx

theorem trace_segment_v16_steps (n : Nat) (bound : n < 7) :
    step caller ((trace_segment_v16 n).reached regs ctx) =
      some ((trace_segment_v16 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_v16 0).stores 15 [] rfl ((trace_segment_v16 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v16 1).stores ((trace_segment_v16 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_v16 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v16 1).stores.certificate) (fuelContext (trace_segment_v16 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_segment_v16 2).stores ((trace_segment_v16 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_segment_v16 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_v16 2).stores.certificate) (fuelContext (trace_segment_v16 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_segment_v16 3).stores ((trace_segment_v16 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_segment_v16 4).stores ((trace_segment_v16 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v16 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v16 4).stores) (applyContext (trace_segment_v16 4).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_segment_v16 5).stores ((trace_segment_v16 5).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_segment_v16 5).stores)
        (applyRegisterEquiv.symm ((trace_segment_v16 5).stage.apply regs)) (applyContext (trace_segment_v16 5).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_segment_v16 6).stores ((trace_segment_v16 6).stage.apply regs) ctx

theorem trace_segment_v18_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_segment_v18 n).reached regs ctx) =
      some ((trace_segment_v18 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_v18 0).stores 6 [10] rfl ((trace_segment_v18 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v18 1).stores ((trace_segment_v18 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_segment_v18 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v18 1).stores.certificate) (fuelContext (trace_segment_v18 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_segment_v18 2).stores ((trace_segment_v18 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_v18 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_v18 2).stores.certificate) (fuelContext (trace_segment_v18 2).stores ctx)))
  · exact fuel_join_step caller .zero (trace_segment_v18 3).stores ((trace_segment_v18 3).stage.apply regs) ctx

theorem trace_segment_j03_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_segment_j03 n).reached regs ctx) =
      some ((trace_segment_j03 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_segment_j03 0).stores rfl ((trace_segment_j03 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_segment_j03 1).stores ((trace_segment_j03 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_j03 2).stores ((trace_segment_j03 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_segment_j03 2).stage.apply regs)) (equalityContext (trace_segment_j03 2).stores ctx))
  · exact equality_join_step caller .equal (trace_segment_j03 3).stores ((trace_segment_j03 3).stage.apply regs) ctx

theorem trace_segment_d02_steps (n : Nat) (bound : n < 18) :
    step caller ((trace_segment_d02 n).reached regs ctx) =
      some ((trace_segment_d02 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_d02 0).stores 6 [9, 10] rfl ((trace_segment_d02 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_d02 1).stores ((trace_segment_d02 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_d02 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_d02 1).stores.certificate) (fuelContext (trace_segment_d02 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_segment_d02 2).stores ((trace_segment_d02 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_segment_d02 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_d02 2).stores.certificate) (fuelContext (trace_segment_d02 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_segment_d02 3).stores ((trace_segment_d02 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_segment_d02 4).stores ((trace_segment_d02 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [9, 10] [.right, .left] [.left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_d02 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_d02 4).stores) (applyContext (trace_segment_d02 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_segment_d02 5).stores ((trace_segment_d02 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .right [10] [.right, .left] [.left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_d02 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_d02 5).stores) (applyContext (trace_segment_d02 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_segment_d02 6).stores ((trace_segment_d02 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.right, .right, .left] [.left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_d02 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_d02 6).stores) (applyContext (trace_segment_d02 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_segment_d02 7).stores ((trace_segment_d02 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .right [] [.right, .left] [.left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_d02 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_d02 7).stores) (applyContext (trace_segment_d02 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_segment_d02 8).stores ((trace_segment_d02 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .right [] [.left] [.right, .left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_d02 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_d02 8).stores) (applyContext (trace_segment_d02 8).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_segment_d02 9).stores ((trace_segment_d02 9).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [] [.right, .right, .left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_d02 9).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_d02 9).stores) (applyContext (trace_segment_d02 9).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_segment_d02 10).stores ((trace_segment_d02 10).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left, .right, .right, .left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_d02 10).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_d02 10).stores) (applyContext (trace_segment_d02 10).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_segment_d02 11).stores ((trace_segment_d02 11).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_segment_d02 11).stores)
        (applyRegisterEquiv.symm ((trace_segment_d02 11).stage.apply regs)) (applyContext (trace_segment_d02 11).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_segment_d02 12).stores ((trace_segment_d02 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_segment_d02 13).stores ((trace_segment_d02 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (trace_segment_d02 14).stores ((trace_segment_d02 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_segment_d02 15).stores ((trace_segment_d02 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_segment_d02 16).stores ((trace_segment_d02 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (trace_segment_d02 17).stores ((trace_segment_d02 17).stage.apply regs) ctx

end ActualEdges

theorem trace_segment_v02_owned (n : Nat) (bound : n < 4) :
    (trace_segment_v02 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v02_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_segment_v02 n).stores ≤ 4 := by
  interval_cases n <;> decide

theorem segment_v02_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v02.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v02 trace_segment_v02 rfl rfl
    (trace_segment_v02_steps caller regs ctx) trace_segment_v02_owned

theorem segment_v02_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v02.start regs ctx)
      segment_v02.ticks (segment_v02.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v02
    4 4 (trace_segment_v02_steps caller regs ctx) trace_segment_v02_cells rfl

theorem trace_segment_v07_owned (n : Nat) (bound : n < 8) :
    (trace_segment_v07 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v07_cells (n : Nat) (bound : n ≤ 8) :
    fixtureCells (trace_segment_v07 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem segment_v07_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v07.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v07 trace_segment_v07 rfl rfl
    (trace_segment_v07_steps caller regs ctx) trace_segment_v07_owned

theorem segment_v07_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v07.start regs ctx)
      segment_v07.ticks (segment_v07.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v07
    8 14 (trace_segment_v07_steps caller regs ctx) trace_segment_v07_cells rfl

theorem trace_segment_v08_owned (n : Nat) (bound : n < 25) :
    (trace_segment_v08 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v08_cells (n : Nat) (bound : n ≤ 25) :
    fixtureCells (trace_segment_v08 n).stores ≤ 15 := by
  interval_cases n <;> decide

theorem segment_v08_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v08.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v08 trace_segment_v08 rfl rfl
    (trace_segment_v08_steps caller regs ctx) trace_segment_v08_owned

theorem segment_v08_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v08.start regs ctx)
      segment_v08.ticks (segment_v08.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v08
    25 15 (trace_segment_v08_steps caller regs ctx) trace_segment_v08_cells rfl

theorem trace_segment_v09_owned (n : Nat) (bound : n < 9) :
    (trace_segment_v09 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v09_cells (n : Nat) (bound : n ≤ 9) :
    fixtureCells (trace_segment_v09 n).stores ≤ 12 := by
  interval_cases n <;> decide

theorem segment_v09_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v09.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v09 trace_segment_v09 rfl rfl
    (trace_segment_v09_steps caller regs ctx) trace_segment_v09_owned

theorem segment_v09_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v09.start regs ctx)
      segment_v09.ticks (segment_v09.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v09
    9 12 (trace_segment_v09_steps caller regs ctx) trace_segment_v09_cells rfl

theorem trace_segment_v10_owned (n : Nat) (bound : n < 9) :
    (trace_segment_v10 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v10_cells (n : Nat) (bound : n ≤ 9) :
    fixtureCells (trace_segment_v10 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem segment_v10_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v10.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v10 trace_segment_v10 rfl rfl
    (trace_segment_v10_steps caller regs ctx) trace_segment_v10_owned

theorem segment_v10_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v10.start regs ctx)
      segment_v10.ticks (segment_v10.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v10
    9 14 (trace_segment_v10_steps caller regs ctx) trace_segment_v10_cells rfl

theorem trace_segment_v11_owned (n : Nat) (bound : n < 17) :
    (trace_segment_v11 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v11_cells (n : Nat) (bound : n ≤ 17) :
    fixtureCells (trace_segment_v11 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem segment_v11_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v11.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v11 trace_segment_v11 rfl rfl
    (trace_segment_v11_steps caller regs ctx) trace_segment_v11_owned

theorem segment_v11_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v11.start regs ctx)
      segment_v11.ticks (segment_v11.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v11
    17 14 (trace_segment_v11_steps caller regs ctx) trace_segment_v11_cells rfl

theorem trace_segment_v12_owned (n : Nat) (bound : n < 13) :
    (trace_segment_v12 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v12_cells (n : Nat) (bound : n ≤ 13) :
    fixtureCells (trace_segment_v12 n).stores ≤ 13 := by
  interval_cases n <;> decide

theorem segment_v12_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v12.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v12 trace_segment_v12 rfl rfl
    (trace_segment_v12_steps caller regs ctx) trace_segment_v12_owned

theorem segment_v12_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v12.start regs ctx)
      segment_v12.ticks (segment_v12.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v12
    13 13 (trace_segment_v12_steps caller regs ctx) trace_segment_v12_cells rfl

theorem trace_segment_v15_owned (n : Nat) (bound : n < 5) :
    (trace_segment_v15 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v15_cells (n : Nat) (bound : n ≤ 5) :
    fixtureCells (trace_segment_v15 n).stores ≤ 4 := by
  interval_cases n <;> decide

theorem segment_v15_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v15.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v15 trace_segment_v15 rfl rfl
    (trace_segment_v15_steps caller regs ctx) trace_segment_v15_owned

theorem segment_v15_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v15.start regs ctx)
      segment_v15.ticks (segment_v15.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v15
    5 4 (trace_segment_v15_steps caller regs ctx) trace_segment_v15_cells rfl

theorem trace_segment_v16_owned (n : Nat) (bound : n < 7) :
    (trace_segment_v16 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v16_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (trace_segment_v16 n).stores ≤ 12 := by
  interval_cases n <;> decide

theorem segment_v16_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v16.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v16 trace_segment_v16 rfl rfl
    (trace_segment_v16_steps caller regs ctx) trace_segment_v16_owned

theorem segment_v16_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v16.start regs ctx)
      segment_v16.ticks (segment_v16.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v16
    7 12 (trace_segment_v16_steps caller regs ctx) trace_segment_v16_cells rfl

theorem trace_segment_v18_owned (n : Nat) (bound : n < 4) :
    (trace_segment_v18 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v18_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_segment_v18 n).stores ≤ 12 := by
  interval_cases n <;> decide

theorem segment_v18_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v18.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v18 trace_segment_v18 rfl rfl
    (trace_segment_v18_steps caller regs ctx) trace_segment_v18_owned

theorem segment_v18_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v18.start regs ctx)
      segment_v18.ticks (segment_v18.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v18
    4 12 (trace_segment_v18_steps caller regs ctx) trace_segment_v18_cells rfl

theorem trace_segment_j03_owned (n : Nat) (bound : n < 4) :
    (trace_segment_j03 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_j03_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_segment_j03 n).stores ≤ 8 := by
  interval_cases n <;> decide

theorem segment_j03_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_j03.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_j03 trace_segment_j03 rfl rfl
    (trace_segment_j03_steps caller regs ctx) trace_segment_j03_owned

theorem segment_j03_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_j03.start regs ctx)
      segment_j03.ticks (segment_j03.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_j03
    4 8 (trace_segment_j03_steps caller regs ctx) trace_segment_j03_cells rfl

theorem trace_segment_d02_owned (n : Nat) (bound : n < 18) :
    (trace_segment_d02 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_d02_cells (n : Nat) (bound : n ≤ 18) :
    fixtureCells (trace_segment_d02 n).stores ≤ 22 := by
  interval_cases n <;> decide

theorem segment_d02_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_d02.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_d02 trace_segment_d02 rfl rfl
    (trace_segment_d02_steps caller regs ctx) trace_segment_d02_owned

theorem segment_d02_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_d02.start regs ctx)
      segment_d02.ticks (segment_d02.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_d02
    18 22 (trace_segment_d02_steps caller regs ctx) trace_segment_d02_cells rfl

end Examples.RotationCertificateFrontEndStreamMachine.StreamCertificates

