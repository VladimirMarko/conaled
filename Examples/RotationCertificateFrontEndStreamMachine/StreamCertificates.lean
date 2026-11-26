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

def segmentV02 : RunFixture where
  name := "closed-controller/segment_v02"
  phase := inspectPhase
  before := data [] [] [] [0] [] [] [] [] [1, 0, 0]
  result := false
  after := data [] [] [] [] [] [] [] [] [0, 0]
  ticks := 4
  peak := 4

def traceSegmentV02 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [0] [] [] [] [] [1, 0, 0], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [0] [] [] [] [] [1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [] [1, 0, 0], .complete⟩
  | 3 => ⟨.inl (equalityJoinPhase .different), data [] [] [] [] [] [] [] [] [0, 0], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [] [] [] [] [] [0, 0], .complete⟩

def segmentV07 : RunFixture where
  name := "closed-controller/segment_v07"
  phase := inspectPhase
  before := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0]
  result := false
  after := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0]
  ticks := 8
  peak := 14

def traceSegmentV07 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 0, 1, 0, 0], .fuel⟩
  | 5 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 6 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .fuel⟩
  | 7 => ⟨.inl (fuelJoinPhase .zero), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .fuel⟩
  | _ => ⟨.inr false, data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩

def segmentV08 : RunFixture where
  name := "closed-controller/segment_v08"
  phase := inspectPhase
  before := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false, false] [1, 1, 0, 0, 0]
  result := true
  after := data [] [] [] [] [] [] [] [false, false, false] []
  ticks := 25
  peak := 15

def traceSegmentV08 : Nat → TracePoint
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

def segmentV09 : RunFixture where
  name := "closed-controller/segment_v09"
  phase := inspectPhase
  before := data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0]
  result := false
  after := data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0]
  ticks := 9
  peak := 12

def traceSegmentV09 : Nat → TracePoint
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

def segmentV10 : RunFixture where
  name := "closed-controller/segment_v10"
  phase := inspectPhase
  before := data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0]
  result := false
  after := data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0]
  ticks := 9
  peak := 14

def traceSegmentV10 : Nat → TracePoint
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

def segmentV11 : RunFixture where
  name := "closed-controller/segment_v11"
  phase := inspectPhase
  before := data [6, 8, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0]
  result := false
  after := data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0]
  ticks := 17
  peak := 14

def traceSegmentV11 : Nat → TracePoint
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

def segmentV12 : RunFixture where
  name := "closed-controller/segment_v12"
  phase := inspectPhase
  before := data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0]
  result := false
  after := data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0]
  ticks := 13
  peak := 13

def traceSegmentV12 : Nat → TracePoint
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

def segmentV15 : RunFixture where
  name := "closed-controller/segment_v15"
  phase := inspectPhase
  before := data [] [] [] [0] [] [] [] [false, false] [0]
  result := true
  after := data [] [] [] [] [] [] [] [false, false] []
  ticks := 5
  peak := 4

def traceSegmentV15 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [0] [] [] [] [false, false] [0], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [0] [] [] [] [false, false] [0], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false, false] [0], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false, false] [], .complete⟩
  | 4 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false, false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false, false] [], .complete⟩

def segmentV16 : RunFixture where
  name := "closed-controller/segment_v16"
  phase := inspectPhase
  before := data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0]
  result := false
  after := data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0]
  ticks := 7
  peak := 12

def traceSegmentV16 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩

def segmentV18 : RunFixture where
  name := "closed-controller/segment_v18"
  phase := inspectPhase
  before := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0]
  result := false
  after := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0]
  ticks := 4
  peak := 12

def traceSegmentV18 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .zero), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0], .fuel⟩
  | _ => ⟨.inr false, data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0], .complete⟩

def segmentJ03 : RunFixture where
  name := "closed-controller/segment_j03"
  phase := inspectPhase
  before := data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] []
  result := true
  after := data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] []
  ticks := 4
  peak := 8

def traceSegmentJ03 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .complete⟩
  | 3 => ⟨.inl (equalityJoinPhase .equal), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .complete⟩
  | _ => ⟨.inr true, data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .complete⟩

def segmentD02 : RunFixture where
  name := "closed-controller/segment_d02"
  phase := inspectPhase
  before := data [6, 9, 10] [.right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 1, 0, 0, 0]
  result := false
  after := data [] [] [.right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0]
  ticks := 18
  peak := 22

def traceSegmentD02 : Nat → TracePoint
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

theorem traceSegmentV02_steps (n : Nat) (bound : n < 4) :
    step caller ((traceSegmentV02 n).reached regs ctx) =
      some ((traceSegmentV02 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (traceSegmentV02 0).stores rfl ((traceSegmentV02 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceSegmentV02 1).stores ((traceSegmentV02 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceSegmentV02 2).stores ((traceSegmentV02 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_different (fun _ => .halt) 0 1 [] [0, 0] (equalityRegisterEquiv.symm ((traceSegmentV02 2).stage.apply regs)) (equalityContext (traceSegmentV02 2).stores ctx) (by decide))
  · exact equality_join_step caller .different (traceSegmentV02 3).stores ((traceSegmentV02 3).stage.apply regs) ctx

theorem traceSegmentV07_steps (n : Nat) (bound : n < 8) :
    step caller ((traceSegmentV07 n).reached regs ctx) =
      some ((traceSegmentV07 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceSegmentV07 0).stores 6 [10] rfl ((traceSegmentV07 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceSegmentV07 1).stores ((traceSegmentV07 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceSegmentV07 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceSegmentV07 1).stores.certificate) (fuelContext (traceSegmentV07 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceSegmentV07 2).stores ((traceSegmentV07 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceSegmentV07 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceSegmentV07 2).stores.certificate) (fuelContext (traceSegmentV07 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceSegmentV07 3).stores ((traceSegmentV07 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((traceSegmentV07 3).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((traceSegmentV07 3).stores.certificate) (fuelContext (traceSegmentV07 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceSegmentV07 4).stores ((traceSegmentV07 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceSegmentV07 4).stage.apply regs) [()] (FuelDispatchMachine.stores ((traceSegmentV07 4).stores.certificate) (fuelContext (traceSegmentV07 4).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceSegmentV07 5).stores ((traceSegmentV07 5).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceSegmentV07 5).stage.apply regs) [] (FuelDispatchMachine.stores ((traceSegmentV07 5).stores.certificate) (fuelContext (traceSegmentV07 5).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceSegmentV07 6).stores ((traceSegmentV07 6).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((traceSegmentV07 6).stage.apply regs) (FuelDispatchMachine.stores ((traceSegmentV07 6).stores.certificate) (fuelContext (traceSegmentV07 6).stores ctx)))
  · exact fuel_join_step caller .zero (traceSegmentV07 7).stores ((traceSegmentV07 7).stage.apply regs) ctx

theorem traceSegmentV08_steps (n : Nat) (bound : n < 25) :
    step caller ((traceSegmentV08 n).reached regs ctx) =
      some ((traceSegmentV08 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceSegmentV08 0).stores 6 [10] rfl ((traceSegmentV08 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceSegmentV08 1).stores ((traceSegmentV08 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((traceSegmentV08 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceSegmentV08 1).stores.certificate) (fuelContext (traceSegmentV08 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceSegmentV08 2).stores ((traceSegmentV08 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false, false] ((traceSegmentV08 2).stage.apply regs) (FuelDispatchMachine.stores ((traceSegmentV08 2).stores.certificate) (fuelContext (traceSegmentV08 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceSegmentV08 3).stores ((traceSegmentV08 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceSegmentV08 4).stores ((traceSegmentV08 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV08 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV08 4).stores) (applyContext (traceSegmentV08 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceSegmentV08 5).stores ((traceSegmentV08 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV08 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV08 5).stores) (applyContext (traceSegmentV08 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceSegmentV08 6).stores ((traceSegmentV08 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV08 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV08 6).stores) (applyContext (traceSegmentV08 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceSegmentV08 7).stores ((traceSegmentV08 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceSegmentV08 7).stores)
        (applyRegisterEquiv.symm ((traceSegmentV08 7).stage.apply regs)) (applyContext (traceSegmentV08 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceSegmentV08 8).stores ((traceSegmentV08 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceSegmentV08 9).stores ((traceSegmentV08 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (traceSegmentV08 10).stores ((traceSegmentV08 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (traceSegmentV08 11).stores ((traceSegmentV08 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceSegmentV08 12).stores ((traceSegmentV08 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (traceSegmentV08 13).stores ((traceSegmentV08 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (traceSegmentV08 14).stores ((traceSegmentV08 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (traceSegmentV08 15).stores ((traceSegmentV08 15).stage.apply regs) ctx
  · exact inspect_step_nil caller (traceSegmentV08 16).stores rfl ((traceSegmentV08 16).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceSegmentV08 17).stores ((traceSegmentV08 17).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceSegmentV08 18).stores ((traceSegmentV08 18).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0] [1, 0, 0, 0] (equalityRegisterEquiv.symm ((traceSegmentV08 18).stage.apply regs)) (equalityContext (traceSegmentV08 18).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceSegmentV08 19).stores ((traceSegmentV08 19).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((traceSegmentV08 19).stage.apply regs)) (equalityContext (traceSegmentV08 19).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceSegmentV08 20).stores ((traceSegmentV08 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((traceSegmentV08 20).stage.apply regs)) (equalityContext (traceSegmentV08 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceSegmentV08 21).stores ((traceSegmentV08 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((traceSegmentV08 21).stage.apply regs)) (equalityContext (traceSegmentV08 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceSegmentV08 22).stores ((traceSegmentV08 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((traceSegmentV08 22).stage.apply regs)) (equalityContext (traceSegmentV08 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceSegmentV08 23).stores ((traceSegmentV08 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceSegmentV08 23).stage.apply regs)) (equalityContext (traceSegmentV08 23).stores ctx))
  · exact equality_join_step caller .equal (traceSegmentV08 24).stores ((traceSegmentV08 24).stage.apply regs) ctx

theorem traceSegmentV09_steps (n : Nat) (bound : n < 9) :
    step caller ((traceSegmentV09 n).reached regs ctx) =
      some ((traceSegmentV09 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceSegmentV09 0).stores 6 [] rfl ((traceSegmentV09 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceSegmentV09 1).stores ((traceSegmentV09 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceSegmentV09 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceSegmentV09 1).stores.certificate) (fuelContext (traceSegmentV09 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceSegmentV09 2).stores ((traceSegmentV09 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceSegmentV09 2).stage.apply regs) (FuelDispatchMachine.stores ((traceSegmentV09 2).stores.certificate) (fuelContext (traceSegmentV09 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceSegmentV09 3).stores ((traceSegmentV09 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceSegmentV09 4).stores ((traceSegmentV09 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV09 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV09 4).stores) (applyContext (traceSegmentV09 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceSegmentV09 5).stores ((traceSegmentV09 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV09 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV09 5).stores) (applyContext (traceSegmentV09 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (traceSegmentV09 6).stores ((traceSegmentV09 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV09 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV09 6).stores) (applyContext (traceSegmentV09 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (traceSegmentV09 7).stores ((traceSegmentV09 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (traceSegmentV09 7).stores)
        (applyRegisterEquiv.symm ((traceSegmentV09 7).stage.apply regs)) (applyContext (traceSegmentV09 7).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (traceSegmentV09 8).stores ((traceSegmentV09 8).stage.apply regs) ctx

theorem traceSegmentV10_steps (n : Nat) (bound : n < 9) :
    step caller ((traceSegmentV10 n).reached regs ctx) =
      some ((traceSegmentV10 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceSegmentV10 0).stores 6 [15, 10] rfl ((traceSegmentV10 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceSegmentV10 1).stores ((traceSegmentV10 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceSegmentV10 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceSegmentV10 1).stores.certificate) (fuelContext (traceSegmentV10 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceSegmentV10 2).stores ((traceSegmentV10 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceSegmentV10 2).stage.apply regs) (FuelDispatchMachine.stores ((traceSegmentV10 2).stores.certificate) (fuelContext (traceSegmentV10 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceSegmentV10 3).stores ((traceSegmentV10 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceSegmentV10 4).stores ((traceSegmentV10 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [15, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV10 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV10 4).stores) (applyContext (traceSegmentV10 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceSegmentV10 5).stores ((traceSegmentV10 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_foreign (fun _ => .halt) .left 15 [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV10 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV10 5).stores) (applyContext (traceSegmentV10 5).stores ctx)) (by decide) (by decide) (by decide))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (traceSegmentV10 6).stores ((traceSegmentV10 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_nil (fun _ => .halt) .left [15, 10] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV10 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV10 6).stores) (applyContext (traceSegmentV10 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (traceSegmentV10 7).stores ((traceSegmentV10 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (traceSegmentV10 7).stores)
        (applyRegisterEquiv.symm ((traceSegmentV10 7).stage.apply regs)) (applyContext (traceSegmentV10 7).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (traceSegmentV10 8).stores ((traceSegmentV10 8).stage.apply regs) ctx

theorem traceSegmentV11_steps (n : Nat) (bound : n < 17) :
    step caller ((traceSegmentV11 n).reached regs ctx) =
      some ((traceSegmentV11 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceSegmentV11 0).stores 6 [8, 10] rfl ((traceSegmentV11 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceSegmentV11 1).stores ((traceSegmentV11 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceSegmentV11 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceSegmentV11 1).stores.certificate) (fuelContext (traceSegmentV11 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceSegmentV11 2).stores ((traceSegmentV11 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceSegmentV11 2).stage.apply regs) (FuelDispatchMachine.stores ((traceSegmentV11 2).stores.certificate) (fuelContext (traceSegmentV11 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceSegmentV11 3).stores ((traceSegmentV11 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceSegmentV11 4).stores ((traceSegmentV11 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [8, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV11 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV11 4).stores) (applyContext (traceSegmentV11 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceSegmentV11 5).stores ((traceSegmentV11 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV11 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV11 5).stores) (applyContext (traceSegmentV11 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceSegmentV11 6).stores ((traceSegmentV11 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV11 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV11 6).stores) (applyContext (traceSegmentV11 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceSegmentV11 7).stores ((traceSegmentV11 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV11 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV11 7).stores) (applyContext (traceSegmentV11 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceSegmentV11 8).stores ((traceSegmentV11 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV11 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV11 8).stores) (applyContext (traceSegmentV11 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceSegmentV11 9).stores ((traceSegmentV11 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceSegmentV11 9).stores)
        (applyRegisterEquiv.symm ((traceSegmentV11 9).stage.apply regs)) (applyContext (traceSegmentV11 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceSegmentV11 10).stores ((traceSegmentV11 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (traceSegmentV11 11).stores ((traceSegmentV11 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (traceSegmentV11 12).stores ((traceSegmentV11 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (traceSegmentV11 13).stores ((traceSegmentV11 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (traceSegmentV11 14).stores ((traceSegmentV11 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (traceSegmentV11 15).stores ((traceSegmentV11 15).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (traceSegmentV11 16).stores ((traceSegmentV11 16).stage.apply regs) ctx

theorem traceSegmentV12_steps (n : Nat) (bound : n < 13) :
    step caller ((traceSegmentV12 n).reached regs ctx) =
      some ((traceSegmentV12 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceSegmentV12 0).stores 7 [10] rfl ((traceSegmentV12 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceSegmentV12 1).stores ((traceSegmentV12 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceSegmentV12 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceSegmentV12 1).stores.certificate) (fuelContext (traceSegmentV12 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceSegmentV12 2).stores ((traceSegmentV12 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceSegmentV12 2).stage.apply regs) (FuelDispatchMachine.stores ((traceSegmentV12 2).stores.certificate) (fuelContext (traceSegmentV12 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceSegmentV12 3).stores ((traceSegmentV12 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceSegmentV12 4).stores ((traceSegmentV12 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .right [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV12 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV12 4).stores) (applyContext (traceSegmentV12 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .right) (traceSegmentV12 5).stores ((traceSegmentV12 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .right [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV12 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV12 5).stores) (applyContext (traceSegmentV12 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .right) (traceSegmentV12 6).stores ((traceSegmentV12 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .right [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV12 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV12 6).stores) (applyContext (traceSegmentV12 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .right)) (traceSegmentV12 7).stores ((traceSegmentV12 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .right) (applyData (traceSegmentV12 7).stores)
        (applyRegisterEquiv.symm ((traceSegmentV12 7).stage.apply regs)) (applyContext (traceSegmentV12 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .right) (traceSegmentV12 8).stores ((traceSegmentV12 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .right) (traceSegmentV12 9).stores ((traceSegmentV12 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (traceSegmentV12 10).stores ((traceSegmentV12 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (traceSegmentV12 11).stores ((traceSegmentV12 11).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (traceSegmentV12 12).stores ((traceSegmentV12 12).stage.apply regs) ctx

theorem traceSegmentV15_steps (n : Nat) (bound : n < 5) :
    step caller ((traceSegmentV15 n).reached regs ctx) =
      some ((traceSegmentV15 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (traceSegmentV15 0).stores rfl ((traceSegmentV15 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceSegmentV15 1).stores ((traceSegmentV15 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceSegmentV15 2).stores ((traceSegmentV15 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((traceSegmentV15 2).stage.apply regs)) (equalityContext (traceSegmentV15 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (traceSegmentV15 3).stores ((traceSegmentV15 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceSegmentV15 3).stage.apply regs)) (equalityContext (traceSegmentV15 3).stores ctx))
  · exact equality_join_step caller .equal (traceSegmentV15 4).stores ((traceSegmentV15 4).stage.apply regs) ctx

theorem traceSegmentV16_steps (n : Nat) (bound : n < 7) :
    step caller ((traceSegmentV16 n).reached regs ctx) =
      some ((traceSegmentV16 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceSegmentV16 0).stores 15 [] rfl ((traceSegmentV16 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceSegmentV16 1).stores ((traceSegmentV16 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceSegmentV16 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceSegmentV16 1).stores.certificate) (fuelContext (traceSegmentV16 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceSegmentV16 2).stores ((traceSegmentV16 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceSegmentV16 2).stage.apply regs) (FuelDispatchMachine.stores ((traceSegmentV16 2).stores.certificate) (fuelContext (traceSegmentV16 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceSegmentV16 3).stores ((traceSegmentV16 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceSegmentV16 4).stores ((traceSegmentV16 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentV16 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentV16 4).stores) (applyContext (traceSegmentV16 4).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (traceSegmentV16 5).stores ((traceSegmentV16 5).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (traceSegmentV16 5).stores)
        (applyRegisterEquiv.symm ((traceSegmentV16 5).stage.apply regs)) (applyContext (traceSegmentV16 5).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (traceSegmentV16 6).stores ((traceSegmentV16 6).stage.apply regs) ctx

theorem traceSegmentV18_steps (n : Nat) (bound : n < 4) :
    step caller ((traceSegmentV18 n).reached regs ctx) =
      some ((traceSegmentV18 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceSegmentV18 0).stores 6 [10] rfl ((traceSegmentV18 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceSegmentV18 1).stores ((traceSegmentV18 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((traceSegmentV18 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceSegmentV18 1).stores.certificate) (fuelContext (traceSegmentV18 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (traceSegmentV18 2).stores ((traceSegmentV18 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceSegmentV18 2).stage.apply regs) (FuelDispatchMachine.stores ((traceSegmentV18 2).stores.certificate) (fuelContext (traceSegmentV18 2).stores ctx)))
  · exact fuel_join_step caller .zero (traceSegmentV18 3).stores ((traceSegmentV18 3).stage.apply regs) ctx

theorem traceSegmentJ03_steps (n : Nat) (bound : n < 4) :
    step caller ((traceSegmentJ03 n).reached regs ctx) =
      some ((traceSegmentJ03 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (traceSegmentJ03 0).stores rfl ((traceSegmentJ03 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (traceSegmentJ03 1).stores ((traceSegmentJ03 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (traceSegmentJ03 2).stores ((traceSegmentJ03 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((traceSegmentJ03 2).stage.apply regs)) (equalityContext (traceSegmentJ03 2).stores ctx))
  · exact equality_join_step caller .equal (traceSegmentJ03 3).stores ((traceSegmentJ03 3).stage.apply regs) ctx

theorem traceSegmentD02_steps (n : Nat) (bound : n < 18) :
    step caller ((traceSegmentD02 n).reached regs ctx) =
      some ((traceSegmentD02 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (traceSegmentD02 0).stores 6 [9, 10] rfl ((traceSegmentD02 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (traceSegmentD02 1).stores ((traceSegmentD02 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((traceSegmentD02 1).stage.apply regs) [] (FuelDispatchMachine.stores ((traceSegmentD02 1).stores.certificate) (fuelContext (traceSegmentD02 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (traceSegmentD02 2).stores ((traceSegmentD02 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((traceSegmentD02 2).stage.apply regs) (FuelDispatchMachine.stores ((traceSegmentD02 2).stores.certificate) (fuelContext (traceSegmentD02 2).stores ctx)))
  · exact fuel_join_step caller .positive (traceSegmentD02 3).stores ((traceSegmentD02 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (traceSegmentD02 4).stores ((traceSegmentD02 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [9, 10] [.right, .left] [.left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentD02 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentD02 4).stores) (applyContext (traceSegmentD02 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceSegmentD02 5).stores ((traceSegmentD02 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .right [10] [.right, .left] [.left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentD02 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentD02 5).stores) (applyContext (traceSegmentD02 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (traceSegmentD02 6).stores ((traceSegmentD02 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.right, .right, .left] [.left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentD02 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentD02 6).stores) (applyContext (traceSegmentD02 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceSegmentD02 7).stores ((traceSegmentD02 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .right [] [.right, .left] [.left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentD02 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentD02 7).stores) (applyContext (traceSegmentD02 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceSegmentD02 8).stores ((traceSegmentD02 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .right [] [.left] [.right, .left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentD02 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentD02 8).stores) (applyContext (traceSegmentD02 8).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceSegmentD02 9).stores ((traceSegmentD02 9).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [] [.right, .right, .left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentD02 9).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentD02 9).stores) (applyContext (traceSegmentD02 9).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (traceSegmentD02 10).stores ((traceSegmentD02 10).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left, .right, .right, .left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((traceSegmentD02 10).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (traceSegmentD02 10).stores) (applyContext (traceSegmentD02 10).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (traceSegmentD02 11).stores ((traceSegmentD02 11).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (traceSegmentD02 11).stores)
        (applyRegisterEquiv.symm ((traceSegmentD02 11).stage.apply regs)) (applyContext (traceSegmentD02 11).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (traceSegmentD02 12).stores ((traceSegmentD02 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (traceSegmentD02 13).stores ((traceSegmentD02 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (traceSegmentD02 14).stores ((traceSegmentD02 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (traceSegmentD02 15).stores ((traceSegmentD02 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (traceSegmentD02 16).stores ((traceSegmentD02 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (traceSegmentD02 17).stores ((traceSegmentD02 17).stage.apply regs) ctx

end ActualEdges

theorem traceSegmentV02_owned (n : Nat) (bound : n < 4) :
    (traceSegmentV02 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem traceSegmentV02_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (traceSegmentV02 n).stores ≤ 4 := by
  interval_cases n <;> decide

theorem segmentV02_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segmentV02.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segmentV02 traceSegmentV02 rfl rfl
    (traceSegmentV02_steps caller regs ctx) traceSegmentV02_owned

theorem segmentV02_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segmentV02.start regs ctx)
      segmentV02.ticks (segmentV02.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceSegmentV02
    4 4 (traceSegmentV02_steps caller regs ctx) traceSegmentV02_cells rfl

theorem traceSegmentV07_owned (n : Nat) (bound : n < 8) :
    (traceSegmentV07 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem traceSegmentV07_cells (n : Nat) (bound : n ≤ 8) :
    fixtureCells (traceSegmentV07 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem segmentV07_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segmentV07.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segmentV07 traceSegmentV07 rfl rfl
    (traceSegmentV07_steps caller regs ctx) traceSegmentV07_owned

theorem segmentV07_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segmentV07.start regs ctx)
      segmentV07.ticks (segmentV07.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceSegmentV07
    8 14 (traceSegmentV07_steps caller regs ctx) traceSegmentV07_cells rfl

theorem traceSegmentV08_owned (n : Nat) (bound : n < 25) :
    (traceSegmentV08 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem traceSegmentV08_cells (n : Nat) (bound : n ≤ 25) :
    fixtureCells (traceSegmentV08 n).stores ≤ 15 := by
  interval_cases n <;> decide

theorem segmentV08_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segmentV08.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segmentV08 traceSegmentV08 rfl rfl
    (traceSegmentV08_steps caller regs ctx) traceSegmentV08_owned

theorem segmentV08_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segmentV08.start regs ctx)
      segmentV08.ticks (segmentV08.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceSegmentV08
    25 15 (traceSegmentV08_steps caller regs ctx) traceSegmentV08_cells rfl

theorem traceSegmentV09_owned (n : Nat) (bound : n < 9) :
    (traceSegmentV09 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem traceSegmentV09_cells (n : Nat) (bound : n ≤ 9) :
    fixtureCells (traceSegmentV09 n).stores ≤ 12 := by
  interval_cases n <;> decide

theorem segmentV09_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segmentV09.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segmentV09 traceSegmentV09 rfl rfl
    (traceSegmentV09_steps caller regs ctx) traceSegmentV09_owned

theorem segmentV09_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segmentV09.start regs ctx)
      segmentV09.ticks (segmentV09.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceSegmentV09
    9 12 (traceSegmentV09_steps caller regs ctx) traceSegmentV09_cells rfl

theorem traceSegmentV10_owned (n : Nat) (bound : n < 9) :
    (traceSegmentV10 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem traceSegmentV10_cells (n : Nat) (bound : n ≤ 9) :
    fixtureCells (traceSegmentV10 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem segmentV10_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segmentV10.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segmentV10 traceSegmentV10 rfl rfl
    (traceSegmentV10_steps caller regs ctx) traceSegmentV10_owned

theorem segmentV10_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segmentV10.start regs ctx)
      segmentV10.ticks (segmentV10.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceSegmentV10
    9 14 (traceSegmentV10_steps caller regs ctx) traceSegmentV10_cells rfl

theorem traceSegmentV11_owned (n : Nat) (bound : n < 17) :
    (traceSegmentV11 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem traceSegmentV11_cells (n : Nat) (bound : n ≤ 17) :
    fixtureCells (traceSegmentV11 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem segmentV11_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segmentV11.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segmentV11 traceSegmentV11 rfl rfl
    (traceSegmentV11_steps caller regs ctx) traceSegmentV11_owned

theorem segmentV11_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segmentV11.start regs ctx)
      segmentV11.ticks (segmentV11.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceSegmentV11
    17 14 (traceSegmentV11_steps caller regs ctx) traceSegmentV11_cells rfl

theorem traceSegmentV12_owned (n : Nat) (bound : n < 13) :
    (traceSegmentV12 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem traceSegmentV12_cells (n : Nat) (bound : n ≤ 13) :
    fixtureCells (traceSegmentV12 n).stores ≤ 13 := by
  interval_cases n <;> decide

theorem segmentV12_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segmentV12.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segmentV12 traceSegmentV12 rfl rfl
    (traceSegmentV12_steps caller regs ctx) traceSegmentV12_owned

theorem segmentV12_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segmentV12.start regs ctx)
      segmentV12.ticks (segmentV12.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceSegmentV12
    13 13 (traceSegmentV12_steps caller regs ctx) traceSegmentV12_cells rfl

theorem traceSegmentV15_owned (n : Nat) (bound : n < 5) :
    (traceSegmentV15 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem traceSegmentV15_cells (n : Nat) (bound : n ≤ 5) :
    fixtureCells (traceSegmentV15 n).stores ≤ 4 := by
  interval_cases n <;> decide

theorem segmentV15_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segmentV15.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segmentV15 traceSegmentV15 rfl rfl
    (traceSegmentV15_steps caller regs ctx) traceSegmentV15_owned

theorem segmentV15_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segmentV15.start regs ctx)
      segmentV15.ticks (segmentV15.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceSegmentV15
    5 4 (traceSegmentV15_steps caller regs ctx) traceSegmentV15_cells rfl

theorem traceSegmentV16_owned (n : Nat) (bound : n < 7) :
    (traceSegmentV16 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem traceSegmentV16_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (traceSegmentV16 n).stores ≤ 12 := by
  interval_cases n <;> decide

theorem segmentV16_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segmentV16.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segmentV16 traceSegmentV16 rfl rfl
    (traceSegmentV16_steps caller regs ctx) traceSegmentV16_owned

theorem segmentV16_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segmentV16.start regs ctx)
      segmentV16.ticks (segmentV16.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceSegmentV16
    7 12 (traceSegmentV16_steps caller regs ctx) traceSegmentV16_cells rfl

theorem traceSegmentV18_owned (n : Nat) (bound : n < 4) :
    (traceSegmentV18 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem traceSegmentV18_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (traceSegmentV18 n).stores ≤ 12 := by
  interval_cases n <;> decide

theorem segmentV18_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segmentV18.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segmentV18 traceSegmentV18 rfl rfl
    (traceSegmentV18_steps caller regs ctx) traceSegmentV18_owned

theorem segmentV18_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segmentV18.start regs ctx)
      segmentV18.ticks (segmentV18.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceSegmentV18
    4 12 (traceSegmentV18_steps caller regs ctx) traceSegmentV18_cells rfl

theorem traceSegmentJ03_owned (n : Nat) (bound : n < 4) :
    (traceSegmentJ03 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem traceSegmentJ03_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (traceSegmentJ03 n).stores ≤ 8 := by
  interval_cases n <;> decide

theorem segmentJ03_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segmentJ03.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segmentJ03 traceSegmentJ03 rfl rfl
    (traceSegmentJ03_steps caller regs ctx) traceSegmentJ03_owned

theorem segmentJ03_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segmentJ03.start regs ctx)
      segmentJ03.ticks (segmentJ03.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceSegmentJ03
    4 8 (traceSegmentJ03_steps caller regs ctx) traceSegmentJ03_cells rfl

theorem traceSegmentD02_owned (n : Nat) (bound : n < 18) :
    (traceSegmentD02 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem traceSegmentD02_cells (n : Nat) (bound : n ≤ 18) :
    fixtureCells (traceSegmentD02 n).stores ≤ 22 := by
  interval_cases n <;> decide

theorem segmentD02_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segmentD02.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segmentD02 traceSegmentD02 rfl rfl
    (traceSegmentD02_steps caller regs ctx) traceSegmentD02_owned

theorem segmentD02_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segmentD02.start regs ctx)
      segmentD02.ticks (segmentD02.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceSegmentD02
    18 22 (traceSegmentD02_steps caller regs ctx) traceSegmentD02_cells rfl

end Examples.RotationCertificateFrontEndStreamMachine.StreamCertificates

