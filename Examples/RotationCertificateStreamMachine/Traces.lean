import Examples.RotationCertificateStreamMachine.Fixtures

/-!
# RotationCertificateStreamMachine: Traces
-/

namespace Examples.RotationCertificateStreamMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.StreamMachine

/-! ## Finite local certificates for exact inclusive peaks

These certificates contain independently fixed finite states. Every adjacent
pair must be justified by an actual public machine step. The generic argument
then identifies any actual prefix by determinism and proves its physical bound.
-/

def fixtureCells (D : LocalData) : Nat :=
  D.certificate.length + D.moveReverse.length + D.path.length + D.source.length +
  D.saved.length + D.scratch.length + D.units.length + D.fuel.length + D.target.length

structure TracePoint where
  control : Phase ⊕ Bool
  stores : LocalData
  stage : RegisterStage

def TracePoint.reached {K Λ R : Type} {Γ : K → Type}
    (p : TracePoint) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (boundaryLabel p.control)) (p.stage.apply regs) p.stores ctx

theorem local_physical_index_sum (f : LocalStack → Nat) :
    ∑ k, f k = f .certificate + f .moveReverse + f .path + f .source +
      f .saved + f .scratch + f .units + f .fuel + f .target := by
  change (∑ k ∈ ({.certificate, .moveReverse, .path, .source, .saved, .scratch,
    .units, .fuel, .target} : Finset LocalStack), f k) = _
  simp [Nat.add_comm, Nat.add_left_comm]

theorem actual_physical_cells_of_complete_cfg
    {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (label : Option (Label Λ)) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    physicalCells (cfg label regs D ctx) = fixtureCells D + externalCells ctx := by
  rw [physicalCells, Fintype.sum_sum_type, local_physical_index_sum]
  rfl

section FiniteTraceConnections

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem finite_trace_actual_prefix (points : Nat → TracePoint) (ticks : Nat)
    (adjacent : ∀ n, n < ticks →
      step caller ((points n).reached regs ctx) = some ((points (n + 1)).reached regs ctx))
    (n : Nat) (bound : n ≤ ticks) :
    Runs (step caller) ((points 0).reached regs ctx) n ((points n).reached regs ctx) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have before := ih (by omega)
      change (next caller)^[n] (some ((points 0).reached regs ctx)) =
        some ((points n).reached regs ctx) at before
      change (next caller)^[n + 1] (some ((points 0).reached regs ctx)) = _
      rw [Function.iterate_succ_apply', before, next_some]
      exact adjacent n (by omega)

variable [Fintype K]

theorem finite_trace_has_its_exact_inclusive_peak (points : Nat → TracePoint)
    (ticks peak : Nat)
    (adjacent : ∀ n, n < ticks →
      step caller ((points n).reached regs ctx) = some ((points (n + 1)).reached regs ctx))
    (bounded : ∀ n, n ≤ ticks → fixtureCells (points n).stores ≤ peak)
    (attained : fixtureCells (points 0).stores = peak) :
    ExactPeak (step caller) ((points 0).reached regs ctx) ticks
      (peak + externalCells ctx) := by
  constructor
  · intro n bound reached executed
    have actual := finite_trace_actual_prefix caller regs ctx points ticks adjacent n bound
    have same : reached = (points n).reached regs ctx :=
      Option.some.inj (executed.symm.trans actual)
    subst reached
    rw [TracePoint.reached, actual_physical_cells_of_complete_cfg]
    exact Nat.add_le_add_right (bounded n bound) _
  · refine ⟨0, (points 0).reached regs ctx, Nat.zero_le _, rfl, ?_⟩
    rw [TracePoint.reached, actual_physical_cells_of_complete_cfg, attained]

end FiniteTraceConnections

/-! ### Fixed small local-state certificates; all edges require actual step proofs -/

def trace_a01 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [] [] [] [] [] [], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [] [] [] [] [] [], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [] [], .complete⟩
  | 3 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [] [], .complete⟩

def trace_a02 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [15] [] [] [] [] [] [] [] [], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [15] [] [] [] [] [] [] [] [], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [] [] [] [] [] [], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .zero), data [15] [] [] [] [] [] [] [] [], .fuel⟩
  | _ => ⟨.inr false, data [15] [] [] [] [] [] [] [] [], .complete⟩

def trace_a03 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [0] [] [] [] [] [0], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [0] [] [] [] [] [0], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [] [0], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [] [], .complete⟩
  | 4 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [] [], .complete⟩

def trace_a04 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [1, 0, 0] [] [] [] [false] [1, 0, 0], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0, 0] [] [] [] [false] [1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0] [] [] [] [false] [1, 0, 0], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false] [0, 0], .complete⟩
  | 4 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 5 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | 6 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false] [], .complete⟩

def trace_a05 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [0, 1, 0, 0] [] [] [] [false, false] [0, 1, 0, 0], .complete⟩
  | 4 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0] [] [] [] [false, false] [1, 0, 0], .complete⟩
  | 5 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false, false] [0, 0], .complete⟩
  | 6 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false, false] [0], .complete⟩
  | 7 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false, false] [], .complete⟩
  | 8 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false, false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false, false] [], .complete⟩

def trace_a06 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [1, 0, 0] [] [] [] [] [0], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0, 0] [] [] [] [] [0], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0] [] [] [] [] [0], .complete⟩
  | 3 => ⟨.inl (equalityJoinPhase .different), data [] [] [] [0, 0] [] [] [] [] [], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [0, 0] [] [] [] [] [], .complete⟩

def trace_a07 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [15] [] [] [] [true] [15], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [15] [] [] [] [true] [15], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [15] [] [] [] [true] [15], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [true] [], .complete⟩
  | 4 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [true] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [true] [], .complete⟩

def trace_a08 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [1, 0, 15, 2] [] [] [] [] [1, 0, 3, 11], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0, 15, 2] [] [] [] [] [1, 0, 3, 11], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 15, 2] [] [] [] [] [1, 0, 3, 11], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [0, 15, 2] [] [] [] [] [0, 3, 11], .complete⟩
  | 4 => ⟨.inl (comparePhase), data [] [] [] [15, 2] [] [] [] [] [3, 11], .complete⟩
  | 5 => ⟨.inl (equalityJoinPhase .different), data [] [] [] [2] [] [] [] [] [11], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [2] [] [] [] [] [11], .complete⟩

def trace_a09 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 1, 0, 0, 0], .fuel⟩
  | 5 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 6 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .fuel⟩
  | 7 => ⟨.inl (fuelJoinPhase .zero), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .fuel⟩
  | _ => ⟨.inr false, data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .complete⟩

def trace_a10 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩

def trace_a11 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [15] [.left] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.undo .left))), data [15] [.left] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.undo .left))), data [8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩

def trace_a12 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [] [] [] [0, 1, 0, 0] [] [] [()] [false] [1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [] [] [] [1, 0, 0] [] [0] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0] [] [0] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (inspectPhase), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0, 0] [] [] [] [false] [1, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0] [] [] [] [false] [0, 0, 0], .complete⟩
  | 21 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false] [0, 0], .complete⟩
  | 22 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 23 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | 24 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false] [], .complete⟩

def trace_a13 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .right))), data [10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .right))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .right))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .right))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .right))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .right))), data [] [] [] [0, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight))), data [] [] [] [1, 0, 0] [] [0] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight))), data [] [] [] [0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 15 => ⟨.inl (inspectPhase), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 16 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 17 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 18 => ⟨.inl (comparePhase), data [] [] [] [0, 1, 0, 0] [] [] [] [false] [0, 1, 0, 0], .complete⟩
  | 19 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0] [] [] [] [false] [1, 0, 0], .complete⟩
  | 20 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false] [0, 0], .complete⟩
  | 21 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 22 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | 23 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false] [], .complete⟩

def trace_a14 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [] [0] [] [] [] [true] [0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [0] [] [] [] [true] [0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [] [] [0] [] [] [] [false] [0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10] [] [] [0] [] [] [] [false] [0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .dropPending)), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 12 => ⟨.inl (applyJoinPhase MoveApplyMachine.rotationFailure), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [0] [] [] [] [false] [0], .complete⟩

def trace_a15 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 8, 8, 10] [] [] [0] [] [] [] [true] [0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 8, 8, 10] [] [] [0] [] [] [] [true] [0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 8, 8, 10] [] [] [0] [] [] [] [false] [0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 8, 8, 10] [] [] [0] [] [] [] [false] [0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 8, 8, 10] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [8, 8, 10] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [8, 10] [.left] [] [0] [] [] [] [false] [0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [.left, .left] [] [0] [] [] [] [false] [0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.left, .left] [] [0] [] [] [] [false] [0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.left] [.left] [0] [] [] [] [false] [0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [.left, .left] [0] [] [] [] [false] [0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [.left, .left] [0] [] [] [] [false] [0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.left, .left] [0] [] [] [] [false] [0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .dropPending)), data [] [] [.left] [0] [] [] [] [false] [0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [.left] [0] [] [] [] [false] [0], .complete⟩
  | 15 => ⟨.inl (applyJoinPhase MoveApplyMachine.rotationFailure), data [] [] [.left] [0] [] [] [] [false] [0], .complete⟩
  | _ => ⟨.inr false, data [] [] [.left] [0] [] [] [] [false] [0], .complete⟩

def trace_a16 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 8, 10] [] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [true] [1, 1, 1, 0, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 8, 10] [] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [true] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 8, 10] [] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 8, 10] [] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 8, 10] [] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [8, 10] [] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [1, 0, 1, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [] [] [] [0, 1, 0, 0, 0] [1] [] [()] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [] [] [] [1, 0, 0, 0] [1] [0] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0] [1] [0] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 0, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (inspectPhase), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 21 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 22 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 23 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0, 0], .complete⟩
  | 24 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0, 0, 0] [] [] [] [false] [1, 0, 0, 0, 0], .complete⟩
  | 25 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0, 0] [] [] [] [false] [0, 0, 0, 0], .complete⟩
  | 26 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0] [] [] [] [false] [0, 0, 0], .complete⟩
  | 27 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false] [0, 0], .complete⟩
  | 28 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 29 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | 30 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false] [], .complete⟩

def trace_a17 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 9, 10] [] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 9, 10] [] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 9, 10] [] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 9, 10] [] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 9, 10] [] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [9, 10] [] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [.right] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.right] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [.right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [.right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanPrefix .left))), data [] [] [] [0, 1, 0, 1, 0, 0] [1] [] [()] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 0, 0] [0, 1] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [1, 0, 1, 0, 0] [0, 1] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [] [] [] [0, 1, 0, 0] [0, 1] [] [()] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [] [] [] [1, 0, 0] [0, 1] [0] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0] [0, 1] [0] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0] [0, 1] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 0, 0, 0] [0, 1] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [0, 1, 1, 0, 0, 0] [1] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 0, 1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 21 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 0, 1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 22 => ⟨.inl (inspectPhase), data [] [] [] [1, 0, 1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 23 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0, 1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 24 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 25 => ⟨.inl (comparePhase), data [] [] [] [0, 1, 1, 0, 0, 0] [] [] [] [false] [0, 1, 1, 0, 0, 0], .complete⟩
  | 26 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 27 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0, 0] [] [] [] [false] [1, 0, 0, 0], .complete⟩
  | 28 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0] [] [] [] [false] [0, 0, 0], .complete⟩
  | 29 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false] [0, 0], .complete⟩
  | 30 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 31 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | 32 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false] [], .complete⟩

def trace_a18 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .borrow), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [true] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .fuel⟩
  | 5 => ⟨.inl (fuelJoinPhase .positive), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .fuel⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [7, 10] [] [] [0, 1, 0, 0] [] [] [()] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [7, 10] [] [] [1, 0, 0] [] [0] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [7, 10] [] [] [0, 0] [] [0] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [7, 10] [] [] [0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 18 => ⟨.inl (inspectPhase), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 19 => ⟨.inl (counterPhase .borrow), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 20 => ⟨.inl (counterPhase .restoreTrue), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 21 => ⟨.inl (fuelJoinPhase .positive), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 22 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 23 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .right))), data [10] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 24 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .right))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 25 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .right))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 26 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .right))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 27 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .right))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 28 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .right))), data [] [] [] [0, 0, 0] [] [] [()] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 29 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight))), data [] [] [] [1, 0, 0] [] [0] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 30 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight))), data [] [] [] [0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 31 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 32 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 33 => ⟨.inl (inspectPhase), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 34 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 35 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 36 => ⟨.inl (comparePhase), data [] [] [] [0, 1, 0, 0] [] [] [] [false, false] [0, 1, 0, 0], .complete⟩
  | 37 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0] [] [] [] [false, false] [1, 0, 0], .complete⟩
  | 38 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false, false] [0, 0], .complete⟩
  | 39 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false, false] [0], .complete⟩
  | 40 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false, false] [], .complete⟩
  | 41 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false, false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false, false] [], .complete⟩

def trace_a19 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [7, 10] [] [] [0, 1, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [7, 10] [] [] [1, 0, 0] [] [0] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [7, 10] [] [] [0, 0] [] [0] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [7, 10] [] [] [0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 16 => ⟨.inl (inspectPhase), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 17 => ⟨.inl (counterPhase .borrow), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 18 => ⟨.inl (counterPhase .borrow), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [()] [] [1, 0, 1, 0, 0], .complete⟩
  | 19 => ⟨.inl (counterPhase .restoreFalse), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [()] [] [1, 0, 1, 0, 0], .complete⟩
  | 20 => ⟨.inl (counterPhase .restoreFalse), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 21 => ⟨.inl (fuelJoinPhase .zero), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩

def trace_a20 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .borrow), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [()] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .fuel⟩
  | 5 => ⟨.inl (fuelJoinPhase .positive), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .fuel⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [15] [] [] [0, 1, 0, 0] [] [] [()] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [15] [] [] [1, 0, 0] [] [0] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [15] [] [] [0, 0] [] [0] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [15] [] [] [0, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (inspectPhase), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (counterPhase .restoreTrue), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .complete⟩
  | 21 => ⟨.inl (fuelJoinPhase .positive), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .complete⟩
  | 22 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .complete⟩
  | 23 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .complete⟩
  | 24 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .complete⟩

def trace_a21 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [] [1, 0, 1, 15] [] [] [] [true] [1, 1, 0, 15], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 15] [] [] [] [true] [1, 1, 0, 15], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [] [] [1, 0, 1, 15] [] [] [] [false] [1, 1, 0, 15], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10] [] [] [1, 0, 1, 15] [] [] [] [false] [1, 1, 0, 15], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [] [] [1, 0, 1, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [] [] [1, 0, 1, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [] [1, 0, 1, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [] [1, 0, 1, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [1, 0, 1, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [] [] [] [0, 1, 15] [] [] [()] [false] [1, 1, 0, 15], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [] [] [] [1, 15] [] [0] [] [false] [1, 1, 0, 15], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [15] [] [0] [] [false] [1, 1, 0, 15], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 0, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 15 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 1, 0, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 16 => ⟨.inl (inspectPhase), data [] [] [] [1, 1, 0, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 17 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 1, 0, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 18 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 0, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 19 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 15] [] [] [] [false] [1, 0, 15], .complete⟩
  | 20 => ⟨.inl (comparePhase), data [] [] [] [0, 15] [] [] [] [false] [0, 15], .complete⟩
  | 21 => ⟨.inl (comparePhase), data [] [] [] [15] [] [] [] [false] [15], .complete⟩
  | 22 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | 23 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false] [], .complete⟩

def trace_d01 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .complete⟩
  | 3 => ⟨.inl (equalityJoinPhase .equal), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .complete⟩
  | _ => ⟨.inr true, data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .complete⟩

def trace_d02 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [15] [.right, .left] [.right] [15] [12] [3] [(), ()] [true] [2], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [15] [.right, .left] [.right] [15] [12] [3] [(), ()] [true] [2], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [15] [.right, .left] [.right] [15] [12] [3] [(), ()] [false] [2], .fuel⟩
  | 3 => ⟨.inl (counterPhase .restoreTrue), data [15] [.right, .left] [.right] [15] [12] [3] [()] [true, false] [2], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreTrue), data [15] [.right, .left] [.right] [15] [12] [3] [] [true, true, false] [2], .fuel⟩
  | 5 => ⟨.inl (fuelJoinPhase .positive), data [15] [.right, .left] [.right] [15] [12] [3] [] [true, true, false] [2], .fuel⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [15] [.right, .left] [.right] [15] [12] [3] [] [true, true, false] [2], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [15] [.right, .left] [.right] [15] [12] [3] [] [true, true, false] [2], .complete⟩
  | 8 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [15] [.right, .left] [.right] [15] [12] [3] [] [true, true, false] [2], .complete⟩
  | _ => ⟨.inr false, data [15] [.right, .left] [.right] [15] [12] [3] [] [true, true, false] [2], .complete⟩

def trace_d03 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [15] [] [] [] [] [] [(), ()] [] [], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [15] [] [] [] [] [] [(), ()] [] [], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [] [] [] [(), ()] [] [], .fuel⟩
  | 3 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [] [] [] [()] [false] [], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [] [] [] [] [false, false] [], .fuel⟩
  | 5 => ⟨.inl (fuelJoinPhase .zero), data [15] [] [] [] [] [] [] [false, false] [], .fuel⟩
  | _ => ⟨.inr false, data [15] [] [] [] [] [] [] [false, false] [], .complete⟩

def trace_d04 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [15] [.right, .left] [.right] [1] [12] [3] [] [true] [0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [15] [.right, .left] [.right] [1] [12] [3] [] [true] [0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 6 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | _ => ⟨.inr false, data [15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩

def trace_d05 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 8, 15] [.right, .left] [.right] [1] [12] [3] [] [true] [0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 8, 15] [.right, .left] [.right] [1] [12] [3] [] [true] [0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 8, 15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 8, 15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 8, 15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [8, 15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [15] [.left, .right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.undo .left))), data [15] [.left, .right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.undo .left))), data [8, 15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.undo .left))), data [9, 8, 15] [.left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.undo .left))), data [8, 9, 8, 15] [] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [6, 8, 9, 8, 15] [] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 12 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [6, 8, 9, 8, 15] [] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | _ => ⟨.inr false, data [6, 8, 9, 8, 15] [] [.right] [1] [12] [3] [] [false] [0], .complete⟩

def trace_d06 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [true] [1, 1, 1, 0, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [true] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [1, 0, 1, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [] [] [] [0, 1, 0, 0, 0] [1] [] [()] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [] [] [] [1, 0, 0, 0] [1] [0] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0] [1] [0] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 0, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (inspectPhase), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 21 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 22 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0, 0], .complete⟩
  | 23 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0, 0, 0] [] [] [] [false] [1, 0, 0, 0, 0], .complete⟩
  | 24 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0, 0] [] [] [] [false] [0, 0, 0, 0], .complete⟩
  | 25 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0] [] [] [] [false] [0, 0, 0], .complete⟩
  | 26 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false] [0, 0], .complete⟩
  | 27 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 28 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | 29 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false] [], .complete⟩

def trace_d07 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [true] [1, 1, 1, 0, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [true] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [1, 0, 1, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [] [] [] [0, 1, 0, 0, 0] [1] [] [()] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [] [] [] [1, 0, 0, 0] [1] [0] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0] [1] [0] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 0, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (inspectPhase), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 21 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0, 0], .complete⟩
  | 22 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0, 0, 0] [] [] [] [false] [1, 0, 0, 0, 0], .complete⟩
  | 23 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0, 0] [] [] [] [false] [0, 0, 0, 0], .complete⟩
  | 24 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0] [] [] [] [false] [0, 0, 0], .complete⟩
  | 25 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false] [0, 0], .complete⟩
  | 26 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 27 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | 28 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false] [], .complete⟩

def trace_d08 : Nat → TracePoint
  | 0 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [.right] [0] [] [15] [(), ()] [] [0], .original⟩
  | 1 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [.right] [0] [] [15] [(), ()] [] [0], .applied⟩
  | 2 => ⟨.inl (inspectPhase), data [] [] [.right] [0] [] [15] [(), ()] [] [0], .complete⟩
  | 3 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [.right] [0] [] [15] [(), ()] [] [0], .complete⟩
  | 4 => ⟨.inl (comparePhase), data [] [] [.right] [0] [] [15] [(), ()] [] [0], .complete⟩
  | 5 => ⟨.inl (comparePhase), data [] [] [.right] [] [] [15] [(), ()] [] [], .complete⟩
  | 6 => ⟨.inl (equalityJoinPhase .equal), data [] [] [.right] [] [] [15] [(), ()] [] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [.right] [] [] [15] [(), ()] [] [], .complete⟩

def trace_d09 : Nat → TracePoint
  | 0 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [] [] [] [] [] [], .original⟩
  | 1 => ⟨.inl (inspectPhase), data [] [] [] [] [] [] [] [] [], .complete⟩
  | 2 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [] [] [] [] [] [], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [] [], .complete⟩
  | 4 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [] [], .complete⟩

def trace_d10 : Nat → TracePoint
  | 0 => ⟨.inl (fuelJoinPhase .positive), data [] [] [] [] [] [] [] [] [], .original⟩
  | 1 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [] [] [] [] [] [] [] [] [], .complete⟩
  | 2 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [] [] [] [] [] [] [] [] [], .complete⟩
  | 3 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [] [] [] [] [] [] [] [] [], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [] [] [] [] [] [], .complete⟩

def trace_d11 : Nat → TracePoint
  | 0 => ⟨.inl (fuelJoinPhase .atEnd), data [15] [] [] [] [] [] [] [] [], .original⟩
  | 1 => ⟨.inl (comparePhase), data [15] [] [] [] [] [] [] [] [], .complete⟩
  | 2 => ⟨.inl (equalityJoinPhase .equal), data [15] [] [] [] [] [] [] [] [], .complete⟩
  | _ => ⟨.inr true, data [15] [] [] [] [] [] [] [] [], .complete⟩

def trace_d12 : Nat → TracePoint
  | 0 => ⟨.inl (comparePhase), data [15] [] [] [] [] [] [] [] [], .original⟩
  | 1 => ⟨.inl (equalityJoinPhase .equal), data [15] [] [] [] [] [] [] [] [], .equality⟩
  | _ => ⟨.inr true, data [15] [] [] [] [] [] [] [] [], .complete⟩

def trace_d13 : Nat → TracePoint
  | 0 => ⟨.inl (equalityJoinPhase .equal), data [15] [] [] [1] [] [] [] [] [0], .original⟩
  | _ => ⟨.inr true, data [15] [] [] [1] [] [] [] [] [0], .complete⟩

def trace_r01 : Nat → TracePoint
  | 0 => ⟨.inl (counterPhase .restoreTrue), data [15] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .restoreTrue), data [15] [] [] [1, 0, 1, 0, 0] [] [] [()] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 1, 0, 0, 0], .complete⟩

def trace_r02 : Nat → TracePoint
  | 0 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false, true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, true] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .zero), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, true] [1, 1, 0, 0, 0], .fuel⟩
  | _ => ⟨.inr false, data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, true] [1, 1, 0, 0, 0], .complete⟩

def trace_r03 : Nat → TracePoint
  | 0 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [15] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [15] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .parser⟩
  | 2 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [15] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .parser⟩
  | 3 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [15] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [15] [] [] [1, 0, 1, 0, 0, 0] [1] [] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [15] [] [] [1, 0, 1, 0, 0, 0] [1] [] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [15] [] [] [0, 1, 0, 0, 0] [1] [] [()] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [15] [] [] [1, 0, 0, 0] [1] [0] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [15] [] [] [0, 0, 0] [1] [0] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [15] [] [] [0, 0, 0, 0] [1] [] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [15] [] [] [1, 1, 0, 0, 0, 0] [1] [] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [15] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 12 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [15] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 13 => ⟨.inl (inspectPhase), data [15] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (fuelJoinPhase .zero), data [15] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .complete⟩

def trace_r04 : Nat → TracePoint
  | 0 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false, true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [true, false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .fuel⟩
  | 5 => ⟨.inl (fuelJoinPhase .positive), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .fuel⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [] [] [] [0, 1, 0, 0] [] [] [()] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [] [] [] [1, 0, 0] [] [0] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0] [] [0] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (inspectPhase), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 21 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0, 0] [] [] [] [true, true, false] [1, 0, 0, 0], .complete⟩
  | 22 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0] [] [] [] [true, true, false] [0, 0, 0], .complete⟩
  | 23 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [true, true, false] [0, 0], .complete⟩
  | 24 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [true, true, false] [0], .complete⟩
  | 25 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [true, true, false] [], .complete⟩
  | 26 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [true, true, false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [true, true, false] [], .complete⟩

def trace_r05 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [1, 0] [] [] [] [true] [1, 0, 15, 2], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0] [] [] [] [true] [1, 0, 15, 2], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [1, 0] [] [] [] [true] [1, 0, 15, 2], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [true] [0, 15, 2], .complete⟩
  | 4 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [true] [15, 2], .complete⟩
  | 5 => ⟨.inl (equalityJoinPhase .different), data [] [] [] [] [] [] [] [true] [2], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [] [] [] [] [true] [2], .complete⟩

def trace_r06 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [1, 0, 15, 2] [] [] [] [true] [1, 0], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0, 15, 2] [] [] [] [true] [1, 0], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 15, 2] [] [] [] [true] [1, 0], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [0, 15, 2] [] [] [] [true] [0], .complete⟩
  | 4 => ⟨.inl (comparePhase), data [] [] [] [15, 2] [] [] [] [true] [], .complete⟩
  | 5 => ⟨.inl (equalityJoinPhase .different), data [] [] [] [2] [] [] [] [true] [], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [2] [] [] [] [true] [], .complete⟩

def trace_r07 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [15] [] [] [0, 1, 0, 0] [] [] [()] [false] [1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [15] [] [] [1, 0, 0] [] [0] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [15] [] [] [0, 0] [] [0] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [15] [] [] [0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (inspectPhase), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 1, 0, 0, 0] [] [] [()] [] [1, 1, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [1, 1, 0, 0, 0] [] [] [()] [] [1, 1, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 21 => ⟨.inl (fuelJoinPhase .zero), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩

def trace_r08 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .borrow), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [()] [true] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .fuel⟩
  | 5 => ⟨.inl (fuelJoinPhase .positive), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .fuel⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [7, 10, 15] [] [] [0, 1, 0, 0] [] [] [()] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [7, 10, 15] [] [] [1, 0, 0] [] [0] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [7, 10, 15] [] [] [0, 0] [] [0] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [7, 10, 15] [] [] [0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 18 => ⟨.inl (inspectPhase), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 19 => ⟨.inl (counterPhase .borrow), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 20 => ⟨.inl (counterPhase .restoreTrue), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 21 => ⟨.inl (fuelJoinPhase .positive), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 22 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 23 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .right))), data [10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 24 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .right))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 25 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .right))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 26 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .right))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 27 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .right))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 28 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .right))), data [15] [] [] [0, 0, 0] [] [] [()] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 29 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight))), data [15] [] [] [1, 0, 0] [] [0] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 30 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight))), data [15] [] [] [0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 31 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 32 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 33 => ⟨.inl (inspectPhase), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 34 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 35 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .complete⟩
  | 36 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 0, 1, 0, 0], .complete⟩
  | 37 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 0, 1, 0, 0], .complete⟩
  | 38 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .complete⟩
  | 39 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 40 => ⟨.inl (fuelJoinPhase .zero), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩

def trace_r09 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [7, 10, 15] [] [] [0, 1, 0, 0] [] [] [()] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [7, 10, 15] [] [] [1, 0, 0] [] [0] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [7, 10, 15] [] [] [0, 0] [] [0] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [7, 10, 15] [] [] [0, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 16 => ⟨.inl (inspectPhase), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 17 => ⟨.inl (counterPhase .borrow), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 18 => ⟨.inl (counterPhase .borrow), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [()] [true] [1, 0, 1, 0, 0], .complete⟩
  | 19 => ⟨.inl (counterPhase .restoreTrue), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .complete⟩
  | 20 => ⟨.inl (counterPhase .restoreTrue), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 21 => ⟨.inl (fuelJoinPhase .positive), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 22 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 23 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .right))), data [10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 24 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .right))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 25 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .right))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 26 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .right))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 27 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .right))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 28 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .right))), data [15] [] [] [0, 0, 0] [] [] [()] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 29 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight))), data [15] [] [] [1, 0, 0] [] [0] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 30 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight))), data [15] [] [] [0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 31 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 32 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 33 => ⟨.inl (inspectPhase), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 34 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 35 => ⟨.inl (counterPhase .restoreTrue), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 36 => ⟨.inl (fuelJoinPhase .positive), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 37 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 38 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 39 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩

def trace_r10 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [.right, .left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [.right, .left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.right, .left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanPrefix .left))), data [] [] [.left] [0, 1, 0, 0] [1] [] [()] [false] [1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.left] [1, 0, 0] [0, 1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [0, 0] [1, 0, 1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [0, 0] [1, 0, 1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .dropPending)), data [] [] [] [0, 0] [1, 0, 1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [] [0, 0] [1, 0, 1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [] [1, 0, 0] [0, 1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [] [0, 1, 0, 0] [1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (applyJoinPhase MoveApplyMachine.rotationFailure), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩



end Examples.RotationCertificateStreamMachine
