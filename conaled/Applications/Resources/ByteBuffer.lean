import Applications.Sequences.ByteBuffer

/-! Event accounting for the finite byte-slot contract. Scalar reference counts
and byte payloads are kept separate; none of these counts are execution times. -/
namespace Resources.ByteBuffer
open Sequences.BoundedSummary
open Sequences.ByteBuffer

/-- Multiplicities of #239 primitives, independently enumerated by operation. -/
structure Primitives where
  visit : Nat := 0
  combine : Nat := 0
  cacheWrite : Nat := 0
  cacheRead : Nat := 0
  slotWrite : Nat := 0
  emit : Nat := 0
  control : Nat := 0
  deriving DecidableEq, Repr

def Primitives.project (p : Primitives) (t : BoundedSummary.Tariff) : Nat :=
  t.visit*p.visit + t.combine*p.combine + t.cacheWrite*p.cacheWrite +
  t.cacheRead*p.cacheRead + t.slotWrite*p.slotWrite + t.emit*p.emit + t.control*p.control

def primitives (cached : Bool) (N : Nat) : Command → Nat → Primitives
  | .append _,n => if n < N then
      { control := 2, slotWrite := 1, combine := if cached then 1 else 0,
        cacheWrite := if cached then 1 else 0 }
    else { control := 1 }
  | .query,n => if cached then { cacheRead := 1 } else { visit := n+1, combine := n }
  | .observe,n => { visit := n+1, emit := n }

/-- Instrument the accumulator loop: one terminal visit, and one visit/combine
per indexed byte. No recursive-frame event is emitted by this iteration model. -/
def scanLoopCount : (n : Nat) → (Fin n → Bool) → Parity → Parity × Nat × Nat
  | 0,_,acc => (acc,1,0)
  | n+1,f,acc =>
    let r := scanLoopCount n (fun i => f i.succ) (acc * measure (f 0))
    (r.1,r.2.1+1,r.2.2+1)

theorem scanLoopCount_exact (n : Nat) (f : Fin n → Bool) (acc : Parity) :
    scanLoopCount n f acc = (scanAcc n f acc,n+1,n) := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => simp [scanLoopCount,scanAcc,ih]

theorem query_loop_events (m : Machine W N) :
    scanLoopCount m.size.val m.buffer.read 1 =
      (queryLoop m,(primitives false N .query m.size.val).visit,
        (primitives false N .query m.size.val).combine) := scanLoopCount_exact _ _ _

theorem primitive_projection (cached : Bool) (t : BoundedSummary.Tariff) (N : Nat)
    (cmd : Command) (n : Nat) :
    (primitives cached N cmd n).project t = BoundedSummary.charge cached t N cmd n := by
  cases cmd <;> cases cached <;> simp [primitives,Primitives.project,BoundedSummary.charge]
  all_goals split <;> simp_all
  all_goals omega

/-- Successful operation events include modeled output consumption. The scalar
bound covers index, accumulator and prepared next-counter/cache values, not the
interpreter stack, object headers or allocator internals. -/
structure Events where
  primitive : Primitives
  zeroBytes : Nat := 0
  copyBytes : Nat := 0
  outputBytes : Nat := 0
  consumeBytes : Nat := 0
  scalarSlots : Nat := 4
  ownedPayloadPeak : Nat
  recursiveFrames : Nat := 0
  deriving DecidableEq, Repr

def events (cached : Bool) (N : Nat) (cmd : Command) (n : Nat) : Events :=
  { primitive := primitives cached N cmd n
    copyBytes := if cmd = .observe then 2*n else 0
    outputBytes := if cmd = .observe then n else 0
    consumeBytes := if cmd = .observe then n else 0
    ownedPayloadPeak := N + if cmd = .observe then 2*n else 0 }

/-- Failure observations have no successful primitive projection. Failed runtime
attempts may expend work; this API intentionally makes no zero-cost claim. -/
def measured (cached allocationAvailable outputAvailable : Bool)
    (cmd : Command) (m : Machine W N) :=
  let r := attempt cached allocationAvailable outputAvailable cmd m
  (r,match r.2 with
      | .ok _ => some (events cached N cmd m.size.val)
      | .error _ => none)

theorem successful_events (cached : Bool) (cmd : Command) (m : Machine W N) :
    (measured cached true true cmd m).2 = some (events cached N cmd m.size.val) := by
  simp [measured,successful_specialization]

theorem successful_projection (cached : Bool) (t : BoundedSummary.Tariff)
    (cmd : Command) (m : Machine W N) :
    (events cached N cmd m.size.val).primitive.project t =
      BoundedSummary.charge cached t N cmd m.decode.length := by
  simpa [events] using primitive_projection cached t N cmd m.size.val

/-- The existing measured trace theorem transports the projection without a new
cost induction or a new successful-client contract. -/
def projected (cached : Bool) (t : BoundedSummary.Tariff)
    (cmd : Command) (m : Machine W N) :=
  (step cached cmd m,(events cached N cmd m.size.val).primitive.project t)

theorem projected_cost (cached : Bool) (t : BoundedSummary.Tariff)
    (cs : List Command) (m : Machine W N) (v : Valid cached m) :
    (run (BoundedSummary.liftM (projected cached t)) cs (m,[])).2 =
      BoundedSummary.budget cached t N cs m.decode :=
  BoundedSummary.run_cost _ (step cached) Machine.decode (Valid cached)
    (step_valid cached) (step_simulation cached)
    (fun cmd m => by simp [projected,successful_projection]) cs (m,[]) v

def construction (cached : Bool) (N : Nat) : Events :=
  { primitive := { slotWrite := N, control := 1, cacheWrite := if cached then 1 else 0 }
    zeroBytes := N, ownedPayloadPeak := N }

def conversion (N n : Nat) : Events :=
  { primitive := { visit := N+(n+1), slotWrite := N, combine := n, cacheWrite := 1 }
    copyBytes := N, ownedPayloadPeak := 2*N }

/-- Construction and copy return events only after allocation succeeds. -/
def measuredConstruction (cached : Bool) (fits : (N : Nat) ≤ (W : Nat)) (available : Bool) :=
  (construct fits available,if available then some (construction cached N) else none)

def measuredConversion (m : Machine W N) (available : Bool) :=
  (copy m available,if available then some (conversion N m.size.val) else none)

theorem copy_projection (m : Machine W N) :
    (measuredConversion m true).1 = (m,.ok (Sequences.ByteBuffer.convert m)) ∧
    (measuredConversion m true).2 = some (conversion N m.size.val) := ⟨rfl,rfl⟩

theorem construction_projection (cached : Bool) (t : BoundedSummary.Tariff) (N : Nat) :
    (construction cached N).primitive.project t = BoundedSummary.construct cached t N := by
  cases cached <;> simp [construction,Primitives.project,BoundedSummary.construct] <;> ring

theorem conversion_projection (t : BoundedSummary.Tariff) (N n : Nat) :
    (conversion N n).primitive.project t =
      N*(t.visit+t.slotWrite) + t.visit*(n+1) + t.combine*n + t.cacheWrite := by
  simp [conversion,Primitives.project]; ring

theorem output_ownership (cached : Bool) (m : Machine W N) :
    (events cached N .observe m.size.val).ownedPayloadPeak ≤ 3*N ∧
    (events cached N .observe m.size.val).consumeBytes = m.decode.length := by
  have := m.size.isLt
  simp [events]; omega

theorem iterative_workspace (cached : Bool) (N n : Nat) (cmd : Command) :
    (events cached N cmd n).scalarSlots = 4 ∧ (events cached N cmd n).recursiveFrames = 0 :=
  ⟨rfl,rfl⟩

end Resources.ByteBuffer
