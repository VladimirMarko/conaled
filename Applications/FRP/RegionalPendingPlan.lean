import Applications.FRP.RegionalMigrationResources
import Applications.FRP.PendingMigrationSource
import Applications.FRP.PendingMigrationProgress
import Applications.FRP.PendingMigrationResources

/-! A bounded shared producer with two consumers. Its input is the left Boolean
summand of Rich.Input; the quiescent regional client retains the full sum port. -/
namespace FRPSpec.Regional.Pending
open Applications.Circuits

/-- Independent fork/join equation: D reads old state, N negates shared input. -/
def oracle (input state : Bool) : Bool × Bool := (Bool.xor state (!input),input)

/-- Actual rich frontend execution occurs at the scheduled producer step. -/
def produce (input : Bool) : Bool := Rich.execute (.inl input)
theorem produce_correct (input : Bool) : produce input = input := Rich.correct (.inl input)

/-- Compile the joint D/N/join operation, retaining the next delay state. -/
def jointSource : FirstOrderCompiler.Term Gate [.prod .base .base] (.prod .base .base) :=
  .pair (.prim (.xor (1/4) (1/4))
    (.pair (.snd (.var .here)) (.prim (.not (1/10)) (.fst (.var .here)))))
    (.fst (.var .here))
def jointBody : Circuit (.prod .base .base) (.prod .base .base) :=
  .compose (FirstOrderCompiler.compile Circuit.target jointSource) (.pair .terminate .identity)
def jointProgram : Indefinite.Program .base .base .base := ⟨jointBody,false⟩

theorem joint_correct (input state : Bool) : jointBody.execute (input,state) = oracle input state := by
  cases input <;> cases state <;> rfl

/-- The same cached producer drives actual fused, split, or checked-boundary
executors. Only the consumer subgraph is selected; the producer is not rerun. -/
def wholeResult : Cut → Bool → Bool → Bool × Bool
  | .fused, d, b => jointBody.execute (d,b)
  | .split, d, b =>
    let delayed := Indefinite.delay.machine.step (d,b)
    (Circuit.xor.execute (delayed.1,Circuit.not.execute d),delayed.2)
  | .checked, d, b =>
    let transmitted := decode (encode d)
    let delayed := Indefinite.delay.machine.step (transmitted,b)
    (Circuit.xor.execute (delayed.1,Circuit.not.execute transmitted),delayed.2)

theorem whole_correct (cut : Cut) (d b : Bool) : wholeResult cut d b = oracle d b := by
  cases cut
  · exact joint_correct d b
  · rfl
  · simp only [wholeResult,decode_encode]; rfl

/-- Pending work is finite state. Presence flags distinguish retained values
from consumer completion; cancellation does not erase outstanding references. -/
structure Residual where
  cached : Option Bool := none
  oldState : Bool := false
  dResult : Option Bool := none
  candidate : Option Bool := none
  nResult : Option Bool := none
  cancelled : Bool := false
  deriving DecidableEq, Repr

abbrev Packed := (Option Bool × Bool) × (Option Bool × Option Bool) × Option Bool × Bool

def pack (r : Residual) : Packed := ((r.cached,r.oldState),(r.dResult,r.candidate),r.nResult,r.cancelled)
def unpack (p : Packed) : Residual := ⟨p.1.1,p.1.2,p.2.1.1,p.2.1.2,p.2.2.1,p.2.2.2⟩
@[simp] theorem unpack_pack (r : Residual) : unpack (pack r) = r := by cases r; rfl

structure CheckedResidual where
  cached : Option Redundant
  oldState : Bool
  dResult : Option Bool
  candidate : Option Bool
  nResult : Option Bool
  cancelled : Bool

def checkEncode (r : Residual) : CheckedResidual :=
  ⟨r.cached.map encode,r.oldState,r.dResult,r.candidate,r.nResult,r.cancelled⟩
def checkDecode (r : CheckedResidual) : Residual :=
  ⟨r.cached.map decode,r.oldState,r.dResult,r.candidate,r.nResult,r.cancelled⟩
@[simp] theorem check_decode_encode (r : Residual) : checkDecode (checkEncode r) = r := by
  cases r with
  | mk cached old d candidate n cancelled =>
    cases cached <;> simp [checkDecode,checkEncode,decode_encode]

def mapSlots {A B : Type} (f : A → B) (s : PendingMigration.Slots A) : PendingMigration.Slots B :=
  ⟨s.left.map f,s.right.map f⟩

def Store : Cut → Type
  | .split => PendingMigration.Slots Residual
  | .fused => PendingMigration.Slots Packed
  | .checked => PendingMigration.Slots CheckedResidual

def storeEncode : (cut : Cut) → PendingMigration.Slots Residual → Store cut
  | .split, s => s
  | .fused, s => mapSlots pack s
  | .checked, s => mapSlots checkEncode s

def storeDecode : (cut : Cut) → Store cut → PendingMigration.Slots Residual
  | .split, s => s
  | .fused, s => mapSlots unpack s
  | .checked, s => mapSlots checkDecode s

@[simp] theorem store_decode_split (s : PendingMigration.Slots Residual) : storeDecode .split s = s := rfl
@[simp] theorem store_encode_split (s : PendingMigration.Slots Residual) : storeEncode .split s = s := rfl

@[simp] theorem store_decode_encode (cut : Cut) (s : PendingMigration.Slots Residual) :
    storeDecode cut (storeEncode cut s) = s := by
  cases cut
  · cases s with
    | mk l r => cases l <;> cases r <;> simp [storeDecode,storeEncode,mapSlots]
  · rfl
  · cases s with
    | mk l r => cases l <;> cases r <;> simp [storeDecode,storeEncode,mapSlots]

/-- Two owned delivery cells refer to the single producer cache by live slot.
They survive cancellation until explicit draining, and block slot retirement. -/
structure Deliveries where
  d : Option Bool := none
  n : Option Bool := none
  deriving DecidableEq, Repr

def Deliveries.references (q : Deliveries) (slot : Bool) : Bool :=
  q.d == some slot || q.n == some slot

def Deliveries.rank (q : Deliveries) : Nat := q.d.toList.length + q.n.toList.length

theorem delivery_bound (q : Deliveries) : q.rank ≤ 2 := by
  cases q with
  | mk d n => cases d <;> cases n <;> simp [Deliveries.rank]

/-- A cut owns its concrete cache/adapter representation; protocol traffic is
owned by the stable adapter, independently of the current cut. -/
structure Active where
  cut : Cut
  protocol : PendingMigration.Session
  retained : Store cut
  deliveries : Deliveries

def Active.residuals (s : Active) : PendingMigration.Slots Residual := storeDecode s.cut s.retained

def Active.withResiduals (s : Active) (r : PendingMigration.Slots Residual) : Active :=
  ⟨s.cut,s.protocol,storeEncode s.cut r,s.deliveries⟩

@[simp] theorem with_residuals (s : Active) (r : PendingMigration.Slots Residual) :
    (s.withResiduals r).residuals = r := store_decode_encode _ _

def initialActive (cut : Cut := .split) (kind : Migration.Kind := .delay) : Active :=
  ⟨cut,PendingMigration.initial kind,storeEncode cut {},{}⟩

def convert (s : Active) (cut : Cut) (kind : Migration.Kind) : Active :=
  ⟨cut,PendingMigration.transfer s.protocol kind,storeEncode cut s.residuals,s.deliveries⟩

@[simp] theorem convert_residuals (s : Active) (cut : Cut) (kind : Migration.Kind) :
    (convert s cut kind).residuals = s.residuals := store_decode_encode _ _

/-- Joint checkpoint includes unfinished consumers and all owned references. -/
structure Checkpoint where
  protocol : PendingMigration.Checkpoint
  residuals : PendingMigration.Slots Residual
  deliveries : Deliveries

def checkpoint (s : Active) : Checkpoint := ⟨PendingMigration.checkpoint s.protocol,s.residuals,s.deliveries⟩

theorem convert_checkpoint (s : Active) (cut : Cut) (kind : Migration.Kind) :
    checkpoint (convert s cut kind) = checkpoint s := by
  simp [checkpoint,convert,PendingMigration.checkpoint_transfer,Active.residuals]

/-- Producer work counts the actual raw frontend evaluator, not an oracle call. -/
inductive WorkEvent where
  | producer | deliverD | deliverN | consumers (cut : Cut) (nodes : Nat) | join | retireInternal
  | protocol (work : Nat) (events : List PendingMigration.TransferEvent)
  | allocate (cells : Nat) | copy (cells : Nat) | validate | release (cells : Nat)
  | policy (work : Nat) | inspect
  deriving Repr

end FRPSpec.Regional.Pending
