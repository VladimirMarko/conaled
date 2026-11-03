import Applications.FRP.LifecyclePipeline
import Applications.FRP.ReactiveConsumers

/-! Bounded external-driver syntax and pure lifecycle adapter. Codec laws in this
module concern numeric token lists, not Lean's decimal parser or byte IO. -/
namespace FRPSpec.Frontier.Driver
open Trace

abbrev Consumer := Reactive.batches Reactive.jointMachine
abbrev State := Lifecycle.Pipeline.State Nat Nat (Nat × Nat)
abbrev Command := Lifecycle.Command Nat Nat
abbrev Event := Lifecycle.Pipeline.Event Nat Nat (Nat × Nat)

def initial : State := Lifecycle.Pipeline.init (fun _ => Frontier.initial 0) Consumer

def encodePacket : Log Nat Nat → List Nat
  | [] => []
  | (t,xs)::rest => t :: xs.length :: (xs ++ encodePacket rest)

def decodePacket : Nat → List Nat → Option (Log Nat Nat × List Nat)
  | 0, xs => some ([],xs)
  | n+1, t::k::xs =>
    if k ≤ xs.length then do
      let (rest,tail) ← decodePacket n (xs.drop k)
      pure ((t,xs.take k)::rest,tail)
    else none
  | _+1, _ => none

def encode : Command → List Nat
  | .begin id t => [0,id,t]
  | .process id => [1,id]
  | .source which m => [2,(match which with | .left => 0 | .right => 1),m.frontier,
      m.packet.length] ++ encodePacket m.packet
  | .idle => [3]

def decode : List Nat → Option Command
  | [0,id,t] => some (.begin id t)
  | [1,id] => some (.process id)
  | 2::side::w::n::xs => do
    let which ← match side with | 0 => some Source.left | 1 => some Source.right | _ => none
    let (packet,tail) ← decodePacket n xs
    if tail = [] then some (.source which ⟨w,packet⟩) else none
  | [3] => some .idle
  | _ => none

/-- Fragment order, empty fragments and duplicate timestamps survive decoding. -/
theorem decodePacket_encode (p : Log Nat Nat) (tail : List Nat) :
    decodePacket p.length (encodePacket p ++ tail) = some (p,tail) := by
  induction p with
  | nil => rfl
  | cons x rest ih =>
    rcases x with ⟨t,xs⟩
    simp [encodePacket,decodePacket,List.append_assoc,ih]

theorem decode_encode (c : Command) : decode (encode c) = some c := by
  cases c with
  | begin id t => rfl
  | process id => rfl
  | idle => rfl
  | source which m =>
    rcases m with ⟨w,p⟩
    have h := decodePacket_encode p []
    simp only [List.append_nil] at h
    cases which <;> simp [encode,decode,h]

/-- Response tokens retain the original ordered batch independently of the aggregate. -/
def encodeResponse (r : Lifecycle.Response Nat Nat) : List Nat :=
  [r.id,r.time,r.batch.length] ++ r.batch

def decodeResponse : List Nat → Option (Lifecycle.Response Nat Nat × List Nat)
  | id::t::n::xs =>
    if n ≤ xs.length then some (⟨id,t,xs.take n⟩,xs.drop n) else none
  | _ => none

theorem decodeResponse_encode (r : Lifecycle.Response Nat Nat) (tail : List Nat) :
    decodeResponse (encodeResponse r ++ tail) = some (r,tail) := by
  rcases r with ⟨id,t,xs⟩
  simp [encodeResponse,decodeResponse]

def encodeAggregate (p : Nat × Nat) : List Nat := [p.1,p.2]
def decodeAggregate : List Nat → Option (Nat × Nat)
  | [n,total] => some (n,total)
  | _ => none

theorem decodeAggregate_encode (p : Nat × Nat) :
    decodeAggregate (encodeAggregate p) = some p := by cases p; rfl

/-- Bounds specialize the driver, not the generic lifecycle mathematics. -/
def supported : Command → Bool
  | .begin id t => id ≤ 65535 && t < 65535
  | .process id => id ≤ 65535
  | .source _ m => m.frontier ≤ 65535 && m.packet.length ≤ 64 &&
      (m.packet.map (fun x => x.2.length)).sum ≤ 64 &&
      m.packet.all (fun x => x.1 ≤ 65535 && x.2.all (· ≤ 65535))
  | .idle => true

inductive DecodeError | malformed | limit deriving DecidableEq, Repr

def decodeBounded (tokens : List Nat) : Except DecodeError Command :=
  match decode tokens with
  | none => .error .malformed
  | some c => if supported c then .ok c else .error .limit

/-- Roundtripping the supported wire subset never changes the command. -/
theorem decodeBounded_encode (c : Command) (h : supported c = true) :
    decodeBounded (encode c) = .ok c := by simp [decodeBounded,decode_encode,h]

theorem decodeBounded_supported (tokens : List Nat) (c : Command)
    (h : decodeBounded tokens = .ok c) : supported c = true := by
  unfold decodeBounded at h
  split at h
  · contradiction
  · split at h <;> simp_all

structure Output where
  packet : Option Bool
  event : Event
  deriving Repr, DecidableEq

/-- Report the existing validator's decision, including rejection, separately
from lifecycle statuses. Both use the same pre-command source state. -/
def packetStatus (s : State) : Command → Option Bool
  | .source r m => some (decide (windowValid (s.lifecycle.engine.sources r) m.frontier m.packet))
  | _ => none

def step (s : State) (c : Command) : State × Output :=
  let next := Lifecycle.Pipeline.step Consumer s c
  (next.1,⟨packetStatus s c,next.2⟩)

@[simp] theorem step_lifecycle (s : State) (c : Command) :
    (step s c).1 = (Lifecycle.Pipeline.step Consumer s c).1 ∧
    (step s c).2.event = (Lifecycle.Pipeline.step Consumer s c).2 := ⟨rfl,rfl⟩

theorem step_compiled (s : State) (c : Command) :
    ((step s c).1,(step s c).2.event) =
      Lifecycle.Pipeline.step (Reactive.batches Reactive.jointSpec) s c := by
  simp [step,Consumer,Reactive.joint_correct]

/-- The published packet status is exactly the decision used by the source update. -/
theorem packet_status_agrees (s : State) (r : Source) (m : Message Nat Nat) :
    packetStatus s (.source r m) =
      some ((advance (s.lifecycle.engine.sources r) m.frontier m.packet).isSome) := by
  simp [packetStatus,advance]
  split <;> simp_all

/-- Structurally rejected packets leave both source and consumer state intact. -/
theorem rejected_stutters (s : State) (r : Source) (m : Message Nat Nat)
    (h : ¬ windowValid (s.lifecycle.engine.sources r) m.frontier m.packet) :
    (step s (.source r m)).1 = s := by
  rcases s with ⟨⟨⟨l,q,request⟩,last⟩,consumer⟩
  cases r <;> cases request <;>
    simp_all [step,Lifecycle.Pipeline.step,Lifecycle.step,Lifecycle.active,
      Engine.step,Engine.update,Engine.pack,Engine.MachineState.sources,
      Trace.process,advance,Demand.next,Demand.emit,Engine.Command.action,
      Lifecycle.tag,Lifecycle.Pipeline.eventMealy,Lifecycle.Pipeline.untag,
      Frontier.Pipeline.responseMealy]

end FRPSpec.Frontier.Driver
