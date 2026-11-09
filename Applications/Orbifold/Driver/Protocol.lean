import Applications.Orbifold.Driver.Accounting
import Lean

namespace Orbifold.DiskTransport.Numerical.Driver
open Lean

structure Request where
  events : List Event
  tolerance : ℚ
  work : Nat
  limits : Limits

def parseRat (j : Json) : Except String ℚ := do
  let xs ← j.getArr?
  if xs.size != 2 then throw "rational must contain numerator and positive denominator strings"
  let ns ← xs[0]!.getStr?
  let ds ← xs[1]!.getStr?
  if ns.length > 20 || ds.length > 20 then throw "input rational text limit"
  let some n := ns.toInt? | throw "invalid numerator"
  let some d := ds.toNat? | throw "invalid denominator"
  if d == 0 then throw "zero denominator"
  if n.natAbs > 2^63 || d > 2^63 then throw "input rational magnitude limit"
  return (n : ℚ)/(d : ℚ)

def parseComplex (j : Json) : Except String QComplex := do
  let xs ← j.getArr?
  if xs.size != 2 then throw "complex coordinate requires two rationals"
  return (← parseRat xs[0]!, ← parseRat xs[1]!)

def parseEvent (j : Json) : Except String Event := do
  let kind ← (← j.getObjVal? "kind").getStr?
  if kind == "relabel" then
    let k ← (← j.getObjVal? "quarter_turns").getNat?
    if hk : k < 4 then return .relabel ⟨k,hk⟩
    else throw "quarter_turns must be 0, 1, 2 or 3"
  let control ← match kind with
    | "move" => do pure <| Input.move (← parseComplex (← j.getObjVal? "velocity"))
    | "turn" => do pure <| Input.turn (← parseRat (← j.getObjVal? "speed"))
    | "hold" => pure Input.hold
    | _ => throw "unsupported command kind"
  let d ← parseRat (← j.getObjVal? "duration")
  if hd : 0 ≤ d then
    if d > 1/4 then throw "duration exceeds bounded demonstration limit 1/4"
    let c : Tick := ⟨control,d,hd⟩
    if supported c then return .command c else throw "unsupported control magnitude"
  else throw "negative duration"

def parseRequest (j : Json) : Except String Request := do
  let initializer ← (← j.getObjVal? "initial").getStr?
  if initializer != "negative-axis" then throw "unsupported initializer; no arbitrary Approx assertion accepted"
  let xs ← (← j.getObjVal? "commands").getArr?
  if xs.size > 16 then throw "at most 16 command/event inputs"
  let events ← xs.toList.mapM parseEvent
  let tolerance ← parseRat (← j.getObjVal? "tolerance")
  if tolerance < 0 || tolerance > 1 then throw "tolerance must lie in [0,1]"
  let work ← (← j.getObjVal? "work").getNat?
  if work > 128 then throw "work exceeds 128 reserved units"
  let rounds ← (← j.getObjVal? "rounds").getNat?
  if rounds == 0 || rounds > 4 then throw "rounds must be between 1 and 4"
  let cap ← (← j.getObjVal? "packet_bits").getNat?
  if cap < 64 || cap > 16384 then throw "packet_bits must lie in [64,16384]"
  return ⟨events,tolerance,work,⟨rounds,cap⟩⟩

def ratJson (r : ℚ) : Json := Json.arr #[toJson (toString r.num),toJson (toString r.den)]
def complexJson (z : QComplex) : Json := Json.arr #[ratJson z.1,ratJson z.2]
def packetJson (q : Packet) : Json := Json.mkObj [
  ("position",complexJson q.state.position),("frame",complexJson q.state.frame),
  ("error",ratJson q.error),("bits",toJson (packetBits q))]

def failureText : Failure → String
  | .domain => "domain-check"
  | .accuracy => "accuracy-unmet"
  | .work => "work-exhausted"
  | .packetBits => "packet-bit-limit"
  | .unsupported => "unsupported-control"

def controlJson : Input → Json
  | .move v => Json.mkObj [("kind",toJson "move"),("velocity",complexJson v)]
  | .turn w => Json.mkObj [("kind",toJson "turn"),("speed",ratJson w)]
  | .hold => Json.mkObj [("kind",toJson "hold")]

def countsJson (c : Resources.AttemptCounts) (charged : Nat) : Json := Json.mkObj [
  ("attempted",toJson c.1),("accepted",toJson c.2.1),("rejected",toJson c.2.2),
  ("charged",toJson charged)]

def samplesJson (start d : ℚ) (qs : List Packet) : Json :=
  toJson (qs.zipIdx.map fun (q,i) => Json.mkObj [
    ("local_time",ratJson ((i+1 : Nat)*d)),("time",ratJson (start+(i+1 : Nat)*d)),
    ("packet",packetJson q)])

def observationJson (index : Nat) (start : ℚ) : Observation → Json
  | .command c n q r => Json.mkObj [
      ("kind",toJson "command"),("index",toJson index),("control",controlJson c.control),
      ("duration",ratJson c.duration),("subdivisions",toJson (n+1)),
      ("time",ratJson start),("end_time",ratJson (start+r.elapsed)),
      ("source",packetJson q),("target",packetJson r.final),
      ("samples",samplesJson start (subTick c n).duration r.samples)]
  | .relabel k q => Json.mkObj [
      ("kind",toJson "relabel"),("index",toJson index),("quarter_turns",toJson k.val),
      ("time",ratJson start),("duration",ratJson 0),
      ("source",packetJson q),("target",packetJson (q.rotate k.val))]

def traceJson : List Observation → Nat → ℚ → List Json
  | [], _, _ => []
  | o::os, i, t => observationJson i t o :: traceJson os (i+1) (t+o.elapsed)

def attemptJson (a : AttemptLog) : Json := Json.mkObj [
  ("subdivisions",toJson a.subdivisions),("work",countsJson a.counts (a.subdivisions+1)),
  ("final_error",a.finalError.map ratJson |>.getD Json.null),
  ("check",toJson (failureText a.reason))]

def reportJson (r : Report) : Json := Json.mkObj [
  ("status",toJson (if r.failure.isNone then "success" else "failure")),
  ("failure",r.failure.map (toJson ∘ failureText) |>.getD Json.null),
  ("initial",packetJson initial),("final",packetJson r.final),("elapsed",ratJson r.elapsed),
  ("work",countsJson r.counts r.charged),("pending",toJson r.pending.length),
  ("failure_index",if r.failure.isSome then toJson r.observations.length else Json.null),
  ("trace",toJson (traceJson r.observations 0 0)),
  ("searches",toJson (r.searches.map fun (i,as) => Json.mkObj [
    ("index",toJson i),("attempts",toJson (as.map attemptJson))]))]

def runRequest (r : Request) : Report := drive r.limits r.tolerance r.events initial r.work 0

theorem request_success (r : Request) (hs : (runRequest r).failure = none) :
    Approx (runRequest r).final (executeEvents r.events initialPose) ∧
    TraceSound initialPose (runRequest r).observations ∧
    (runRequest r).final.error ≤ r.tolerance :=
  success_sound r.limits r.tolerance r.events initial r.work 0 initial_approx hs

end Orbifold.DiskTransport.Numerical.Driver
