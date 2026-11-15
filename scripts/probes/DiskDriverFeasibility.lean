import Applications.Orbifold.MeasuredNumericalExecution
import Applications.Orbifold.NumericalSymmetry

open Orbifold.DiskTransport.Numerical

def initial : Packet := ⟨⟨(-1/4096,0),((1-(1/4096)^2)/2,0)⟩,0⟩
def origin : Packet := ⟨⟨(0,0),(1/2,0)⟩,0⟩
def tick (c : Input) (num den n : Nat) : Tick :=
  ⟨c,(num:ℚ)/(den:ℚ)/(n:ℚ),by positivity⟩
def qs (q : Packet) : List ℚ :=
  [q.state.position.1,q.state.position.2,q.state.frame.1,q.state.frame.2,q.error]
def bits (n : Nat) : Nat := if n == 0 then 0 else n.log2 + 1
def sizes (q : Packet) : Nat × Nat :=
  ((qs q).foldl (fun a v => max a (bits v.num.natAbs)) 0,
   (qs q).foldl (fun a v => max a (bits v.den)) 0)

def main (args : List String) : IO UInt32 := do
  let kind := args[0]?.getD "move"
  let n := (args[1]?.getD "1").toNat!.toUInt64.toNat
  let num := (args[2]?.getD "1").toNat!
  let den := (args[3]?.getD "1024").toNat!
  let tolerance : ℚ := 1 / ((args[4]?.getD "32768").toNat! : ℚ)
  let limit := (args[5]?.getD "16384").toNat!
  let mode := args[6]?.getD "steps"
  if n == 0 || n > 256 || den == 0 then
    IO.println "invalid probe parameters"
    return 2
  let move := tick (.move (1,0)) num den n
  let turn := tick (.turn 1) num den n
  let ticks := if kind == "word" then List.replicate n move ++ List.replicate n turn ++ List.replicate n move
    else if kind == "turn" then List.replicate n turn
    else if kind == "hold" then List.replicate n (tick .hold num den n)
    else List.replicate n move
  let q0 := if kind == "origin" then origin else initial
  let out ← IO.getStdout
  let started ← IO.monoNanosNow
  if mode == "whole" then
    let r := Measured.run ticks q0
    let ended ← IO.monoNanosNow
    let peak := match r.1 with
      | none => sizes q0
      | some s => (s.samples ++ [q0]).foldl (fun a q => let b := sizes q; (max a.1 b.1,max a.2 b.2)) (0,0)
    let error := match r.1 with | none => "null" | some s => s!"\"{s.final.error}\""
    let meets := match r.1 with | none => false | some s => decide (s.final.error ≤ tolerance)
    out.putStrLn s!"event=whole success={r.1.isSome} attempts={r.2.1} accepted={r.2.2.1} rejected={r.2.2.2} num_bits={peak.1} den_bits={peak.2} error={error} meets_tolerance={meets} elapsed_ns={ended-started}"
    out.flush
    return 0
  let mut q := q0
  let mut accepted := 0
  let mut elapsed : ℚ := 0
  for c in ticks do
    let sb := sizes q
    if max sb.1 sb.2 > limit then
      out.putStrLn s!"event=bit_cutoff accepted={accepted} num_bits={sb.1} den_bits={sb.2}"
      out.flush
      return 3
    let before ← IO.monoNanosNow
    let result := Measured.run [c] q
    let after ← IO.monoNanosNow
    match result.1 with
    | none =>
      out.putStrLn s!"event=rejected index={accepted} attempts={result.2.1} rejected={result.2.2.2} step_ns={after-before}"
      out.flush
      return 0
    | some r =>
      q := r.final
      accepted := accepted+1
      elapsed := elapsed+c.duration
      let sz := sizes q
      out.putStrLn s!"event=step index={accepted} num_bits={sz.1} den_bits={sz.2} error={q.error} clock={elapsed} step_ns={after-before}"
      out.flush
  let ended ← IO.monoNanosNow
  out.putStrLn s!"event=complete accepted={accepted} error={q.error} clock={elapsed} meets_tolerance={decide (q.error ≤ tolerance)} elapsed_ns={ended-started}"
  out.flush
  return 0
