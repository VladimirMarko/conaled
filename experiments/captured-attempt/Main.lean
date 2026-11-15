import Applications.Interaction.CapturedAttempt
import Lean

open Lean Interaction.Measurement Interaction.CapturedAttempt

private def statusText : Status → String
  | .confirmed => "confirmed" | .failed => "failed" | .unknown => "unknown"

private def completionText : Completion → String
  | .exited n => s!"exit:{n}" | .spawnFailed => "spawn-failed"
  | .timedOut => "timeout" | .unknown => "unknown"

private def bytesJson (b : ByteArray) : Json := toJson (b.data.map UInt8.toNat)

private structure Report where
  observer : Observer := {}
  captureState : CaptureState ByteArray ByteArray := .empty
  events : Array Json := #[]
  capturedA : Option ByteArray := none
  capturedB : Option ByteArray := none
  stdout : ByteArray := ByteArray.empty
  stderr : ByteArray := ByteArray.empty
  consumed : Json := .null
  stdoutStatus : String := "unobserved"
  stderrStatus : String := "unobserved"
  protocolStatus : String := "unobserved"
  raw : Option Nat := none
  stage : String := "preflight"
  error : Option String := none
  failureStage : Option String := none
  injectionApplied : Bool := false
  command : Array String := #[]

private def event (r : IO.Ref Report) (name : String) (fields : List (String × Json) := []) : IO Unit :=
  r.modify fun s => {s with events := s.events.push (Json.mkObj
    (("seq", toJson s.events.size) :: ("event", toJson name) :: fields))}

private def injected (r : IO.Ref Report) (fault : String) : IO Unit := do
  r.modify fun s => {s with injectionApplied := true}
  event r "injected_fault" [("fault", toJson fault), ("origin", toJson "injected")]

private def probe (r : IO.Ref Report) (p : Probe) : IO Unit := do
  let s ← r.get
  let some next := advance s.observer (.response p)
    | throw (IO.userError "inadmissible response before authorization")
  r.set {s with observer := next}

private def boundedRead (path : System.FilePath) (cap : Nat)
    (retain : ByteArray → IO Unit := fun _ => pure ()) : IO ByteArray :=
  IO.FS.withFile path .read fun handle => do
    let mut result := ByteArray.empty
    for _ in [:cap + 1] do
      let next ← handle.read ((cap + 1 - result.size).toUSize)
      if next.isEmpty then break
      result := result ++ next
      retain result
      if result.size > cap then break
    return result

private def captureEvent (r : IO.Ref Report) (e : CaptureEvent ByteArray ByteArray) : IO Unit := do
  let s ← r.get
  let some next := captureAdvance s.captureState e
    | throw (IO.userError "inadmissible capture event")
  r.set {s with captureState := next}

private def waitBarrier (r : IO.Ref Report) (path : System.FilePath) : IO Unit := do
  for _ in [:500] do
    if ← path.pathExists then
      event r "barrier_observed" [("path", toJson path.toString)]
      return
    IO.sleep 10
  throw (IO.userError "barrier observation budget exhausted")

private def capture (r : IO.Ref Report) (work : System.FilePath) (slot fault : String) : IO ByteArray := do
  r.modify fun s => {s with stage := "read-" ++ slot}
  let retain := fun bytes => r.modify fun s =>
    if slot == "A" then {s with capturedA := some bytes} else {s with capturedB := some bytes}
  if fault == "read-a-denied" && slot == "A" then
    injected r fault
    throw (IO.userError "injected read permission denial")
  if fault == "read-b-error-after-prefix" && slot == "B" then
    let chunk ← IO.FS.withFile (work / "live" / slot) .read fun h => h.read 1
    retain chunk
    injected r fault
    throw (IO.userError "injected read failure after prefix")
  let bytes ← boundedRead (work / "live" / slot) 4096 retain
  if slot == "A" then r.modify fun s => {s with capturedA := some bytes}
  else r.modify fun s => {s with capturedB := some bytes}
  event r "read_return" [("slot", toJson slot), ("bytes", bytesJson bytes), ("eof", toJson (decide (bytes.size ≤ 4096)))]
  if bytes.size > 4096 then throw (IO.userError "input cap exceeded")
  captureEvent r (if slot == "A" then .readA bytes else .readB bytes)
  r.modify fun s => {s with stage := "seal-" ++ slot}
  if fault == "seal-b-error-after-prefix" && slot == "B" then
    IO.FS.writeBinFile (work / "sealed" / slot) (bytes.extract 0 1)
    injected r fault
    throw (IO.userError "injected seal failure after prefix")
  IO.FS.writeBinFile (work / "sealed" / slot) bytes
  captureEvent r (if slot == "A" then .sealA else .sealB)
  event r "seal_return" [("slot", toJson slot), ("bytes", bytesJson bytes)]
  return bytes

private def poll {cfg : IO.Process.StdioConfig} (r : IO.Ref Report)
    (child : IO.Process.Child cfg) : Nat → IO (Option UInt32)
  | 0 => pure none
  | n + 1 => do
    match ← child.tryWait with
    | some code =>
      event r "poll_return" [("raw", toJson code.toNat)]
      return some code
    | none =>
      event r "poll_pending"
      IO.sleep 10
      poll r child n

private def validOutput (a b out err : ByteArray) : Option Json := do
  let text ← String.fromUTF8? out
  let j ← (Json.parse text).toOption
  let ja ← (j.getObjValAs? (Array Nat) "a").toOption
  let jb ← (j.getObjValAs? (Array Nat) "b").toOption
  let total ← (j.getObjValAs? Nat "sum").toOption
  if ja != a.data.map UInt8.toNat || jb != b.data.map UInt8.toNat then none
  else if total != (ja.toList ++ jb.toList).foldl (· + ·) 0 then none
  else if err != "fixture-complete\n".toUTF8 then none
  else some j

private def payload (r : Report) (work : System.FilePath) (mode fault : String) : Json :=
  Json.mkObj [
    ("protocol", toJson "captured-attempt-v1"), ("case", toJson mode),
    ("injected_fault", toJson fault), ("injection_applied", toJson r.injectionApplied), ("events", toJson r.events),
    ("declared_inputs", toJson #[(work / "live/A").toString, (work / "live/B").toString]),
    ("captured_a", (r.capturedA.map bytesJson).getD .null),
    ("captured_b", (r.capturedB.map bytesJson).getD .null),
    ("stdout_bytes", bytesJson r.stdout), ("stderr_bytes", bytesJson r.stderr),
    ("consumed", r.consumed), ("stdout_status", toJson r.stdoutStatus),
    ("stderr_status", toJson r.stderrStatus), ("protocol_status", toJson r.protocolStatus),
    ("raw_termination", toJson r.raw),
    ("completion", toJson (completionText r.observer.observed.completion)),
    ("output_complete", toJson r.observer.observed.outputComplete),
    ("cleanup", toJson (statusText r.observer.observed.cleanup)),
    ("publication", toJson (statusText r.observer.observed.publication)),
    ("success", toJson (successful r.observer.controller)),
    ("retry_refused", toJson (advance r.observer .authorize).isNone),
    ("stage", toJson r.stage), ("failure_stage", toJson r.failureStage), ("error", toJson r.error), ("command", toJson r.command)]

private def attempt (work : System.FilePath) (mode fault fixture : String) : IO UInt32 := do
  let r ← IO.mkRef ({} : Report)
  try
    let a ← capture r work "A" fault
    if mode == "mixed" || mode == "live-input-bug" then
      IO.FS.writeFile (work / "barrier/a-read") "read\n"
      event r "barrier_release" [("path", toJson (work / "barrier/a-read").toString)]
      waitBarrier r (work / "barrier/writer-done")
    let b ← capture r work "B" fault
    let s ← r.get
    let some issued := authorizeCaptured s.captureState s.observer | throw (IO.userError "authorization refused")
    r.set {s with observer := issued, stage := "spawn"}
    event r "authorize"
    let inputs := if mode == "live-input-bug" then "live" else "sealed"
    let command := #["python3", fixture, "child", work.toString, mode,
      (work / inputs / "A").toString, (work / inputs / "B").toString]
    r.modify fun s => {s with command := command}
    if fault == "spawn-before-call" then
      injected r fault
      probe r .spawnFailed
      probe r (.cleanup .confirmed)
      event r "spawn_error" [("origin", toJson "injected"), ("before_call", toJson true)]
      throw (IO.userError "injected failure before spawn call")
    let child ← IO.Process.spawn {
      cmd := "python3"
      args := command.extract 1 command.size
      stdin := .null
      stdout := .null
      stderr := .null }
    event r "spawn_return"
    r.modify fun s => {s with stage := "observe"}
    let result? ← try
      if fault == "poll-error" then
        injected r fault
        throw (IO.userError "injected polling exception")
      pure (some (← poll r child 100))
      catch e =>
        event r "poll_error" [("diagnostic", toJson e.toString)]
        pure none
    match result? with
    | some (some raw) =>
      r.modify fun s => {s with raw := some raw.toNat}
      probe r (.raw raw.toNat)
      probe r (.cleanup .confirmed)
      event r "cleanup_observed"
    | _ =>
      probe r (if result?.isSome then .timeout else .unknownCompletion)
      event r "cleanup_request"
      let killed ← try
        child.kill
        pure true
        catch e =>
          event r "cleanup_error" [("diagnostic", toJson e.toString)]
          pure false
      let reaped ← try poll r child 100 catch e =>
        event r "cleanup_error" [("diagnostic", toJson e.toString)]
        pure none
      let cleanup := if reaped.isSome then Status.confirmed else if killed then .unknown else .failed
      probe r (.cleanup cleanup)
      if reaped.isSome then event r "cleanup_observed"
    if fault == "completion-unknown" then
      injected r fault
      probe r .unknownCompletion
    if fault == "cleanup-unknown" || fault == "cleanup-failed" then
      injected r fault
      probe r (.cleanup (if fault == "cleanup-unknown" then .unknown else .failed))
    r.modify fun s => {s with stage := "channels"}
    let stdout? ← try
      let bytes ← boundedRead (work / "stdout.bin") 65536 (fun b => r.modify fun s => {s with stdout := b})
      let status := if bytes.size > 65536 then "overflow" else if (String.fromUTF8? bytes).isNone then "invalid-utf8" else "read-complete"
      r.modify fun s => {s with stdout := bytes, stdoutStatus := status}
      event r "channel_return" [("name", toJson "stdout"), ("prefix", bytesJson bytes), ("eof", toJson (decide (bytes.size ≤ 65536)))]
      pure (some bytes)
      catch e =>
        r.modify fun s => {s with stdoutStatus := "read-error"}
        event r "channel_error" [("name", toJson "stdout"), ("diagnostic", toJson e.toString)]
        pure none
    let stderr? ← try
      let bytes ← boundedRead (work / "stderr.bin") 65536 (fun b => r.modify fun s => {s with stderr := b})
      let status := if bytes.size > 65536 then "overflow" else if (String.fromUTF8? bytes).isNone then "invalid-utf8" else "read-complete"
      r.modify fun s => {s with stderr := bytes, stderrStatus := status}
      event r "channel_return" [("name", toJson "stderr"), ("prefix", bytesJson bytes), ("eof", toJson (decide (bytes.size ≤ 65536)))]
      pure (some bytes)
      catch e =>
        r.modify fun s => {s with stderrStatus := "read-error"}
        event r "channel_error" [("name", toJson "stderr"), ("diagnostic", toJson e.toString)]
        pure none
    let stdout := stdout?.getD ByteArray.empty
    let stderr := stderr?.getD ByteArray.empty
    let consumed := validOutput a b stdout stderr
    r.modify fun s => {s with
      consumed := consumed.getD .null
      protocolStatus := if consumed.isSome then "valid" else "invalid-or-incomplete"}
    let normal := (← r.get).observer.observed.completion == .exited 0
    probe r (.channels (normal && stdout?.isSome && stderr?.isSome && consumed.isSome && stdout.size ≤ 65536 && stderr.size ≤ 65536))
  catch e =>
    r.modify fun s => {s with error := some e.toString, failureStage := some s.stage}
    let s ← r.get
    let name := if s.stage.startsWith "read-" then "read_error"
      else if s.stage.startsWith "seal-" then "seal_error" else "operation_error"
    event r name [("diagnostic", toJson e.toString), ("stage", toJson s.stage),
      ("origin", toJson (if s.injectionApplied then "injected" else "runtime")),
      ("captured_a", (s.capturedA.map bytesJson).getD .null),
      ("captured_b", (s.capturedB.map bytesJson).getD .null)]
  r.modify fun s => {s with stage := "publication"}
  event r "publication_request"
  let provisional := payload (← r.get) work mode fault
  let written ← try
    if fault == "publication-before-write" then
      injected r fault
      throw (IO.userError "injected failure before publication write")
    IO.FS.writeFile (work / "evidence.json") (provisional.compress ++ "\n")
    pure true
    catch e =>
      if (← r.get).observer.controller.started then probe r (.publication .failed)
      event r "publication_error" [("diagnostic", toJson e.toString)]
      pure false
  if written then
    try
      if fault == "publication-after-write" then
        injected r fault
        throw (IO.userError "injected acknowledgment loss after write/close")
      if (← r.get).observer.controller.started then probe r (.publication .confirmed)
      event r "publication_ack"
    catch e =>
      if (← r.get).observer.controller.started then probe r (.publication .unknown)
      event r "publication_ack_lost" [("origin", toJson "injected"), ("diagnostic", toJson e.toString)]
  event r "select"
  if (advance (← r.get).observer .authorize).isNone then event r "retry_refused"
  if fault == "receipt-truncated" then injected r fault
  let final ← r.get
  let receipt := (payload final work mode fault).compress
  if fault == "receipt-truncated" then
    IO.print (String.ofList (receipt.toList.take 64))
  else IO.println receipt
  return if successful final.observer.controller then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [work, mode, fault, fixture] =>
    if !["success", "mixed", "nonzero", "signal", "missing-output", "stdout-overflow", "stderr-overflow", "invalid-output", "timeout", "boundary", "live-input-bug"].contains mode || !["none", "publication-after-write", "read-a-denied", "read-b-error-after-prefix", "seal-b-error-after-prefix", "poll-error", "completion-unknown", "cleanup-unknown", "cleanup-failed", "spawn-before-call", "publication-before-write", "receipt-truncated"].contains fault then
      IO.eprintln "unsupported fixture case/fault"
      return 2
    for name in ["sealed/A", "sealed/B", "stdout.bin", "stderr.bin", "attempt.marker", "evidence.json"] do
      if ← (System.FilePath.mk work / name).pathExists then
        IO.eprintln s!"requires unused resource: {name}"
        return 2
    attempt work mode fault fixture
  | _ => IO.eprintln "usage: Main WORK CASE FAULT FIXTURE"; pure 2
