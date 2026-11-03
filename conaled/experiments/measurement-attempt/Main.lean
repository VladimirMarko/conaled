import Applications.Interaction.Measurement
import Lean

open Interaction.Measurement Lean

private def completionText : Completion → String
  | .exited code => s!"exit:{code}"
  | .spawnFailed => "spawn-failed"
  | .timedOut => "timeout"
  | .unknown => "unknown"

private def statusText : Status → String
  | .confirmed => "confirmed"
  | .failed => "failed"
  | .unknown => "unknown"

private def evidence (o : Observation) (success : Bool) (output : String)
    (outputBytes captured : ByteArray) (command : Array String) (fault liveAfter declaredInput : String)
    (elapsedMs : Nat) : Lean.Json :=
  Lean.Json.mkObj [
    ("completion", toJson (completionText o.completion)),
    ("output_complete", toJson o.outputComplete),
    ("cleanup", toJson (statusText o.cleanup)),
    ("publication", toJson (statusText o.publication)),
    ("success", toJson success), ("output", toJson output),
    ("output_bytes", toJson (outputBytes.data.map UInt8.toNat)),
    ("captured_bytes", toJson (captured.data.map UInt8.toNat)),
    ("declared_input", toJson declaredInput),
    ("live_after_capture", toJson liveAfter),
    ("elapsed_ms", toJson elapsedMs),
    ("timing_scope", toJson "capture-through-observation-excludes-publication"),
    ("output_limit_bytes", toJson (4096 : Nat)),
    ("poll_limit", toJson (100 : Nat)), ("poll_sleep_ms", toJson (10 : Nat)),
    ("command", toJson command), ("injected_fault", toJson fault)]

/-- Finite polling; OS primitive calls and sleep are trusted, not time-bounded by Lean. -/
private def poll {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg) :
    Nat → IO (Option UInt32)
  | 0 => pure none
  | n + 1 => do
    match ← child.tryWait with
    | some code => pure (some code)
    | none => IO.sleep 10; poll child n

private def readUpTo (handle : IO.FS.Handle) : Nat → IO ByteArray
  | 0 => pure ByteArray.empty
  | n + 1 => do
    let bytes ← handle.read (n + 1).toUSize
    if bytes.isEmpty then return bytes
    -- One-byte reads give a simple structural bound without an OS short-read assumption.
    let mut result := bytes
    for _ in [:n + 1 - bytes.size] do
      let next ← handle.read 1
      if next.isEmpty then break
      result := result ++ next
    return result

private def boundedRead (path : System.FilePath) : IO ByteArray :=
  IO.FS.withFile path .read fun handle => readUpTo handle 4097

private def attempt (work live destination : System.FilePath)
    (mode fault fixture : String) : IO UInt32 := do
  unless ["success", "nonzero", "spawn-failure", "timeout", "boundary", "mutate",
      "overflow", "missing-output"].contains mode do
    throw (IO.userError "unsupported fixture mode")
  unless ["none", "spawn-error", "cleanup-failed", "cleanup-unknown",
      "completion-unknown"].contains fault do
    throw (IO.userError "unsupported injected fault")
  for name in ["captured", "output", "executions"] do
    if ← (work / name).pathExists then
      throw (IO.userError s!"attempt requires unused resource: {name}")
  let startedAt ← IO.monoMsNow
  let some controller := begin initial | throw (IO.userError "attempt already started")
  let captured ← boundedRead live
  if captured.size > 4096 then throw (IO.userError "input exceeds 4096 bytes")
  let sealed := work / "captured"
  IO.FS.writeBinFile sealed captured
  if mode == "mutate" then IO.FS.writeFile live "changed\n"
  let liveAfter ← IO.FS.readFile live
  let outputPath := work / "output"
  let executable := if mode == "spawn-failure" then (work / "absent-executable").toString else "python3"
  let command := #[executable, fixture, mode, sealed.toString,
    outputPath.toString, (work / "executions").toString]
  let child? ← try
    if fault == "spawn-error" then throw (IO.userError "injected spawn error")
    pure (some (← IO.Process.spawn {
      cmd := executable
      args := command.extract 1 command.size
      stdin := .null
      stdout := .null
      stderr := .null }))
    catch _ => pure none
  let (completion, cleanup) ← match child? with
    | none => pure (Completion.spawnFailed, Status.confirmed)
    | some child => do
      let observedExit ← try pure (some (← poll child 100)) catch _ => pure none
      match observedExit with
      | some (some code) => pure (.exited code.toNat, .confirmed)
      | _ =>
        let killed ← try child.kill; pure true catch _ => pure false
        let reaped ← try poll child 100 catch _ => pure none
        pure ((if observedExit.isSome then .timedOut else .unknown), if reaped.isSome then .confirmed else if killed then .unknown else .failed)
  let completion := if fault == "completion-unknown" then Completion.unknown else completion
  let bytes? ← try pure (some (← boundedRead outputPath)) catch _ => pure none
  let bytes := bytes?.getD ByteArray.empty
  let outputBytes := bytes.extract 0 4096
  let output := (String.fromUTF8? outputBytes).getD "[invalid UTF-8; see output_bytes]"
  let complete := bytes?.isSome && bytes.size ≤ 4096 &&
    (match completion with | .exited _ => true | _ => false)
  let cleanup := if fault == "cleanup-failed" then Status.failed
    else if fault == "cleanup-unknown" then .unknown else cleanup
  let observed : Observation := ⟨completion, complete, cleanup, .unknown⟩
  let elapsedMs := (← IO.monoMsNow) - startedAt
  let publication ← try
    IO.FS.writeFile destination ((evidence observed false output outputBytes captured command fault liveAfter live.toString elapsedMs).compress ++ "\n")
    pure Status.confirmed
    catch _ => pure Status.failed
  let final := {observed with publication := publication}
  let accepted := successful (record controller final)
  IO.println (evidence final accepted output outputBytes captured command fault liveAfter live.toString elapsedMs).compress
  return if accepted then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [work, live, destination, mode, fault, fixture] =>
    attempt work live destination mode fault fixture
  | _ => throw (IO.userError "usage: Main WORK LIVE EVIDENCE MODE FAULT CHILD")
