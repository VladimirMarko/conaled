import Applications.Orbifold.Driver.Protocol

open Lean Orbifold.DiskTransport.Numerical.Driver

/-- Read a finite frame; IO/resource exceptions are outside the analytic theorem. -/
def readBounded (h : IO.FS.Handle) : Nat → ByteArray → IO (Except String String)
  | 0, _ => pure (.error "request exceeds 65536-byte input limit")
  | n+1, buf => do
    let b ← h.read 1
    if b.isEmpty then
      match String.fromUTF8? buf with
      | some s => return .ok s
      | none => return .error "invalid UTF-8"
    readBounded h n (buf ++ b)

def errorJson (reason : String) : Json :=
  Json.mkObj [("status",toJson "input_error"),("reason",toJson reason)]

def main (args : List String) : IO UInt32 := do
  try
    let [path] := args | do
      IO.println (errorJson "usage: disk-driver.lean request.json").compress
      return 2
    let text ← IO.FS.withFile path .read fun h => readBounded h 65537 ByteArray.empty
    match text.bind (fun s => (Json.parse s).bind parseRequest) with
    | .error why =>
      IO.println (errorJson why).compress
      return 2
    | .ok request =>
      IO.println (reportJson (runRequest request)).compress
      return 0
  catch e =>
    IO.println (Json.mkObj [("status",toJson "process_error"),("reason",toJson e.toString)]).compress
    return 3
