import Applications.FRP.DriverProtocol

/-! Sequential byte IO for the bounded lifecycle driver. Stream operations are
trusted runtime primitives; no publication is retried after an exception. -/
namespace FRPSpec.Frontier.Driver

def number (s : String) : Except DecodeError Nat := do
  if s.length > 5 then throw .limit
  let some n := s.toNat? | throw .malformed
  if toString n != s then throw .malformed
  if n > 65535 then throw .limit
  return n

def parse (line : String) : Except DecodeError Command := do
  let words := line.splitOn " "
  let tokens ← match words with
    | "begin"::xs => do pure (0 :: (← xs.mapM number))
    | "process"::xs => do pure (1 :: (← xs.mapM number))
    | "source"::"left"::xs => do pure (2 :: 0 :: (← xs.mapM number))
    | "source"::"right"::xs => do pure (2 :: 1 :: (← xs.mapM number))
    | ["idle"] => pure [3]
    | _ => throw .malformed
  decodeBounded tokens

def statusText : Lifecycle.BeginStatus → String
  | .accepted => "accepted"
  | .busy => "busy"
  | .stale => "stale"

def numbers (xs : List Nat) : String := String.intercalate " " (xs.map toString)

/-- Human-readable command rendering. Numeric token roundtrips are proved in
DriverProtocol; the decimal and text-framing wrappers are runtime-tested. -/
def formatCommand : Command → String
  | .begin id t => "begin " ++ numbers [id,t]
  | .process id => "process " ++ numbers [id]
  | .source r m => "source " ++ (match r with | .left => "left " | .right => "right ") ++
      numbers ([m.frontier,m.packet.length] ++ encodePacket m.packet)
  | .idle => "idle"

def render (o : Output) : String :=
  let p := match o.packet with | none => "-" | some true => "accepted" | some false => "rejected"
  let status := o.event.1.status.map statusText |>.getD "-"
  let response := match o.event.1.response with
    | none => "-"
    | some r => numbers (encodeResponse r)
  let aggregate := match o.event.2 with | none => "-" | some p => numbers (encodeAggregate p)
  s!"ok packet {p} status {status} response {response} aggregate {aggregate}"

/-- Errors consume a driver frame but leave the modeled lifecycle unchanged. -/
def decodedStep (s : State) (input : Except DecodeError Command) : State × String :=
  match input with
  | .error .malformed => (s,"error malformed")
  | .error .limit => (s,"error limit")
  | .ok c => let next := step s c; (next.1,render next.2)

theorem decoded_error_stutters (s : State) (e : DecodeError) :
    (decodedStep s (.error e)).1 = s := by cases e <;> rfl

theorem decoded_agrees (s : State) (c : Command) :
    decodedStep s (.ok c) = ((Lifecycle.Pipeline.step Consumer s c).1,render (step s c).2) := rfl

/-- Finite replay is a specification helper; the IO loop does not call it or
retain a transcript. Invalid positions remain in its output list. -/
def replay (s : State) : List (Except DecodeError Command) → State × List String
  | [] => (s,[])
  | x::xs => let next := decodedStep s x; let rest := replay next.1 xs
             (rest.1,next.2::rest.2)

def acceptedCommands (xs : List (Except DecodeError Command)) : List Command :=
  xs.filterMap (fun x => match x with | .ok c => some c | .error _ => none)

theorem replay_state (s : State) (xs : List (Except DecodeError Command)) :
    (replay s xs).1 = (Lifecycle.Pipeline.run Consumer s (acceptedCommands xs)).1 := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | error e => cases e <;> simpa [replay,decodedStep,acceptedCommands] using ih s
    | ok c =>
      simpa [replay,decodedStep,acceptedCommands,Lifecycle.Pipeline.run,step] using
        (ih (Lifecycle.Pipeline.step Consumer s c).1)

inductive Frame | eof | line (text : String) | error (reason : String)

/-- Reads at most 4097 individual bytes, including the terminating LF. The
extra byte distinguishes a full legal frame from an overlong prefix. -/
def readFrame (input : IO.FS.Stream) : Nat → ByteArray → IO Frame
  | 0, _ => pure (.error "frame-limit")
  | n+1, buf => do
    let b ← input.read 1
    if b.isEmpty then
      return if buf.isEmpty then .eof else .error "incomplete-frame"
    let c := b[0]!
    if c == 10 then return .line (String.fromUTF8! buf)
    if c < 32 || c > 126 then return .error "non-ascii"
    readFrame input n (buf.push c)

/-- A successful flush is local publication, not external acknowledgment.
An exception escapes; the caller terminates without another read or retry. -/
def publish (output : IO.FS.Stream) (line : String) : IO Unit := do
  output.write (line ++ "\n").toUTF8
  output.flush

/-- Finite fuel also counts malformed frames. It is not a retained transcript. -/
def drive (input output : IO.FS.Stream) : Nat → State → IO UInt32
  | 0, _ => do publish output "error frame-budget"; return 2
  | fuel+1, state => do
    match ← readFrame input 4097 ByteArray.empty with
    | .eof => return 0
    | .error reason => publish output s!"error {reason}"; return 2
    | .line line =>
      let next := decodedStep state (parse line)
      publish output next.2
      drive input output fuel next.1

def runDriver : IO UInt32 := do
  try
    drive (← IO.getStdin) (← IO.getStdout) 256 initial
  catch _ =>
    try
      let err ← IO.getStderr
      err.putStr "FRP driver: IO failure; publication may be partial; no retry\n"
      err.flush
    catch _ => pure ()
    return 3

end FRPSpec.Frontier.Driver
