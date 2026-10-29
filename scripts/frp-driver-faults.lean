import Applications.FRP.DriverIO

/-! Inject failures through the same public streams used by the real driver.
These are executable fixtures, not claims about every OS failure history. -/
open FRPSpec.Frontier.Driver

def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def publicationFailure (atFlush : Bool) : IO Unit := do
  let consumed := "source left 1 0\nsource right 1 0\nbegin 0 0\nprocess 0\n"
  let source ← IO.mkRef ({data := (consumed ++ "idle\n").toUTF8} : IO.FS.Stream.Buffer)
  let sink ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let writes ← IO.mkRef (0 : Nat)
  let flushes ← IO.mkRef (0 : Nat)
  let base := IO.FS.Stream.ofBuffer sink
  let output : IO.FS.Stream := {base with
    write := fun bytes => do
      writes.modify (·+1)
      if (← writes.get) < 4 || atFlush then base.write bytes
      else
        base.write (bytes.extract 0 7)
        throw (IO.userError "injected after partial write")
    flush := do
      flushes.modify (·+1)
      if (← writes.get) == 4 then throw (IO.userError "injected flush failure")}
  -- Also fail the diagnostic sink: reporting failure must not cause a retry.
  let errors : IO.FS.Stream := {base with
    putStr := fun _ => throw (IO.userError "injected diagnostic failure")}
  let exit ← IO.withStdin (IO.FS.Stream.ofBuffer source) <|
    IO.withStdout output <| IO.withStderr errors runDriver
  ensure (exit == 3) "failure exit code"
  ensure ((← source.get).pos == consumed.toUTF8.size) "read a second command after publication failure"
  ensure ((← writes.get) == 4) "publication was retried"
  ensure ((← flushes.get) == (if atFlush then 4 else 3)) "unexpected flush count"
  let bytes := (← sink.get).data
  let prefix := "ok packet accepted status - response - aggregate -\n" ++
    "ok packet accepted status - response - aggregate -\n" ++
    "ok packet - status accepted response - aggregate -\n"
  let response := if atFlush then "ok packet - status - response 0 0 0 aggregate 1 0\n" else "ok pack"
  ensure (String.fromUTF8! bytes == prefix ++ response)
    "fixture did not retain the ambiguous response publication"

def readFailure : IO Unit := do
  let sink ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let base := IO.FS.Stream.ofBuffer sink
  let input : IO.FS.Stream := {base with read := fun _ => throw (IO.userError "read failure")}
  let errors ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let exit ← IO.withStdin input <| IO.withStdout base <|
    IO.withStderr (IO.FS.Stream.ofBuffer errors) runDriver
  ensure (exit == 3) "read failure exit code"
  ensure ((← sink.get).data.isEmpty) "read failure published a lifecycle result"

def main : IO Unit := do
  publicationFailure false
  publicationFailure true
  readFailure
  IO.println "failure fixtures passed"
