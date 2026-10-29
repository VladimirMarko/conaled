import Applications.FRP.IndefiniteIO

/-- Run with no arguments for one tick of delay, or `twice` for two ticks. -/
def main (args : List String) : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  match args with
  | [] => FRPSpec.Indefinite.serve FRPSpec.Indefinite.delay input output
  | ["twice"] => FRPSpec.Indefinite.serve FRPSpec.Indefinite.twice input output
  | _ =>
    (← IO.getStderr).putStrLn "usage: reactive-service.lean [twice]"
    return 2
  return 0
