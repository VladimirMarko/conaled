import Applications.FRP.MigrationIO

def main (args : List String) : IO UInt32 := do
  let kind ← match args with
    | [] | ["delay"] => pure FRPSpec.Migration.Kind.delay
    | ["redundant"] => pure FRPSpec.Migration.Kind.redundant
    | _ =>
      (← IO.getStderr).putStrLn "usage: migration-service.lean [delay|redundant]"
      return 2
  FRPSpec.Migration.serve kind (← IO.getStdin) (← IO.getStdout)
  return 0
