import Applications.FRP.PendingMigrationIO

def main (args : List String) : IO UInt32 := do
  let kind ← match args with
    | [] | ["delay"] => pure FRPSpec.Migration.Kind.delay
    | ["redundant"] => pure FRPSpec.Migration.Kind.redundant
    | _ => return 2
  FRPSpec.PendingMigration.serve kind (← IO.getStdin) (← IO.getStdout)
  return 0
