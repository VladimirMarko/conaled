import Applications.FRP.RegionalMigrationIO

def main : IO Unit := do
  FRPSpec.Regional.Reconfiguration.serve (← IO.getStdin) (← IO.getStdout)
