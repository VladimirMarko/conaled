import Applications.FRP.RegionalPendingIO

def main : IO Unit := do
  FRPSpec.Regional.Pending.serve (← IO.getStdin) (← IO.getStdout)
