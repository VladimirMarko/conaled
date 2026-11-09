import Applications.Orbifold.Driver.Interval
import Examples.NumericalMotion

open Orbifold.DiskTransport.Numerical

def main : IO Unit := do
  let result := Driver.searchInterval ⟨4,16384⟩ (1/32768) 128
    Examples.NumericalMotion.moveTick Examples.NumericalMotion.initial
  match result.accepted with
  | none => throw (IO.userError "bounded search must find the two-step fixed-duration refinement")
  | some selected =>
    unless selected.subdivisions == 2 && selected.execution.elapsed == (1/1024 : ℚ) &&
        selected.execution.final.error == (160251/8589934592 : ℚ) && result.counts.1 == 3 do
      throw (IO.userError "refinement must retain retry work without advancing committed time")
