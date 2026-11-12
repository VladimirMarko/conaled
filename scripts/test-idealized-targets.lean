import Examples.IdealizedTargets

open OracleComputation IntervalAnalysis Examples.IdealizedTargets

/-- Runtime checks exercise the executable observations, not the noncomputable ideal oracle. -/
def main : IO Unit := do
  unless observe 0 .zero 0 == none do
    throw (IO.userError "bound zero must be unknown")
  unless observe 1 effectiveProgram 0 == none do
    throw (IO.userError "insufficient bound must be unknown")
  unless observe 2 effectiveProgram 0 == some 2 do
    throw (IO.userError "sufficient bound must return two")
  unless observeZero (singleton 0) == some true do
    throw (IO.userError "singleton zero must be recognized")
  unless observeZero compiledBox == some false do
    throw (IO.userError "compiled singleton five must be nonzero")
  unless observeZero unitBox == none do
    throw (IO.userError "ambiguous interval must remain unknown")
  unless observeZero (add unitBox (neg unitBox)) == none do
    throw (IO.userError "dependency loss must not become an exact decision")
  IO.println "idealized-target executable observations: PASS"
