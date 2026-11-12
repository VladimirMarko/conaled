import Applications.Resources.DelayedInsertion

open Resources.DelayedInsertion

private def check [BEq α] [Repr α] (name : String) (actual expected : α) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"{name}: expected {repr expected}, got {repr actual}")

/-- The first public seam: building recipes and counting their outer spine. -/
def main : IO Unit := do
  let built := ordinary (1 : Nat) [2, 3]
  check "ordinary outer cells" (outerCells built.2) 6
  let counted := countOuter built
  check "outer count" counted.1 3
  check "count preserves builder events" counted.2 (built.2 ++ [.outerObserve 4])
  check "build and count do not force callbacks" (callbackBills counted.2) []
  IO.println "delayed insertion: first construction/count slice passed"
