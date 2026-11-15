import Examples.SchreierDiagramDriver

open Lean SchreierDiagrams SchreierDiagramDriver

def main : IO Unit := do
  let data := diagram "A < B & \"C\"" unitVertices permutations
    (fun _ => "line\n\"quoted\"\\tail<&>") permutationLabel
  (← IO.getStdout).putStrLn data.compress
