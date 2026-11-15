import Lake.Build.Trace

-- Executable tooling, not an audited library theorem. Read bytes through the
-- pinned Lake implementation; never consult the replaceable .hash sidecars.
def main (args : List String) : IO Unit := do
  let [manifest] := args | throw <| IO.userError "expected a JSON array of file paths"
  let json ← IO.ofExcept <| Lean.Json.parse (← IO.FS.readFile manifest)
  let paths ← IO.ofExcept <| Lean.fromJson? (α := Array String) json
  let hashes ← paths.mapM fun path => do
    return (← Lake.computeBinFileHash (System.FilePath.mk path)).hex
  IO.println (Lean.toJson hashes).compress
