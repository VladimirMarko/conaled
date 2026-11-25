import Applications.Rendering.PPM

/-- The OS and Lean runtime implement these external writes; no filesystem theorem is claimed. -/
def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: RenderOrthographic.lean OUTPUT_DIRECTORY")
  let output : System.FilePath := directory
  IO.FS.createDirAll output
  for k in List.finRange 3 do
    let name := s!"frame-00{k.val}.ppm"
    IO.FS.writeFile (output / name) (Applications.Rendering.PPM.frameText k)
    IO.println s!"wrote {output / name}"
